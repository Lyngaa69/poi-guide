/* access.js - shared by editor.html and people.html.
 *
 * Who may see which routes (invite-only routes), without a server:
 *  - an invite-only route has files with a secret part in the name:  <name>-<8 letters>.gpx  (and its audio files)
 *  - every invited person has a personal file  ture/u-<code>.json  that lists the routes they may open
 *  - the invitation link is  .../#u=<code>
 *  - the people, groups and which routes exist live in a PRIVATE repository (people.json), never in the public one
 *
 * This is "hidden", not "locked": the public repository can still be read by anyone who finds it.
 */
(function (global) {
  'use strict';
  var API = 'https://api.github.com';
  var ALPHA = 'abcdefghjkmnpqrstuvwxyz23456789';          // 31 letters and digits that are easy to read aloud
  var TOKEN_RE = /^(.*)-([a-z2-9]{8})$/;

  /* ---------- settings kept in this browser ---------- */
  function ls(k) { try { return localStorage.getItem('studio:' + k); } catch (e) { return null; } }
  function lsSet(k, v) { try { localStorage.setItem('studio:' + k, v); } catch (e) { } }
  function detectRepo() {
    var h = location.hostname, p = location.pathname.split('/').filter(Boolean);
    if (/\.github\.io$/i.test(h) && p.length && !/\.html?$/i.test(p[0])) return h.split('.')[0] + '/' + p[0];
    return '';
  }
  var cfg = {
    repo: function () { return ls('ghRepo') || detectRepo(); },
    token: function () { return ls('ghToken') || ''; },
    adminRepo: function () { return ls('adminRepo') || ''; },
    setAdminRepo: function (v) { lsSet('adminRepo', v); },
    ready: function () { return !!(cfg.repo() && cfg.token()); },
    adminReady: function () { return !!(cfg.repo() && cfg.token() && cfg.adminRepo()); }
  };

  /* ---------- random codes ---------- */
  function random(n) {
    var out = '';
    while (out.length < n) {
      var b = new Uint8Array(n * 2);
      (global.crypto || global.msCrypto).getRandomValues(b);
      for (var i = 0; i < b.length && out.length < n; i++) {
        var v = b[i] & 31;
        if (v < ALPHA.length) out += ALPHA.charAt(v);
      }
    }
    return out;
  }
  function newCode() { return random(10); }
  function prettyCode(c) { return c.slice(0, 5) + '-' + c.slice(5); }
  function normCode(s) { return String(s || '').toLowerCase().replace(/[^a-z0-9]/g, ''); }
  function splitBase(base) { var m = TOKEN_RE.exec(base); return m ? { slug: m[1], token: m[2] } : { slug: base, token: null }; }
  function baseOf(fil) { return String(fil).replace(/\.[^.]+$/, ''); }

  /* ---------- GitHub ---------- */
  function toB64(text) {
    var bytes = new TextEncoder().encode(text), bin = '';
    for (var i = 0; i < bytes.length; i += 0x8000) bin += String.fromCharCode.apply(null, bytes.subarray(i, i + 0x8000));
    return btoa(bin);
  }
  function fromB64(b64) {
    var bin = atob(String(b64).replace(/\s/g, '')), bytes = new Uint8Array(bin.length);
    for (var i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
    return new TextDecoder().decode(bytes);
  }
  function encPath(p) { return String(p).split('/').map(encodeURIComponent).join('/'); }
  function err(code, msg, status) { var e = new Error(msg); e.code = code; if (status) e.status = status; return e; }
  function fail(r) {
    return r.json().catch(function () { return {}; }).then(function (j) {
      var m = (j && j.message) || '', msg;
      if (r.status === 401) msg = 'GitHub rejected the token. It may be wrong or expired.';
      else if (r.status === 403) msg = 'The token is not allowed to do this. It needs "Contents: Read and write" on the repository. ' + m;
      else if (r.status === 404) msg = 'The repository or file was not found, or the token does not have access to it.';
      else if (r.status === 409 || (r.status === 422 && /fast forward|sha|does not match|is at/i.test(m))) msg = 'Something else was saved to GitHub at the same moment (often the automatic audio job). Nothing was lost. Wait a moment and press the button again.';
      else msg = 'GitHub error ' + r.status + (m ? ': ' + m : '');
      throw err('HTTP', msg, r.status);
    });
  }
  function call(repo, method, path, body) {
    var opts = { method: method, headers: { 'Accept': 'application/vnd.github+json', 'Authorization': 'Bearer ' + cfg.token() } };
    if (body !== undefined) { opts.headers['Content-Type'] = 'application/json'; opts.body = JSON.stringify(body); }
    return fetch(API + '/repos/' + repo + path, opts);
  }
  function req(repo, method, path, body) { return call(repo, method, path, body).then(function (r) { if (!r.ok) return fail(r); return r.json(); }); }
  function reqOrNull(repo, path) {
    return call(repo, 'GET', path).then(function (r) { if (r.status === 404) return null; if (!r.ok) return fail(r); return r.json(); });
  }
  function getText(repo, path) {
    return reqOrNull(repo, '/contents/' + encPath(path)).then(function (f) { return f && !Array.isArray(f) ? { text: fromB64(f.content), sha: f.sha } : null; });
  }
  function putText(repo, path, text, message, sha) {
    var body = { message: message, content: toB64(text) };
    if (sha) body.sha = sha;
    return req(repo, 'PUT', '/contents/' + encPath(path), body);
  }
  function listDir(repo, dir) { return reqOrNull(repo, '/contents/' + encPath(dir)).then(function (a) { return Array.isArray(a) ? a : []; }); }
  /* Another save can land on GitHub in the middle of ours (most often the audio job saving new audio, or the publish of the route before this one).
     GitHub then says "409" or "422 Update is not a fast forward". Nothing is wrong: start again from the newest version, a few times, with a short wait. */
  function transient(e) {
    var s = e && e.status;
    return s === 409 || s === 422 || s === 502 || s === 503 || s === 504 || (!s && !!e && /Failed to fetch|NetworkError|Load failed/i.test(e.message || ''));
  }
  function retry(fn, delays, onRetry) {              // delays: the waits between the tries (default: a few seconds in all); onRetry(k, total) is called before each new try
    var n = 0;
    function go() {
      return fn().catch(function (e) {
        var waits = delays || (global.Access && global.Access.retryDelays) || [];
        if (!transient(e) || n >= waits.length) throw e;
        var d = waits[n++];
        if (onRetry) { try { onRetry(n, waits.length); } catch (x) { } }
        return new Promise(function (res) { setTimeout(res, d); }).then(go);
      });
    }
    return go();
  }

  /* One commit: write files, delete files, rename files (keeping their content, so audio is not uploaded again).
     A file can be text (a string) or binary ({ base64: '...' }, for example an audio recording). Everything in one commit means one push, so the audio job
     starts once and sees all the files. Two commits one after the other can overtake each other, and the run for the first does not see the second. */
  function commitTree(repo, o) {
    var files = o.files || {}, deletes = o.deletes || [], renames = o.renames || [];
    var branch, head, baseTree;
    return req(repo, 'GET', '')
      .then(function (r) { branch = r.default_branch; return req(repo, 'GET', '/git/ref/heads/' + encodeURIComponent(branch)); })
      .then(function (ref) { head = ref.object.sha; return req(repo, 'GET', '/git/commits/' + head); })
      .then(function (c) {
        baseTree = c.tree.sha;
        var dirs = {};
        renames.forEach(function (rn) { dirs[rn.from.replace(/\/[^/]*$/, '')] = 1; });
        return Promise.all(Object.keys(dirs).map(function (d) { return listDir(repo, d).then(function (list) { return [d, list]; }); }));
      })
      .then(function (lists) {
        var bins = Object.keys(files).filter(function (p) { return files[p] && typeof files[p] === 'object' && files[p].base64; }), blobSha = {};
        return Promise.all(bins.map(function (p) {
          return req(repo, 'POST', '/git/blobs', { content: files[p].base64, encoding: 'base64' }).then(function (b) { blobSha[p] = b.sha; });
        })).then(function () { return [lists, blobSha]; });
      })
      .then(function (pair) {
        var lists = pair[0], blobSha = pair[1];
        var shaOf = {}, tree = [];
        lists.forEach(function (pair) { pair[1].forEach(function (f) { shaOf[pair[0] + '/' + f.name] = f.sha; }); });
        renames.forEach(function (rn) {
          if (!shaOf[rn.from]) throw err('MISSING', 'A file that should be renamed was not found: ' + rn.from);
          tree.push({ path: rn.to, mode: '100644', type: 'blob', sha: shaOf[rn.from] });
          tree.push({ path: rn.from, mode: '100644', type: 'blob', sha: null });
        });
        deletes.forEach(function (p) { tree.push({ path: p, mode: '100644', type: 'blob', sha: null }); });
        Object.keys(files).forEach(function (p) {
          if (blobSha[p]) tree.push({ path: p, mode: '100644', type: 'blob', sha: blobSha[p] });
          else tree.push({ path: p, mode: '100644', type: 'blob', content: files[p] });
        });
        if (!tree.length) return { noop: true };
        return req(repo, 'POST', '/git/trees', { base_tree: baseTree, tree: tree }).then(function (t) {
          if (t.sha === baseTree) return { noop: true };           // nothing changed: no empty commit
          return req(repo, 'POST', '/git/commits', { message: o.message, tree: t.sha, parents: [head] })
            .then(function (c) { return req(repo, 'PATCH', '/git/refs/heads/' + encodeURIComponent(branch), { sha: c.sha }); })
            .then(function () { return { noop: false }; });
        });
      });
  }

  /* ---------- the admin list (private repository) ---------- */
  function emptyModel() { return { v: 1, routes: [], groups: [], people: [] }; }
  function normalise(m) {
    m = m && typeof m === 'object' ? m : {};
    ['routes', 'groups', 'people'].forEach(function (k) { if (!Array.isArray(m[k])) m[k] = []; });
    m.v = 1;
    m.people.forEach(function (p) { if (!Array.isArray(p.groups)) p.groups = []; if (!Array.isArray(p.routes)) p.routes = []; });
    m.groups.forEach(function (g) { if (!Array.isArray(g.routes)) g.routes = []; });
    return m;
  }
  function loadAdmin() {
    var repo = cfg.adminRepo();
    if (!repo) return Promise.reject(err('NOADMIN', 'The invitation list has not been set up yet.'));
    return reqOrNull(repo, '').then(function (r) {
      if (!r) throw err('ADMIN404', 'The private repository "' + repo + '" was not found, or the token does not have access to it.');
      if (r.private === false) throw err('ADMINPUBLIC', 'The repository "' + repo + '" is public. The list of people must be in a private repository.');
      return getText(repo, 'people.json');
    }).then(function (f) {
      if (!f) return { model: emptyModel(), sha: null };
      var m;
      try { m = JSON.parse(f.text); } catch (e) { throw err('ADMINJSON', 'people.json in the private repository could not be read.'); }
      return { model: normalise(m), sha: f.sha };
    });
  }
  function saveAdmin(model, sha, message) {
    return putText(cfg.adminRepo(), 'people.json', JSON.stringify(model, null, 2) + '\n', message || 'Studio: update invitations', sha)
      .then(function (r) { return r && r.content ? r.content.sha : null; });
  }

  /* ---------- who sees what ---------- */
  function entryOf(r) {
    var e = { navn: r.navn, fil: r.fil, beskrivelse: r.beskrivelse || '', radius: r.radius || 300, adaptiv: r.adaptiv !== false };
    if (r.rute) e.rute = r.rute;
    return e;
  }
  function routeIdsOf(model, person) {
    var ids = {};
    (person.routes || []).forEach(function (id) { ids[id] = 1; });
    (person.groups || []).forEach(function (gid) {
      model.groups.forEach(function (g) { if (g.id === gid) (g.routes || []).forEach(function (id) { ids[id] = 1; }); });
    });
    return ids;
  }
  function routesOf(model, person) {
    var ids = routeIdsOf(model, person);
    return model.routes.filter(function (r) { return r.access === 'invite' && ids[r.rid]; });
  }
  function personalFiles(model) {
    var out = {};
    model.people.forEach(function (p) {
      out['ture/u-' + p.code + '.json'] = JSON.stringify({ v: 1, routes: routesOf(model, p).map(entryOf) }, null, 1) + '\n';
    });
    return out;
  }
  function linkFor(code) {
    var base = new URL('./', location.href).href.replace(/#.*$/, '');
    return base + '#u=' + code;
  }
  function purgeRoute(model, rid) {
    model.routes = model.routes.filter(function (r) { return r.rid !== rid; });
    model.groups.forEach(function (g) { g.routes = g.routes.filter(function (x) { return x !== rid; }); });
    model.people.forEach(function (p) { p.routes = p.routes.filter(function (x) { return x !== rid; }); });
  }

  /* ---------- files that belong to one route ---------- */
  function routeFileNames(dirList, fil) {
    var base = baseOf(fil), esc = base.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), pat = new RegExp('^' + esc + '-\\d+\\.mp3$');
    return dirList.filter(function (f) { return f.type === 'file' && (f.name === fil || f.name === base + '.audio.json' || pat.test(f.name)); }).map(function (f) { return f.name; });
  }
  function renamePlan(dirList, oldFil, newFil) {
    var ob = baseOf(oldFil), nb = baseOf(newFil);
    return routeFileNames(dirList, oldFil).map(function (name) {
      var to = name === oldFil ? newFil : name.indexOf(ob) === 0 ? nb + name.slice(ob.length) : name;
      return { from: 'ture/' + name, to: 'ture/' + to };
    });
  }

  /* All personal files that should exist, and the ones that no longer should (removed people). */
  function syncPlan(model, dirList) {
    var files = personalFiles(model), wanted = {};
    Object.keys(files).forEach(function (p) { wanted[p.replace(/^ture\//, '')] = 1; });
    var deletes = [];
    dirList.forEach(function (f) { if (f.type === 'file' && /^u-[a-z0-9]+\.json$/.test(f.name) && !wanted[f.name]) deletes.push('ture/' + f.name); });
    return { files: files, deletes: deletes };
  }

  /* ---------- operations ---------- */
  function readTureList() {
    return getText(cfg.repo(), 'ture/ture.json').then(function (f) {
      if (!f) return { list: [], sha: null };
      var list;
      try { list = JSON.parse(f.text); } catch (e) { throw err('LIST', 'The route list (ture.json) could not be read, so nothing was changed.'); }
      return { list: Array.isArray(list) ? list : [], sha: f.sha };
    });
  }
  function tureJsonText(list) { return JSON.stringify(list, null, 2); }

  /* Publish everything in the model: personal files for all people, plus optional renames (new secret names for routes). */
  function publishModel(model, opts) {
    opts = opts || {};
    var repo = cfg.repo();
    return listDir(repo, 'ture').then(function (dir) {
      var plan = syncPlan(model, dir), renames = [], files = plan.files;
      (opts.rotate || []).forEach(function (rid) {
        var r = model.routes.filter(function (x) { return x.rid === rid; })[0];
        if (!r) return;
        var s = splitBase(baseOf(r.fil)), newFil = s.slug + '-' + random(8) + '.gpx';
        var rp = renamePlan(dir, r.fil, newFil);
        if (!rp.length) return;
        renames = renames.concat(rp);
        r.fil = newFil;
      });
      // personal files must list the NEW names, so they are built after the renames
      plan = syncPlan(model, dir); files = plan.files;
      return commitTree(repo, { files: files, deletes: plan.deletes, renames: renames, message: opts.message || 'Studio: update who can see which routes' });
    });
  }

  /* Change who can see an existing route: 'open' | 'invite' | 'draft'. */
  function setRouteAccess(route, access) {
    // route: {fil, navn, beskrivelse, radius, adaptiv, rute, vis, rid?}
    return retry(function () {
      var repo = cfg.repo(), admin, tl;
      return Promise.all([loadAdmin(), readTureList()]).then(function (res) {
        admin = res[0]; tl = res[1];
        var model = admin.model, fil = route.fil;
        var rec = model.routes.filter(function (r) { return r.fil === fil || (route.rid && r.rid === route.rid); })[0];
        var inList = tl.list.filter(function (x) { return x && x.fil === fil; })[0];
        var label = access === 'invite' ? 'invite only' : access === 'draft' ? 'a draft' : 'open to everyone';
        var message = 'Studio: ' + fil + ' is now ' + label;
        if (access === 'open') {
          if (rec) {                                   // from invite only / draft: back into the public list
            var meta = entryOf(rec);
            purgeRoute(model, rec.rid);
            tl.list = tl.list.filter(function (x) { return !(x && x.fil === meta.fil); });
            tl.list.unshift(meta);
          } else if (inList) { delete inList.vis; }
          return finish(repo, model, tl, [], message, admin, null);
        }
        if (rec) { rec.access = access; return finish(repo, model, tl, [], message, admin, rec); }
        // an open (or old hidden) route that has no secret name yet: give it one, and move it out of the public list
        return listDir(repo, 'ture').then(function (dir) {
          var newFil = baseOf(fil) + '-' + random(8) + '.gpx', moves = renamePlan(dir, fil, newFil), src = inList || route;
          if (!moves.length) throw err('MISSING', 'The route file ' + fil + ' was not found in the repository.');
          var created = { rid: random(8), fil: newFil, access: access, navn: src.navn || baseOf(fil), beskrivelse: src.beskrivelse || '', radius: src.radius || 300, adaptiv: src.adaptiv !== false };
          if (src.rute) created.rute = src.rute;
          model.routes.push(created);
          tl.list = tl.list.filter(function (x) { return !(x && x.fil === fil); });
          return finish(repo, model, tl, moves, message, admin, created);
        });
      });
    });
  }
  function finish(repo, model, tl, renames, message, admin, rec) {
    return listDir(repo, 'ture').then(function (dir) {
      var plan = syncPlan(model, dir), files = plan.files;
      files['ture/ture.json'] = tureJsonText(tl.list);
      return commitTree(repo, { files: files, deletes: plan.deletes, renames: renames, message: message });
    }).then(function () { return saveAdmin(model, admin.sha, message); })
      .then(function () { return rec; });
  }

  /* Publish a route that is invite-only or a draft. */
  function publishRoute(entry, gpxText, access) {
    return retry(function () {
      var repo = cfg.repo(), admin;
      return loadAdmin().then(function (a) {
        admin = a;
        var model = a.model, rec = model.routes.filter(function (r) { return r.fil === entry.fil; })[0];
        if (!rec) { rec = { rid: random(8), fil: entry.fil }; model.routes.push(rec); }
        rec.access = access; rec.navn = entry.navn; rec.beskrivelse = entry.beskrivelse || ''; rec.radius = entry.radius || 300; rec.adaptiv = entry.adaptiv !== false;
        if (entry.rute) rec.rute = entry.rute; else delete rec.rute;
        return listDir(repo, 'ture').then(function (dir) {
          var plan = syncPlan(model, dir), files = plan.files;
          files['ture/' + entry.fil] = gpxText;
          return commitTree(repo, { files: files, deletes: plan.deletes, message: 'Studio: ' + entry.fil });
        });
      }).then(function () { return saveAdmin(admin.model, admin.sha, 'Studio: ' + entry.fil); });
    });
  }

  /* Delete an invite-only or draft route (files, audio, and every mention). */
  function deleteRoute(fil) {
    return retry(function () {
      var repo = cfg.repo(), admin;
      return loadAdmin().then(function (a) {
        admin = a;
        var model = a.model, rec = model.routes.filter(function (r) { return r.fil === fil; })[0];
        if (rec) purgeRoute(model, rec.rid);
        return listDir(repo, 'ture').then(function (dir) {
          var plan = syncPlan(model, dir), names = routeFileNames(dir, fil);
          if (!names.length && !rec) throw err('MISSING', 'Nothing to delete was found in the repository.');
          return commitTree(repo, { files: plan.files, deletes: plan.deletes.concat(names.map(function (n) { return 'ture/' + n; })), message: 'Studio: delete route ' + fil })
            .then(function () { return names; });
        });
      }).then(function (names) { return saveAdmin(admin.model, admin.sha, 'Studio: delete route ' + fil).then(function () { return names; }); });
    });
  }

  /* The routes that are not open, for the route list in Studio. */
  function hiddenRoutes() {
    return loadAdmin().then(function (a) { return a.model.routes.map(function (r) { var e = entryOf(r); e._access = r.access; e._rid = r.rid; return e; }); });
  }

  /* Check that the private repository can be used. */
  function checkAdmin(repo) {
    return reqOrNull(repo, '').then(function (r) {
      if (!r) throw err('ADMIN404', 'The repository "' + repo + '" was not found. Create it on GitHub first, and let the token reach it.');
      if (r.private === false) throw err('ADMINPUBLIC', 'The repository "' + repo + '" is public. Make it private first (Settings > Danger zone > Change visibility).');
      if (r.permissions && !r.permissions.push) throw err('ADMINREAD', 'The token can read "' + repo + '" but not write to it. Set Contents to Read and write.');
      return true;
    });
  }

  global.Access = {
    cfg: cfg, random: random, newCode: newCode, prettyCode: prettyCode, normCode: normCode, linkFor: linkFor,
    splitBase: splitBase, baseOf: baseOf, entryOf: entryOf, routesOf: routesOf, routeIdsOf: routeIdsOf, personalFiles: personalFiles,
    emptyModel: emptyModel, loadAdmin: loadAdmin, saveAdmin: saveAdmin, checkAdmin: checkAdmin,
    publishModel: publishModel, setRouteAccess: setRouteAccess, publishRoute: publishRoute, deleteRoute: deleteRoute, hiddenRoutes: hiddenRoutes,
    purgeRoute: purgeRoute, retry: retry, retryDelays: [400, 900, 1600, 2500, 4000], longRetryDelays: [500, 1000, 2000, 3000, 5000, 8000, 12000, 15000],
    commitTree: commitTree, toB64: toB64, fromB64: fromB64
  };
})(window);
