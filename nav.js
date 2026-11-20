/* Wayside navigation (shared by Wayside and Wayside Studio).
   Works on a route track: a list of [lat, lon]. It does three things:
   1. finds the turns along the track (or reads turns that were saved in the GPX file),
   2. works out where on the track a car is, and how far it is to the next turn,
   3. writes the words that are spoken ("In 300 metres, turn right").
   No map, no network. Everything here is plain calculation, so it can be tested without a browser. */
(function (root) {
  'use strict';
  var NS = 'https://wayside.app/ns/1';
  var RAD = Math.PI / 180;

  /* ---------- geometry ---------- */
  function dist(la1, lo1, la2, lo2) {
    var R = 6371000, dLat = (la2 - la1) * RAD, dLon = (lo2 - lo1) * RAD;
    var a = Math.sin(dLat / 2) * Math.sin(dLat / 2) + Math.cos(la1 * RAD) * Math.cos(la2 * RAD) * Math.sin(dLon / 2) * Math.sin(dLon / 2);
    return 2 * R * Math.asin(Math.min(1, Math.sqrt(a)));
  }
  function bearing(la1, lo1, la2, lo2) {                 // degrees, 0 = north, clockwise
    var y = Math.sin((lo2 - lo1) * RAD) * Math.cos(la2 * RAD);
    var x = Math.cos(la1 * RAD) * Math.sin(la2 * RAD) - Math.sin(la1 * RAD) * Math.cos(la2 * RAD) * Math.cos((lo2 - lo1) * RAD);
    return (Math.atan2(y, x) / RAD + 360) % 360;
  }
  function angDiff(a, b) {                               // signed change from heading a to heading b, -180..180 (positive = to the right)
    var d = (b - a + 540) % 360 - 180;
    return d === -180 ? 180 : d;
  }

  /* ---------- a track with distances along it ---------- */
  function prepare(pts) {
    var out = [], cum = [], total = 0;
    for (var i = 0; i < pts.length; i++) {
      var p = pts[i];
      if (!p || isNaN(p[0]) || isNaN(p[1])) continue;
      if (out.length) {
        var d = dist(out[out.length - 1][0], out[out.length - 1][1], p[0], p[1]);
        if (d < 1) continue;                              // the same spot twice
        total += d;
      }
      out.push([p[0], p[1]]); cum.push(total);
    }
    return { pts: out, cum: cum, total: total };
  }
  function pointAtS(prep, s) {                            // [lat, lon] at s metres along the track
    var pts = prep.pts, cum = prep.cum;
    if (!pts.length) return null;
    if (s <= 0) return pts[0].slice();
    if (s >= prep.total) return pts[pts.length - 1].slice();
    var lo = 0, hi = cum.length - 1;
    while (hi - lo > 1) { var m = (lo + hi) >> 1; if (cum[m] <= s) lo = m; else hi = m; }
    var f = (s - cum[lo]) / ((cum[hi] - cum[lo]) || 1);
    return [pts[lo][0] + (pts[hi][0] - pts[lo][0]) * f, pts[lo][1] + (pts[hi][1] - pts[lo][1]) * f];
  }
  function segAtS(prep, s) {                              // index of the segment that holds s
    var cum = prep.cum, lo = 0, hi = cum.length - 1;
    if (hi < 1) return 0;
    if (s <= 0) return 0;
    if (s >= cum[hi]) return hi - 1;
    while (hi - lo > 1) { var m = (lo + hi) >> 1; if (cum[m] <= s) lo = m; else hi = m; }
    return lo;
  }

  /* Where is the car on the track?
     Looks in a window around where it was last (hintS), so a route that crosses itself or comes back to its start does not confuse it.
     Without a hint, or when the window finds nothing close, the whole track is searched (ties go to the earlier part). */
  function locate(prep, lat, lon, hintS, opt) {
    opt = opt || {};
    var pts = prep.pts, n = pts.length;
    if (n < 2) return null;
    var kx = 111320 * Math.cos(lat * RAD), ky = 110540;
    var from = 0, to = n - 2;
    if (hintS != null && !opt.global) {
      from = segAtS(prep, Math.max(0, hintS - (opt.back == null ? 80 : opt.back)));
      to = segAtS(prep, Math.min(prep.total, hintS + (opt.ahead == null ? 2500 : opt.ahead)));
    }
    function scan(a, b) {
      var best = null;
      for (var i = a; i <= b; i++) {
        var ax = (pts[i][1] - lon) * kx, ay = (pts[i][0] - lat) * ky;
        var bx = (pts[i + 1][1] - lon) * kx, by = (pts[i + 1][0] - lat) * ky;
        var dx = bx - ax, dy = by - ay, l2 = dx * dx + dy * dy;
        var u = l2 ? Math.max(0, Math.min(1, -(ax * dx + ay * dy) / l2)) : 0;
        var px = ax + u * dx, py = ay + u * dy, d = Math.sqrt(px * px + py * py);
        if (!best || d < best.off - 15) {                 // a clearly closer part wins; near-ties keep the earlier one
          best = { off: d, s: prep.cum[i] + u * (prep.cum[i + 1] - prep.cum[i]), seg: i, lat: lat + py / ky, lon: lon + px / kx };
        }
      }
      return best;
    }
    var r = scan(from, to);
    if (r && hintS != null && !opt.global && r.off > (opt.far == null ? 150 : opt.far)) {
      var g = scan(0, n - 2);
      if (g && g.off < r.off - 30) r = g;
    }
    return r;
  }

  /* ---------- finding the turns from the shape of the track ----------
     The track is walked in 10 m steps. A turn is a place where the heading changes a lot over a short stretch,
     and where the road before and after is fairly straight. A winding road, where the heading changes all the time, gives no turns.
     There is no road network here, so roundabouts and junctions cannot be told apart from the shape alone. Studio lets you correct them. */
  var STEP = 10;
  function resample(prep) {
    var xs = [], ys = [], ss = [];
    var lat0 = prep.pts[0][0], lon0 = prep.pts[0][1];
    var kx = 111320 * Math.cos(lat0 * RAD), ky = 110540;
    for (var s = 0; s <= prep.total; s += STEP) {
      var p = pointAtS(prep, s);
      xs.push((p[1] - lon0) * kx); ys.push((p[0] - lat0) * ky); ss.push(s);
    }
    return { x: xs, y: ys, s: ss, lat0: lat0, lon0: lon0, kx: kx, ky: ky };
  }
  function hdg(R, a, b) { return (Math.atan2(R.x[b] - R.x[a], R.y[b] - R.y[a]) / RAD + 360) % 360; }
  function classify(ang) {
    var a = Math.abs(ang), side = ang > 0 ? 'right' : 'left';
    if (a < 30) return null;
    if (a < 60) return 'slight-' + side;
    if (a < 135) return side;
    if (a < 165) return 'sharp-' + side;
    return 'uturn';
  }
  /* Two settings. "normal" finds clear corners. "more" also finds gentle forks (30 degrees and up) and tight bends, and is meant for routes
     where "normal" misses turns; it gives more false turns on winding roads, which Studio lets you delete. */
  var SENS = {
    normal: { minA: 40, nms: 4, spread: 22, tierB: 55, conc: 20 },
    more:   { minA: 30, nms: 4, spread: 35, tierB: 35, conc: 0 }
  };
  function detectTurns(prep, opt) {
    opt = opt || {};
    var P = SENS[opt.sensitivity] || SENS.normal;
    if (opt.minAngle) P = { minA: opt.minAngle, nms: P.nms, spread: P.spread, tierB: P.tierB, conc: P.conc };
    if (!prep || prep.pts.length < 3 || prep.total < 120) return [];
    var R = resample(prep), n = R.x.length;
    if (n < 16) return [];
    var T = [];                                           // heading change over 60 m around each sample
    for (var i = 0; i < n; i++) T.push(i < 3 || i > n - 4 ? 0 : angDiff(hdg(R, i - 3, i), hdg(R, i, i + 3)));
    var ev = [];
    for (var j = 4; j <= n - 5; j++) {
      var v = Math.abs(T[j]);
      if (v < P.minA) continue;
      var peak = true;
      for (var k = Math.max(0, j - P.nms); k <= Math.min(n - 1, j + P.nms); k++) {
        if (k !== j && (Math.abs(T[k]) > v || (Math.abs(T[k]) === v && k < j))) { peak = false; break; }
      }
      if (!peak) continue;
      // Is the road straight before and after (a junction on a plain road)? Where the track is too short to look 100 m ahead, that side is not judged.
      var pre = j - 14 >= 0 ? Math.abs(angDiff(hdg(R, j - 14, j - 9), hdg(R, j - 9, j - 4))) : 0;
      var post = j + 14 <= n - 1 ? Math.abs(angDiff(hdg(R, j + 4, j + 9), hdg(R, j + 9, j + 14))) : 0;
      var iso = pre <= P.spread && post <= P.spread;
      var conc = 0;                                       // the sharpest change in a single 10 m step: a corner has one, a bend does not
      for (var q = Math.max(1, j - 2); q <= Math.min(n - 2, j + 2); q++) conc = Math.max(conc, Math.abs(angDiff(hdg(R, q - 1, q), hdg(R, q, q + 1))));
      // Not straight around it (town streets, a bend right after a junction): it still counts if it is a clear, sharp corner.
      if (!(iso || (v >= P.tierB && conc >= P.conc))) continue;
      var ang = iso ? angDiff(hdg(R, Math.max(0, j - 9), j - 3), hdg(R, j + 3, Math.min(n - 1, j + 9))) : T[j];
      ev.push({ j: j, ang: ang });
    }
    // A long, tight curve (a radius under about 60 m for 150 degrees or more, within 300 m) is a roundabout or a ramp loop, even when the track is smooth
    // and has no sharp corner. It replaces the single turns found inside it.
    var D = [];
    for (var m = 0; m < n; m++) D.push(m < 1 || m > n - 2 ? 0 : angDiff(hdg(R, m - 1, m), hdg(R, m, m + 1)));
    var loops = [];
    for (var a = 1; a < n - 1;) {
      if (Math.abs(D[a]) < 6) { a++; continue; }
      var dirPos = D[a] > 0, b = a, tot = 0, gap = 0, last = a;
      while (b < n - 1 && gap <= 1 && (D[b] > 0) === dirPos) {
        if (Math.abs(D[b]) >= 6) { tot += D[b]; last = b; gap = 0; } else { tot += D[b]; gap++; }
        b++;
      }
      if (Math.abs(tot) >= 150 && (last - a) * STEP <= 300 && Math.abs(tot) / Math.max(1, (last - a)) >= 6) loops.push({ from: a, to: last, ang: tot });
      a = Math.max(b, a + 1);
    }
    ev = ev.filter(function (x) { return !loops.some(function (L) { return x.j >= L.from - 5 && x.j <= L.to + 5; }); });
    loops.forEach(function (L) { ev.push({ j: Math.round((L.from + L.to) / 2), ang: L.ang, loop: true }); });
    ev.sort(function (x, y) { return x.j - y.j; });
    // Same-direction turns close together that add up to a loop (a roundabout, a ramp) are one thing, not several.
    var turns = [];
    function add(j, ang, type, merged) {
      var s = R.s[j];
      if (s < 25 || s > prep.total - 60) return;           // nothing useful to say right at the start or at the end
      var lat = R.lat0 + R.y[j] / R.ky, lon = R.lon0 + R.x[j] / R.kx;
      var t = { lat: lat, lon: lon, at: Math.round(s), type: type || classify(ang), angle: Math.round(ang), auto: true };
      if (merged) t.loop = merged;
      if (t.type) turns.push(t);
    }
    for (var e = 0; e < ev.length;) {
      if (ev[e].loop) { add(ev[e].j, ev[e].ang, Math.abs(ev[e].ang) >= 200 ? 'roundabout' : null, 1); e++; continue; }
      var f = e, sum = ev[e].ang;
      while (f + 1 < ev.length && !ev[f + 1].loop && (R.s[ev[f + 1].j] - R.s[ev[f].j]) <= 130 && (ev[f + 1].ang > 0) === (ev[e].ang > 0)) { f++; sum += ev[f].ang; }
      if (f > e && Math.abs(sum) >= 250) { add(ev[Math.round((e + f) / 2)].j, sum, 'roundabout', f - e + 1); e = f + 1; }
      else { add(ev[e].j, ev[e].ang, null, 0); e++; }
    }
    return turns;
  }

  /* Turns from OSRM steps (Studio asks OSRM for a driving route between the stops, and OSRM knows junctions and roundabouts). */
  function turnsFromOsrm(route) {
    var out = [];
    try {
      (route.legs || []).forEach(function (leg) {
        (leg.steps || []).forEach(function (st) {
          var m = st.maneuver || {}, loc = m.location;
          if (!loc || loc.length < 2) return;
          var mod = String(m.modifier || ''), t = String(m.type || ''), type = null, exit = null;
          var side = /left/.test(mod) ? 'left' : /right/.test(mod) ? 'right' : '';
          if (t === 'depart' || t === 'arrive' || t === 'continue' || t === 'new name' || t === 'notification') return;
          if (t === 'roundabout' || t === 'rotary' || t === 'roundabout turn' || t === 'exit roundabout' || t === 'exit rotary') {
            if (t.indexOf('exit') === 0) return;
            type = 'roundabout'; exit = Number(m.exit) > 0 ? Number(m.exit) : null;
          } else if (t === 'fork') {
            if (!side) return; type = 'fork-' + side;
          } else if (t === 'turn' || t === 'end of road' || t === 'on ramp' || t === 'off ramp' || t === 'merge') {
            if (t === 'merge') return;
            if (mod === 'uturn') type = 'uturn';
            else if (!side) return;                       // straight on: nothing to say
            else if (/slight/.test(mod)) type = 'slight-' + side;
            else if (/sharp/.test(mod)) type = 'sharp-' + side;
            else type = side;
          } else return;
          var turn = { lat: loc[1], lon: loc[0], type: type, auto: true, source: 'osrm' };
          if (exit) turn.exit = exit;
          if (st.name) turn.name = String(st.name);
          out.push(turn);
        });
      });
    } catch (e) { return []; }
    return out;
  }

  /* Give every turn its distance along the track ("at"), and sort them. */
  function place(prep, turns) {
    var list = [];
    (turns || []).forEach(function (t) {
      var s = null, loc;
      if (t.at != null && !isNaN(t.at)) {                 // "at" is only a hint (Studio may have used a thinner copy of the track); the position decides
        var w = Math.max(500, prep.total * 0.02);
        loc = locate(prep, t.lat, t.lon, Number(t.at), { back: w, ahead: w, far: 60 });
      } else loc = locate(prep, t.lat, t.lon, null, { global: true });
      if (loc && loc.off < 120) s = loc.s;
      if (s == null) return;
      var c = {}; Object.keys(t).forEach(function (k) { c[k] = t[k]; });
      c.at = Math.round(s);
      list.push(c);
    });
    list.sort(function (a, b) { return a.at - b.at; });
    var out = [];                                         // two turns closer than 25 m are one
    list.forEach(function (t) { if (!out.length || t.at - out[out.length - 1].at >= 25) out.push(t); });
    return out;
  }

  /* ---------- words ---------- */
  var TYPES = ['left', 'right', 'slight-left', 'slight-right', 'sharp-left', 'sharp-right', 'uturn', 'roundabout', 'fork-left', 'fork-right'];
  var LABEL = {
    left: 'Turn left', right: 'Turn right', 'slight-left': 'Bear left', 'slight-right': 'Bear right',
    'sharp-left': 'Sharp left', 'sharp-right': 'Sharp right', uturn: 'U-turn', roundabout: 'Roundabout',
    'fork-left': 'Keep left at the fork', 'fork-right': 'Keep right at the fork'
  };
  function actionText(t, da) {
    var ex = t.exit;
    if (da) {
      var D = {
        left: 'drej til venstre', right: 'drej til højre', 'slight-left': 'hold lidt til venstre', 'slight-right': 'hold lidt til højre',
        'sharp-left': 'drej skarpt til venstre', 'sharp-right': 'drej skarpt til højre', uturn: 'vend om',
        'fork-left': 'hold til venstre ved vejdelingen', 'fork-right': 'hold til højre ved vejdelingen'
      };
      if (t.type === 'roundabout') return ex ? 'tag ' + ex + '. afkørsel i rundkørslen' : 'kør ind i rundkørslen og følg ruten';
      return (D[t.type] || 'fortsæt') + (t.name && t.type.indexOf('fork') !== 0 && t.type !== 'uturn' ? ' ind på ' + t.name : '');
    }
    var E = {
      left: 'turn left', right: 'turn right', 'slight-left': 'bear left', 'slight-right': 'bear right',
      'sharp-left': 'turn sharp left', 'sharp-right': 'turn sharp right', uturn: 'make a U-turn',
      'fork-left': 'keep left at the fork', 'fork-right': 'keep right at the fork'
    };
    if (t.type === 'roundabout') {
      var ord = ex === 1 ? '1st' : ex === 2 ? '2nd' : ex === 3 ? '3rd' : ex ? ex + 'th' : '';
      return ex ? 'at the roundabout take the ' + ord + ' exit' : 'enter the roundabout and follow the route';
    }
    return (E[t.type] || 'continue') + (t.name && t.type.indexOf('fork') !== 0 && t.type !== 'uturn' ? ' onto ' + t.name : '');
  }
  function cap(s) { return s.charAt(0).toUpperCase() + s.slice(1); }
  function distWords(m, da) {                             // 480 -> "500 meter"
    if (m >= 950) {
      var km = Math.round(m / 100) / 10;
      var txt = (da ? String(km).replace('.', ',') : String(km));
      return da ? txt + ' kilometer' : txt + (km === 1 ? ' kilometre' : ' kilometres');
    }
    var r = m >= 500 ? Math.round(m / 100) * 100 : Math.round(m / 50) * 50;
    if (r < 50) r = 50;
    return r + (da ? ' meter' : ' metres');
  }
  function say(turn, kind, meters, da) {                  // kind: 'far' (with distance) or 'near' (right now)
    var a = actionText(turn, da);
    if (kind === 'far') return da ? 'Om ' + distWords(meters, true) + ', ' + a + '.' : 'In ' + distWords(meters, false) + ', ' + a + '.';
    return cap(a) + '.';
  }
  function offRouteText(da) { return da ? 'Du er kørt af ruten.' : 'You are off the route.'; }
  function backOnText(da) { return da ? 'Tilbage på ruten.' : 'Back on the route.'; }
  function arrivedText(da) { return da ? 'Du er fremme.' : 'You have arrived.'; }

  /* ---------- saving turns in the GPX file ----------
     <gpx> ... <extensions><turns xmlns="https://wayside.app/ns/1" edited="1"><turn lat lon at type exit name/></turns></extensions></gpx>
     "edited" is there once somebody has looked at the list in Studio, even if the list is empty (so "no turns" is kept as it is). */
  function turnsFromDoc(doc) {
    var all = doc.getElementsByTagName('turns'), node = null;
    for (var n = 0; n < all.length; n++) if (all[n].namespaceURI === NS) { node = all[n]; break; }   // only our own element counts
    if (!node) return null;
    var out = [], kids = node.children;
    for (var i = 0; i < kids.length; i++) {
      var k = kids[i];
      if ((k.localName || k.nodeName).toLowerCase() !== 'turn') continue;
      var lat = parseFloat(k.getAttribute('lat')), lon = parseFloat(k.getAttribute('lon')), type = k.getAttribute('type');
      if (isNaN(lat) || isNaN(lon) || TYPES.indexOf(type) === -1) continue;
      var t = { lat: lat, lon: lon, type: type };
      var at = parseFloat(k.getAttribute('at')); if (!isNaN(at)) t.at = at;
      var ex = parseInt(k.getAttribute('exit'), 10); if (ex > 0) t.exit = ex;
      var nm = k.getAttribute('name'); if (nm) t.name = nm;
      out.push(t);
    }
    return out;
  }
  function writeTurns(doc, turns) {                       // replaces any earlier <turns>, puts a new one last in <extensions> of <gpx>
    var rootEl = doc.documentElement, ns = rootEl.namespaceURI;
    Array.prototype.slice.call(doc.getElementsByTagName('turns')).forEach(function (n) { if (n.namespaceURI === NS && n.parentNode) n.parentNode.removeChild(n); });
    var ext = null;
    for (var i = 0; i < rootEl.children.length; i++) if ((rootEl.children[i].localName || '').toLowerCase() === 'extensions') ext = rootEl.children[i];
    if (!ext) { ext = ns ? doc.createElementNS(ns, 'extensions') : doc.createElement('extensions'); rootEl.appendChild(ext); }
    var el = doc.createElementNS(NS, 'turns'); el.setAttribute('edited', '1');
    (turns || []).forEach(function (t) {
      var e = doc.createElementNS(NS, 'turn');
      e.setAttribute('lat', t.lat.toFixed(6)); e.setAttribute('lon', t.lon.toFixed(6));
      if (t.at != null) e.setAttribute('at', String(Math.round(t.at)));
      e.setAttribute('type', t.type);
      if (t.exit) e.setAttribute('exit', String(t.exit));
      if (t.name) e.setAttribute('name', t.name);
      el.appendChild(e);
    });
    ext.appendChild(el);
  }

  /* ---------- what to say, and when ----------
     A small helper that is given where the car is along the track and returns what is due now. */
  function lead(speed) {                                  // metres before a turn: first call, and the last call
    var v = speed != null && speed > 1 ? speed : 12;
    return { far: Math.max(250, Math.min(900, Math.round(v * 20))), near: Math.max(50, Math.min(150, Math.round(v * 5))) };
  }

  var api = {
    NS: NS, TYPES: TYPES, LABEL: LABEL,
    dist: dist, bearing: bearing, angDiff: angDiff,
    prepare: prepare, pointAtS: pointAtS, locate: locate,
    detectTurns: detectTurns, turnsFromOsrm: turnsFromOsrm, place: place,
    say: say, actionText: actionText, distWords: distWords, offRouteText: offRouteText, backOnText: backOnText, arrivedText: arrivedText,
    turnsFromDoc: turnsFromDoc, writeTurns: writeTurns, lead: lead
  };
  if (typeof module === 'object' && module.exports) module.exports = api;
  root.WaysideNav = api;
})(typeof window !== 'undefined' ? window : this);
