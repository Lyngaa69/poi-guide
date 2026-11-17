"""Suggests pronunciations for Danish words from the NST pronunciation lexicon (CC0, Nasjonalbiblioteket).

The lexicon writes sounds as SAMPA. This module turns them into the symbols that the Piper voice was
trained on (espeak style), learned from 24,000 words, and builds a few variants per word that a person
can listen to and choose between. Nothing here decides anything: it only makes candidates.
"""
import gzip, json, os, re

HERE = os.path.dirname(os.path.abspath(__file__))
VOWS = set('iyueo2E9OaAQ@')
VOWEL = {'i':'i','y':'y','u':'u','e':'e','o':'o','a':'a','A':'ɑ','@':'ə','E':'ε','2':'œ','9':'œ','O':'ɒ','Q':'ɒ'}
CONS = {'f':'f','s':'s','h':'h','m':'m','n':'n','l':'l','j':'j','v':'ʋ','w':'w','R':'ʁ','N':'ŋ','D':'ð','S':'ʃ'}

_LEX = None
_TABLE = None

def lexicon():
    global _LEX
    if _LEX is None:
        _LEX = {}
        with gzip.open(os.path.join(HERE, 'nst-da.tsv.gz'), 'rt', encoding='utf-8') as f:
            for line in f:
                w, _, t = line.rstrip('\n').partition('\t')
                _LEX[w] = t.split('|')
    return _LEX

def _table():
    global _TABLE
    if _TABLE is None:
        _TABLE = json.load(open(os.path.join(HERE, 'nst-stops.json'), encoding='utf-8'))
    return _TABLE

def _flat(s):
    s = s.replace('_', '').replace('¤', '')
    flat = []
    for si, syl in enumerate(s.split('$')):
        stress = 'st' if syl[:1] in '"%' else 'un'
        syl = syl.replace('"', '').replace('%', '')
        for t in syl:
            if t in "'?:": continue
            flat.append((si, t, stress))
    return flat

def _cat(t):
    if t in VOWS or t == '6': return 'V'
    if t in 'mnNlRvwjD': return 'N'
    if t == 's': return 's'
    if t in 'bdgptk': return 'T'
    return 'O'

def _stop_symbols(orth, sampa):
    tabs = _table(); flat = _flat(sampa); word = (orth or '').lower(); opos = 0; out = []
    for k, (si, t, stress) in enumerate(flat):
        if t not in 'bdgptk': continue
        pair = {'b':'bp','p':'bp','d':'dt','t':'dt','g':'gk','k':'gk'}[t]
        j = opos; found = '-'
        while j < len(word):
            if word[j] in pair: found = word[j]; break
            j += 1
        if found != '-': opos = j + 1
        prev = _cat(flat[k-1][1]) if k else 'S'
        nxt = _cat(flat[k+1][1]) if k + 1 < len(flat) else 'E'
        seen_v = any(x[1] in VOWS or x[1] == '6' for x in flat[:k] if x[0] == si)
        pos = 'coda' if seen_v else ('first' if si == 0 else 'inner')
        x = (t, found, prev, nxt, pos, stress)
        keys = ['|'.join(x), '|'.join(x[:5]), '|'.join((x[0], x[1], x[4])), '|'.join(x[:2]), x[0]]
        sym = None
        for lvl, key in enumerate(keys):
            if key in tabs[lvl]: sym = tabs[lvl][key]; break
        out.append(sym or {'b':'b','d':'d','g':'ɡ','p':'p','t':'t','k':'k'}[t])
    return out

def convert(sampa, orth=None, stod=False, raw_clusters=False):
    """NST SAMPA -> espeak-style symbols. stod=True puts the glottal stop after the vowel.
       raw_clusters=True keeps the unaspirated stop after s as written (sd, sɡ, sb)."""
    stops = iter(_stop_symbols(orth, sampa)) if orth else None
    out = []
    for syl in sampa.replace('_', '').replace('¤', '').split('$'):
        stress = ''
        if syl.startswith('"'): stress, syl = 'ˈ', syl[1:]
        elif syl.startswith('%'): stress, syl = 'ˌ', syl[1:]
        syl = syl.replace('"', '').replace('%', '')
        toks = []
        for c in syl:
            if c == "'":
                if toks and toks[-1] == 's': toks[-1] = 'ʃ'
                else: toks.append('j')
            elif c == ':': toks.append('ː')
            elif c == '?': toks.append('ʔ' if stod else '')
            else: toks.append(c)
        has_v = any(t in VOWS for t in toks)
        res = []; placed = False; seen_v = False
        for i, t in enumerate(toks):
            nxt_long = i + 1 < len(toks) and toks[i+1] == 'ː'
            if t in VOWS or (t == '6' and not has_v and not seen_v):
                if not placed and stress: res.append(stress); placed = True
                seen_v = True
                if t == '6': res.append('ʌ')
                elif t == 'E' and nxt_long: res.append('ɛ')
                else: res.append(VOWEL[t])
            elif t == '6':
                res.append('ɐ̯')
            elif t == 'ː':
                prev_sym = res[-1] if res else ''
                res.append('' if prev_sym == 'œ' else 'ː')
            elif t and t in 'bdgptk':
                learned = next(stops, None) if stops else None
                raw = {'b':'b','d':'d','g':'ɡ','p':'p','t':'t','k':'k'}[t]
                if raw_clusters and t in 'bdg' and i and toks[i-1] == 's' and not seen_v:
                    res.append(raw)
                else:
                    res.append(learned or raw)
            else:
                res.append(CONS.get(t, t if t in ('ʃ', 'ʔ') else ''))
        out.append(''.join(res))
    return ''.join(out)

def lookup(word):
    """(sampa, how) from the lexicon, directly or as a two-part compound; (None, None) if unknown"""
    lex = lexicon(); w = word.lower()
    if w in lex: return lex[w][0], 'direct'
    best = None
    for i in range(3, len(w) - 2):
        a, b = w[:i], w[i:]
        if a in lex and b in lex:
            sc = min(len(a), len(b))
            if not best or sc > best[0]: best = (sc, a, b)
    if best:
        _, a, b = best
        ta, tb = lex[a][0], lex[b][0]
        tb = tb.replace('"', '%', 1) if '"' in tb else tb
        return ta.replace('?', '') + '$' + tb, 'compound %s+%s' % (a, b)
    return None, None

def candidates(word):
    """list of (id, value, label): value is the IPA between slashes; id A (Piper as it is) is added by the caller"""
    sampa, how = lookup(word)
    if not sampa: return [], None
    seen = set(); out = []
    def add(id_, ipa, label):
        if ipa and ipa not in seen:
            seen.add(ipa); out.append((id_, '/' + ipa + '/', label))
    b = convert(sampa, word)
    c = convert(sampa, word, stod=True)
    d = convert(sampa, word, raw_clusters=True)
    e = convert(sampa, word, stod=True, raw_clusters=True)
    add('B', b, 'NST')
    add('C', c, 'NST with stød')
    add('D', d, 'NST, sd/sg/sb after s')
    add('E', e, 'NST with stød, sd/sg/sb after s')
    return out, how
