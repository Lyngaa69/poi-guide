#!/usr/bin/env python3
"""Makes Danish audio (mp3) for every stop in every route in ture/*.gpx.

  python tools/make_audio.py --plan   shows what needs new audio (needs only Python)
  python tools/make_audio.py          makes the audio (needs piper-tts, ffmpeg and the voice in VOICE_DIR)

Files per route <name>.gpx:
  ture/<name>-01.mp3, -02.mp3 ...   one file per stop, in the order of the stops
  ture/<name>.audio.json            a fingerprint of the text behind each file
A route whose manifest says  "voice": "local:..."  has audio made outside GitHub (for example with
tools/windows/lav-lyd.ps1). This program leaves such routes alone.

Wayside only plays a file when its fingerprint matches the current text of the stop,
so an edited stop never plays old audio.

Word previews for the pronunciation page in Studio are made in ture/udtale/ (ord.json plus one mp3 per variant).
Words you have decided on are listed in tools/udtale.txt (own pronunciation) or tools/udtale-ok.txt (fine as it is).

Pronunciation fixes live in tools/udtale.txt, one per line:  word = how it should sound
  torvet = /tˈɒɐ̯ʋəð/      (between / / or [ ]: exact sounds, IPA; IPA copied from the web works)
  drewsen = drusen          (otherwise: a respelling that the voice reads correctly)
  ~aa = å                   (starts with ~: replaces these letters inside every word)
Lines starting with # are ignored. Words match whole words, in any capitalisation.
"""
import base64, json, os, re, subprocess, sys, time, wave
import urllib.error, urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TURE = ROOT / 'ture'
VOICE_ID = 'piper-da_DK-talesyntese-medium-v1'

# ---------- Danish numbers written as words, so the voice reads them naturally ----------
UNITS = ['nul', 'en', 'to', 'tre', 'fire', 'fem', 'seks', 'syv', 'otte', 'ni']
TEENS = {10: 'ti', 11: 'elleve', 12: 'tolv', 13: 'tretten', 14: 'fjorten', 15: 'femten',
         16: 'seksten', 17: 'sytten', 18: 'atten', 19: 'nitten'}
TENS = {20: 'tyve', 30: 'tredive', 40: 'fyrre', 50: 'halvtreds', 60: 'tres',
        70: 'halvfjerds', 80: 'firs', 90: 'halvfems'}

def below100(n):
    if n < 10: return UNITS[n]
    if n < 20: return TEENS[n]
    t, u = n // 10 * 10, n % 10
    return TENS[t] if u == 0 else UNITS[u] + 'og' + TENS[t]

def digits(n):
    return ' '.join(UNITS[int(c)] for c in str(n))

def num(n):
    if n < 100: return below100(n)
    if n < 1000:
        h, r = divmod(n, 100)
        head = 'hundrede' if h == 1 else UNITS[h] + ' hundrede'
        return head if r == 0 else head + ' og ' + below100(r)
    if n < 1000000:
        th, r = divmod(n, 1000)
        head = 'tusind' if th == 1 else num(th) + ' tusind'
        return head if r == 0 else head + ' og ' + num(r)
    if n < 1000000000:
        m, r = divmod(n, 1000000)
        head = 'en million' if m == 1 else num(m) + ' millioner'
        return head if r == 0 else head + ' og ' + num(r)
    return digits(n)               # very long numbers are read digit by digit

def year(n):
    if 1100 <= n < 2000:
        h, r = divmod(n, 100)
        head = TEENS[h] + ' hundrede'
        return head if r == 0 else head + ' og ' + below100(r)
    return num(n)

def normalize(t):
    t = t.replace('365discount', 'tre seks fem discount').replace("2020'erne", 'tyvetyverne')
    t = re.sub(r'\b(1[1-9]\d{2}|20\d{2})\b', lambda m: year(int(m.group(1))), t)
    t = re.sub(r'\b\d{1,3}(?:\.\d{3})+\b', lambda m: num(int(m.group(0).replace('.', ''))), t)   # 12.000 -> twelve thousand
    t = re.sub(r'\b(\d+)[,.](\d+)\b', lambda m: num(int(m.group(1))) + ' komma ' + digits(m.group(2)), t)
    t = re.sub(r'\b\d+\b', lambda m: num(int(m.group(0))), t)
    return t

# ---------- pronunciation fixes ----------
# ---------- IPA from the web -> what the voice understands ----------
PIPER_SYMBOLS = set(" !\"#$'(),-.0123456789:;?^_abcdefhijklmnopqrstuvwxyzæçðøħŋœǀǁǂǃɐɑɒɓɔɕɖɗɘəɚɛɜɞɟɠɡɢɣɤɥɦɧɨɪɫɬɭɮɯɰɱɲɳɴɵɶɸɹɺɻɽɾʀʁʂʃʄʈʉʊʋʌʍʎʏʐʑʒʔʕʘʙʛʜʝʟʡʢʰʲˈˌːˑ˞ˤ̧̩̪̯̺̻̃βεθχᵻ↑↓ⱱ")
IPA_VOWELS = set('iyɨʉɯuɪʏʊeøɘɵɤoəɛœɜɞʌɔæɐaɶɑɒɚεᵻ')
IPA_CONSONANTS = set('bcdfɡghjklmnŋpqrstvwxzʁʋðʃɕçʒɹɾʔθβχ')

def sanitize_ipa(s):
    """Accepts IPA as written on Wikipedia, Wiktionary or ordnet.dk, e.g. [ˈdɑnˌmɑɡ̊], and turns it into
    what the Piper voice can use: only sounds it knows, the stress mark just before the vowel, and
    p, t, k for the small-ring (voiceless) stops at the end of a syllable."""
    s = s.strip().strip('[]/').strip()
    s = s.replace('g', 'ɡ').replace('.', '').replace('\u203f', '').replace('ˀ', 'ʔ')
    out = []; i = 0
    while i < len(s):
        c = s[i]
        if c in 'bdɡ' and i + 1 < len(s) and s[i + 1] in '\u030a\u0325':        # b̥ d̥ ɡ̊
            nxt = s[i + 2] if i + 2 < len(s) else ''
            coda = nxt == '' or nxt in 'ˈˌ' or nxt in IPA_CONSONANTS
            out.append({'b': 'p', 'd': 't', 'ɡ': 'k'}[c] if coda else c)
            i += 2
            continue
        out.append(c); i += 1
    s = ''.join(out)
    res = []; i = 0                                              # stress mark goes before the vowel, as espeak writes it
    while i < len(s):
        c = s[i]
        if c in 'ˈˌ':
            j = i + 1
            while j < len(s) and s[j] not in IPA_VOWELS and s[j] not in 'ˈˌ':
                j += 1
            if j < len(s) and s[j] in IPA_VOWELS:
                res.extend(s[i + 1:j]); res.append(c); i = j
                continue
        res.append(c); i += 1
    return ''.join(ch for ch in res if ch in PIPER_SYMBOLS)

def load_dictionary():
    entries, rules = [], []
    path = ROOT / 'tools' / 'udtale.txt'
    if not path.exists():
        return entries, rules
    for line in path.read_text(encoding='utf-8').splitlines():
        line = line.strip()
        if not line or line.startswith('#') or '=' not in line:
            continue
        word, value = [x.strip() for x in line.split('=', 1)]
        if not word or not value:
            continue
        if len(value) > 2 and ((value.startswith('/') and value.endswith('/')) or (value.startswith('[') and value.endswith(']'))):
            value = '[[' + sanitize_ipa(value) + ']]'                  # exact sounds, IPA between / / or [ ]
        if word.startswith('~'):
            rules.append((word[1:], value))
        else:
            entries.append((word, value))
    entries.sort(key=lambda e: -len(e[0]))              # longest words first
    return entries, rules

DICTIONARY, RULES = load_dictionary()

def _keep_case(match, value):
    s = match.group(0)
    if len(s) > 1 and s.isupper(): return value.upper()
    if s[0].isupper(): return value[:1].upper() + value[1:]
    return value

def apply_dictionary(text, ipa=True):
    parts = re.split(r'(\[\[.*?\]\])', text)                # never touch exact sounds that are already in the text
    for word, value in DICTIONARY:
        if not ipa and value.startswith('[['):
            continue                                                # exact sounds only work for Piper
        pat = re.compile(r'(?<![\wæøåÆØÅ])' + re.escape(word) + r'(?![\wæøåÆØÅ])', re.IGNORECASE)
        for i in range(0, len(parts), 2):
            parts[i] = pat.sub(lambda m: '\x00' + value + '\x00', parts[i])   # \x00 marks inserted sounds, so later entries skip them
        # re-split so that inserted sounds are protected from the next entries
        joined = ''.join(parts)
        parts = re.split(r'(\x00.*?\x00)', joined)
    out = []
    for i, p in enumerate(parts):
        if i % 2 == 1:                                          # an inserted sound
            out.append(p.strip('\x00'))
        else:
            seg = re.split(r'(\[\[.*?\]\])', p)
            for j in range(0, len(seg), 2):
                for src_letters, value in RULES:
                    seg[j] = re.sub(re.escape(src_letters), lambda m, v=value: _keep_case(m, v), seg[j], flags=re.IGNORECASE)
            out.append(''.join(seg))
    return ''.join(out)

def spoken(text):
    """What is actually sent to the voice: numbers as words, then the pronunciation fixes."""
    return apply_dictionary(normalize(text))

# ---------- reading the stops (same rules as Wayside) ----------
def plain_text(s):
    """Same cleaning as Wayside: <expressions> and other tags are removed, spaces collapsed."""
    s = s or ''
    s = re.sub(r'<br\s*/?>', '. ', s, flags=re.IGNORECASE)
    s = re.sub(r'</p>', ' ', s, flags=re.IGNORECASE)
    s = re.sub(r'<[^>]+>', '', s)
    return re.sub(r'\s+', ' ', s).strip()

def clean(s):
    return plain_text(s)

def fnv1a(text):
    h = 0x811c9dc5
    for b in text.encode('utf-8'):
        h ^= b
        h = (h * 0x01000193) & 0xffffffff
    return '%08x' % h

def child_text(el, names):
    for n in names:
        for ch in el:
            if ch.tag.split('}')[-1].lower() == n:
                t = clean(ch.text)
                if t: return t
    return ''

def raw_child_text(el, names):
    for n in names:
        for ch in el:
            if ch.tag.split('}')[-1].lower() == n:
                raw = re.sub(r'\s+', ' ', ch.text or '').strip()
                if plain_text(raw): return raw
    return ''

def read_stops_raw(gpx):
    """[(plain, raw)] for every stop. plain has no <expressions> (used for fingerprints and the Piper voice),
    raw keeps them (used by the Gemini voice)."""
    root = ET.parse(gpx).getroot()
    out = []
    for el in root.iter():
        if el.tag.split('}')[-1].lower() != 'wpt': continue
        try:
            float(el.get('lat')); float(el.get('lon'))
        except (TypeError, ValueError):
            continue
        raw_name = raw_child_text(el, ['name'])
        name = plain_text(raw_name) or 'Stop %d' % (len(out) + 1)
        if not plain_text(raw_name): raw_name = name
        raw_desc = raw_child_text(el, ['desc', 'cmt'])
        desc = plain_text(raw_desc)
        out.append((name + ('. ' + desc if desc else ''), raw_name + ('. ' + raw_desc if desc else '')))
    return out

def read_stops(gpx):
    return [p for p, _ in read_stops_raw(gpx)]

# ---------- voice settings (tools/lyd.json, edited in Studio) ----------
DEFAULT_SETTINGS = {
    'provider': 'gemini',                      # 'gemini' or 'piper'
    'model': 'gemini-3.8-flash-tts',
    'voice': 'Gacrux',
    'stylePreset': 'podcast',
    'style': 'relaxed podcast host, warm and conversational, natural pacing',
    'numbers': 'model',                        # 'model' = the voice reads numbers itself, 'program' = written out as words first
}

def load_settings():
    s = dict(DEFAULT_SETTINGS)
    try:
        s.update({k: v for k, v in json.loads((ROOT / 'tools' / 'lyd.json').read_text(encoding='utf-8')).items() if k in s})
    except Exception:
        pass
    return s

def active_provider():
    """'piper', 'gemini', or 'none' (Gemini is chosen but there is no key, so nothing is touched)"""
    if load_settings()['provider'] != 'gemini':
        return 'piper'
    return 'gemini' if os.environ.get('GEMINI_API_KEY', '').strip() else 'none'

def voice_id_for(provider):
    if provider == 'gemini':
        s = load_settings()
        return 'gemini:%s:%s' % (s['model'], s['voice'])
    return VOICE_ID

def gemini_text(raw):
    """What is sent to Gemini: the stop text with <expressions> kept, respellings and ~rules applied."""
    s = load_settings()
    parts = re.split(r'(<[^>]*>)', raw)
    out = []
    for i, p in enumerate(parts):
        if i % 2 == 1:
            out.append(p)                                          # an <expression>, left exactly as written
        else:
            if s['numbers'] == 'program': p = normalize(p)
            out.append(apply_dictionary(p, ipa=False))
    return ''.join(out)

def gemini_spoken_hash(raw):
    s = load_settings()
    return fnv1a(json.dumps({'style': s['style'], 'numbers': s['numbers'], 'text': gemini_text(raw)}, ensure_ascii=False, sort_keys=True))

# ---------- planning ----------
def plan_route(gpx, provider='piper'):
    base = gpx.stem
    items = read_stops_raw(gpx)
    stops = [p for p, _ in items]
    raws = [r for _, r in items]
    hashes = [fnv1a(s) for s in stops]
    if provider == 'gemini':
        spoken_hashes = [gemini_spoken_hash(r) for r in raws]
    else:
        spoken_hashes = [fnv1a(spoken(s)) for s in stops]
    vid = voice_id_for(provider)
    width = max(2, len(str(len(stops))))
    man_path = TURE / (base + '.audio.json')
    try:
        man = json.loads(man_path.read_text(encoding='utf-8'))
    except Exception:
        man = {}
    if str(man.get('voice', '')).startswith('local:'):          # audio made on someone's own computer: hands off
        return dict(base=base, stops=stops, raws=raws, hashes=hashes, spoken_hashes=spoken_hashes, width=width, voice_id=vid,
                    todo=[], orphans=[], manifest_ok=True, failed=set(), external=man['voice'])
    same_voice = man.get('voice') == vid
    old = man.get('stops', []) if same_voice else []
    failed = set(man.get('failed', [])) if same_voice else set()
    old_spoken = man.get('spoken') if same_voice else None
    todo = []
    for i, h in enumerate(hashes, 1):
        mp3 = TURE / ('%s-%0*d.mp3' % (base, width, i))
        unchanged = i <= len(old) and old[i - 1] == h
        if unchanged:
            if old_spoken is not None:
                unchanged = i <= len(old_spoken) and old_spoken[i - 1] == spoken_hashes[i - 1]
            else:                                  # old manifest: only stops touched by the dictionary need new audio
                unchanged = spoken(stops[i - 1]) == normalize(stops[i - 1])
        if not (unchanged and (mp3.exists() or i in failed)):
            todo.append(i)
    pat = re.compile('^' + re.escape(base) + r'-(\d+)\.mp3$')
    orphans = [p for p in TURE.iterdir() if (m := pat.match(p.name)) and int(m.group(1)) > len(stops)]
    manifest_ok = same_voice and man.get('stops') == hashes and man.get('spoken') == spoken_hashes
    return dict(base=base, stops=stops, raws=raws, hashes=hashes, spoken_hashes=spoken_hashes, width=width, voice_id=vid,
                todo=todo, orphans=orphans, manifest_ok=manifest_ok, failed=failed)

def all_plans(provider='piper'):
    return [plan_route(g, provider) for g in sorted(TURE.glob('*.gpx')) if read_stops(g)]

def needed(plans):
    return any(p['todo'] or p['orphans'] or not p['manifest_ok'] for p in plans)

# ---------- making audio ----------
def load_voice():
    from piper import PiperVoice
    vdir = Path(os.environ.get('VOICE_DIR', ROOT / '.voice'))
    onnx = next(vdir.glob('*.onnx'))
    return PiperVoice.load(str(onnx), config_path=str(onnx) + '.json')

def make_mp3(voice, text, out_mp3, raw=False):
    wav_path = str(out_mp3) + '.wav'
    with wave.open(wav_path, 'wb') as w:
        voice.synthesize_wav(text if raw else spoken(text), w)
    subprocess.run(['ffmpeg', '-y', '-loglevel', 'error', '-i', wav_path,
                    '-af', 'loudnorm=I=-16:TP=-1.5:LRA=11,apad=pad_dur=0.4',
                    '-ac', '1', '-ar', '22050', '-b:a', '64k', str(out_mp3)], check=True)
    os.remove(wav_path)

# ---------- the Gemini voice ----------
class Transient(Exception):      # worth trying again later (rate limit, server hiccup)
    pass

class Permanent(Exception):      # trying again will not help for this stop
    pass

class BadKey(Exception):
    pass

def _redact(msg):
    key = os.environ.get('GEMINI_API_KEY', '').strip()
    return msg.replace(key, '***') if key else msg

def gemini_body(text, settings):
    content = {'type': 'text', 'text': text}
    if settings['style'].strip():
        content['annotations'] = [{'type': 'speech_metadata', 'style': settings['style'].strip()}]
    return {
        'model': settings['model'],
        'input': [{'type': 'user_input', 'content': [content]}],
        'response_format': {'type': 'audio'},
        'generation_config': {'speech_config': [{'voice': settings['voice']}]},
    }

def find_audio(resp):
    found = []
    def walk(x):
        if isinstance(x, dict):
            if x.get('type') == 'audio' and isinstance(x.get('data'), str):
                found.append(x['data'])
            for v in x.values(): walk(v)
        elif isinstance(x, list):
            for v in x: walk(v)
    walk(resp.get('steps', resp))
    if not found:
        raise Permanent('The answer from Gemini had no audio in it')
    return base64.b64decode(found[-1])

def gemini_call(text, settings):
    url = os.environ.get('GEMINI_API_BASE', 'https://generativelanguage.googleapis.com').rstrip('/') + '/v1beta/interactions'
    req = urllib.request.Request(url, data=json.dumps(gemini_body(text, settings)).encode('utf-8'), method='POST', headers={
        'Content-Type': 'application/json', 'x-goog-api-key': os.environ['GEMINI_API_KEY'].strip()})
    try:
        with urllib.request.urlopen(req, timeout=180) as r:
            return find_audio(json.loads(r.read().decode('utf-8')))
    except urllib.error.HTTPError as e:
        detail = _redact(e.read().decode('utf-8', 'replace')[:300])
        if e.code in (401, 403):
            raise BadKey('HTTP %d: %s' % (e.code, detail))
        if e.code in (429, 500, 502, 503, 504):
            t = Transient('HTTP %d: %s' % (e.code, detail)); t.retry_after = e.headers.get('Retry-After'); raise t
        raise Permanent('HTTP %d: %s' % (e.code, detail))
    except (urllib.error.URLError, TimeoutError, ConnectionError) as e:
        raise Transient(_redact(str(e)))

def gemini_wav(text, settings):
    attempts = int(os.environ.get('GEMINI_ATTEMPTS', '4'))
    for k in range(1, attempts + 1):
        try:
            return gemini_call(text, settings)
        except Transient as e:
            if k == attempts: raise
            wait = float(os.environ.get('GEMINI_RETRY_SLEEP', '0') or 0) or None
            ra = getattr(e, 'retry_after', None)
            if wait is None:
                wait = min(90.0, float(ra)) if ra and str(ra).replace('.', '', 1).isdigit() else 20.0 * k
            print('Gemini asked us to wait (%s). Trying again in %d s.' % (_redact(str(e))[:80], wait))
            time.sleep(wait)

def make_mp3_gemini(raw, out_mp3, settings):
    data = gemini_wav(gemini_text(raw), settings)
    wav_path = str(out_mp3) + '.wav'
    if data[:4] == b'RIFF':
        open(wav_path, 'wb').write(data)
    else:                                                       # headerless 16-bit, 24 kHz, mono
        with wave.open(wav_path, 'wb') as w:
            w.setnchannels(1); w.setsampwidth(2); w.setframerate(24000); w.writeframes(data)
    subprocess.run(['ffmpeg', '-y', '-loglevel', 'error', '-i', wav_path,
                    '-af', 'loudnorm=I=-16:TP=-1.5:LRA=11,apad=pad_dur=0.4',
                    '-ac', '1', '-ar', '24000', '-b:a', '64k', str(out_mp3)], check=True)
    os.remove(wav_path)

def generate_gemini(plans):
    settings = load_settings()
    pace = float(os.environ.get('GEMINI_PACE', '6.5'))
    deadline = time.time() + float(os.environ.get('AUDIO_TIME_BUDGET', '840'))
    last = 0.0; stop_all = False; trouble = 0
    print('Voice: Gemini %s, %s. Style: %s' % (settings['model'], settings['voice'], settings['style'] or '(none)'))
    for p in plans:
        if p.get('external'):
            continue
        for path in p['orphans']:
            path.unlink(); print('removed', path.name)
        failed = set(p['failed']) - set(p['todo'])
        for i in p['todo']:
            if stop_all or time.time() > deadline:
                if not stop_all:
                    print('::warning::Time budget used up. The stops that are missing are made the next time the job runs.')
                stop_all = True
                continue
            if last and time.time() - last < pace:
                time.sleep(pace - (time.time() - last))
            out = TURE / ('%s-%0*d.mp3' % (p['base'], p['width'], i))
            try:
                make_mp3_gemini(p['raws'][i - 1], out, settings)
                last = time.time(); trouble = 0
                failed.discard(i); print('made', out.name)
            except BadKey as e:
                print('::error::Gemini did not accept the key (GEMINI_API_KEY). Check the secret in GitHub. %s' % _redact(str(e)))
                sys.exit(1)
            except Transient as e:
                last = time.time(); trouble += 1
                if out.exists(): out.unlink()
                print('::warning::Gemini was busy for stop %d in %s (%s). It is tried again at the next run.' % (i, p['base'], _redact(str(e))[:120]))
                if trouble >= 3:
                    print('::warning::Gemini keeps saying no. Stopping for now.')
                    stop_all = True
            except Exception as e:
                last = time.time()
                failed.add(i)
                if out.exists(): out.unlink()
                print('::warning::No audio for stop %d in %s: %s: %s' % (i, p['base'], type(e).__name__, _redact(str(e))[:200]))
        (TURE / (p['base'] + '.audio.json')).write_text(
            json.dumps({'voice': p['voice_id'], 'stops': p['hashes'], 'spoken': p['spoken_hashes'], 'failed': sorted(failed)}, indent=2) + '\n', encoding='utf-8')

# ---------- word previews (the pronunciation page in Studio) ----------
UD_DIR = TURE / 'udtale'          # inside ture/, so the existing commit step saves it
STOP_WORDS = set("""og i på af at en et er den det til med som for der de du jeg han hun vi man ikke kan skal vil har have hvor fra ved om var blev bliver kom kommer går ligger lidt mod over under ind ud op ned her dér da så men eller også både hele hvert denne dette disse sig sin sit deres din dit dig mig nu hvis når dem ham hende os jer sådan sådanne anden andre andet først sidst alle alt noget nogle ingen mere mest meget mange få flere fleste cirka omkring efter før mellem siden indtil igen stadig altså kun bare blot dog jo nok måske ville kunne skulle måtte blive været haft fået givet sat lavet ligget stået gjort sagt set taget kaldt kaldes regnes fundet bygget åbnet holdt kører køre fremme starter turen ruten stoppet stop hvad hvem hvordan hvorfor hvilken hvilke altid aldrig ofte nogen ny nye nyt gamle gammel stor store stort lille små god gode godt dag år tid sted vej side del nord syd øst vest""".split())

def decided_words():
    keys = {w.lower() for w, _ in DICTIONARY}
    ok = ROOT / 'tools' / 'udtale-ok.txt'
    if ok.exists():
        for line in ok.read_text(encoding='utf-8').splitlines():
            line = line.strip()
            if line and not line.startswith('#'):
                keys.add(line.lower())
    return keys

def slug(word):
    s = word.lower().replace('æ', 'ae').replace('ø', 'oe').replace('å', 'aa')
    return re.sub(r'[^a-z0-9]+', '-', s).strip('-') or 'ord'

def collect_words():
    info = {}
    for g in sorted(TURE.glob('*.gpx')):
        for s in read_stops(g):
            for mo in re.finditer(r"[A-Za-zÆØÅæøå]+", s):
                w = mo.group(0); k = w.lower()
                if k in STOP_WORDS or (len(k) < 4 and not w[0].isupper()):
                    continue
                e = info.setdefault(k, {'forms': {}, 'count': 0, 'context': ''})
                e['count'] += 1
                e['forms'][w] = e['forms'].get(w, 0) + 1
                if not e['context']:
                    a, b = max(0, mo.start() - 42), min(len(s), mo.end() + 42)
                    e['context'] = ('…' if a else '') + s[a:b].strip() + ('…' if b < len(s) else '')
    return info

def preview_plan():
    """what the pronunciation page should show, and whether the preview files are up to date"""
    try:
        import nst_convert
    except Exception:
        nst_convert = None
    done = decided_words()
    words = []
    for k, e in sorted(collect_words().items()):
        if k in done:
            continue
        shown = max(e['forms'], key=lambda f: e['forms'][f])
        variants = [{'id': 'A', 'label': 'As now (Piper)', 'value': ''}]
        how = None
        if nst_convert:
            cands, how = nst_convert.candidates(k)
            variants += [{'id': i, 'label': l, 'value': v} for i, v, l in cands]
        for v in variants:
            v['file'] = 'ture/udtale/%s-%s.mp3' % (slug(k), v['id'])
        words.append({'word': shown, 'key': k, 'count': e['count'], 'context': e['context'], 'how': how or '', 'variants': variants})
    return {'words': words}

def previews_needed(plan):
    path = UD_DIR / 'ord.json'
    try:
        old = json.loads(path.read_text(encoding='utf-8'))
    except Exception:
        old = None
    if old != plan:
        return True
    return any(not (ROOT / v['file']).exists() for w in plan['words'] for v in w['variants'])

def make_previews(plan, voice_loader):
    UD_DIR.mkdir(exist_ok=True)
    path = UD_DIR / 'ord.json'
    try:
        old = json.loads(path.read_text(encoding='utf-8'))
    except Exception:
        old = {'words': []}
    old_val = {(w['key'], v['id']): v['value'] for w in old['words'] for v in w['variants']}
    wanted = set(); voice = None
    for w in plan['words']:
        for v in w['variants']:
            out = ROOT / v['file']; wanted.add(out.name)
            if out.exists() and old_val.get((w['key'], v['id'])) == v['value']:
                continue
            try:
                if voice is None: voice = voice_loader()
                text = w['key'] if v['id'] == 'A' else '[[' + v['value'].strip('/') + ']]'
                make_mp3(voice, text, out, raw=True)
            except Exception as e:
                print('::warning::No preview for %s %s: %s: %s' % (w['key'], v['id'], type(e).__name__, e))
    for f in UD_DIR.glob('*.mp3'):
        if f.name not in wanted:
            f.unlink()
    path.write_text(json.dumps(plan, ensure_ascii=False, indent=1) + '\n', encoding='utf-8')
    print('previews: %d words listed' % len(plan['words']))

def main():
    provider = active_provider()
    plans = all_plans(provider) if provider != 'none' else []
    if '--plan' in sys.argv:
        s = load_settings()
        if provider == 'none':
            print('::warning::The voice is set to Gemini, but GEMINI_API_KEY is not set in GitHub. No audio is made until it is.')
        elif provider == 'gemini':
            print('audio engine: Gemini (%s, %s)' % (s['model'], s['voice']))
        else:
            print('audio engine: Piper')
        for p in plans:
            if p.get('external'):
                print('%s: %d stops, audio made outside GitHub (%s), left alone' % (p['base'], len(p['stops']), p['external']))
                continue
            print('%s: %d stops, %d need audio, %d old files to remove%s' % (
                p['base'], len(p['stops']), len(p['todo']), len(p['orphans']),
                '' if p['manifest_ok'] else ', fingerprint file to update'))
        pneeded = False
        if provider == 'piper':
            pplan = preview_plan()
            pneeded = previews_needed(pplan)
            print('word previews: %d words to review%s' % (len(pplan['words']), ', needs updating' if pneeded else ', up to date'))
        flag = 'true' if (needed(plans) or pneeded) else 'false'
        print('needed=' + flag)
        if os.environ.get('GITHUB_OUTPUT'):
            with open(os.environ['GITHUB_OUTPUT'], 'a') as f:
                f.write('needed=%s\n' % flag)
                f.write('piper=%s\n' % ('true' if (flag == 'true' and provider == 'piper') else 'false'))
        return
    if provider == 'none':
        print('::warning::The voice is set to Gemini, but GEMINI_API_KEY is not set in GitHub. No audio is made.')
        return
    if provider == 'gemini':
        generate_gemini(plans)
        return
    voice = None
    for p in plans:
        if p.get('external'):
            continue
        for path in p['orphans']:
            path.unlink(); print('removed', path.name)
        failed = set(p['failed']) - set(p['todo'])
        for i in p['todo']:
            out = TURE / ('%s-%0*d.mp3' % (p['base'], p['width'], i))
            try:
                if voice is None: voice = load_voice()
                make_mp3(voice, p['stops'][i - 1], out)
                failed.discard(i)
                print('made', out.name)
            except Exception as e:          # keep going; Wayside uses the phone voice for this stop
                failed.add(i)
                if out.exists(): out.unlink()
                print('::warning::No audio for stop %d in %s: %s: %s' % (i, p['base'], type(e).__name__, e))
        (TURE / (p['base'] + '.audio.json')).write_text(
            json.dumps({'voice': p['voice_id'], 'stops': p['hashes'], 'spoken': p['spoken_hashes'], 'failed': sorted(failed)}, indent=2) + '\n', encoding='utf-8')
    pplan = preview_plan()
    if previews_needed(pplan):
        make_previews(pplan, load_voice)

if __name__ == '__main__':
    main()
