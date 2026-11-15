#!/usr/bin/env python3
"""Makes Danish audio (mp3) for every stop in every route in ture/*.gpx.

  python tools/make_audio.py --plan   shows what needs new audio (needs only Python)
  python tools/make_audio.py          makes the audio (needs piper-tts, ffmpeg and the voice in VOICE_DIR)

Files per route <name>.gpx:
  ture/<name>-01.mp3, -02.mp3 ...   one file per stop, in the order of the stops
  ture/<name>.audio.json            a fingerprint of the text behind each file
Wayside only plays a file when its fingerprint matches the current text of the stop,
so an edited stop never plays old audio.
"""
import json, os, re, subprocess, sys, wave
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

def num(n):
    if n < 100: return below100(n)
    if n < 1000:
        h, r = divmod(n, 100)
        head = 'hundrede' if h == 1 else UNITS[h] + ' hundrede'
        return head if r == 0 else head + ' og ' + below100(r)
    th, r = divmod(n, 1000)
    head = 'tusind' if th == 1 else UNITS[th] + ' tusind'
    return head if r == 0 else head + ' og ' + num(r)

def year(n):
    if 1100 <= n < 2000:
        h, r = divmod(n, 100)
        head = TEENS[h] + ' hundrede'
        return head if r == 0 else head + ' og ' + below100(r)
    return num(n)

def normalize(t):
    t = t.replace('365discount', 'tre seks fem discount').replace("2020'erne", 'tyvetyverne')
    t = re.sub(r'\b(1[1-9]\d{2}|20\d{2})\b', lambda m: year(int(m.group(1))), t)
    t = re.sub(r'\b(\d+),(\d+)\b', lambda m: num(int(m.group(1))) + ' komma ' + ' '.join(UNITS[int(c)] for c in m.group(2)), t)
    t = re.sub(r'\b\d+\b', lambda m: num(int(m.group(0))), t)
    return t

# ---------- reading the stops (same rules as Wayside) ----------
def clean(s):
    return re.sub(r'\s+', ' ', s or '').strip()

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

def read_stops(gpx):
    root = ET.parse(gpx).getroot()
    out = []
    for el in root.iter():
        if el.tag.split('}')[-1].lower() != 'wpt': continue
        try:
            float(el.get('lat')); float(el.get('lon'))
        except (TypeError, ValueError):
            continue
        name = child_text(el, ['name']) or 'Stop %d' % (len(out) + 1)
        desc = child_text(el, ['desc', 'cmt'])
        out.append(name + ('. ' + desc if desc else ''))
    return out

# ---------- planning ----------
def plan_route(gpx):
    base = gpx.stem
    stops = read_stops(gpx)
    hashes = [fnv1a(s) for s in stops]
    width = max(2, len(str(len(stops))))
    man_path = TURE / (base + '.audio.json')
    try:
        man = json.loads(man_path.read_text(encoding='utf-8'))
    except Exception:
        man = {}
    same_voice = man.get('voice') == VOICE_ID
    old = man.get('stops', []) if same_voice else []
    todo = []
    for i, h in enumerate(hashes, 1):
        mp3 = TURE / ('%s-%0*d.mp3' % (base, width, i))
        if not (i <= len(old) and old[i - 1] == h and mp3.exists()):
            todo.append(i)
    pat = re.compile('^' + re.escape(base) + r'-(\d+)\.mp3$')
    orphans = [p for p in TURE.iterdir() if (m := pat.match(p.name)) and int(m.group(1)) > len(stops)]
    manifest_ok = same_voice and man.get('stops') == hashes
    return dict(base=base, stops=stops, hashes=hashes, width=width, todo=todo, orphans=orphans, manifest_ok=manifest_ok)

def all_plans():
    return [plan_route(g) for g in sorted(TURE.glob('*.gpx')) if read_stops(g)]

def needed(plans):
    return any(p['todo'] or p['orphans'] or not p['manifest_ok'] for p in plans)

# ---------- making audio ----------
def load_voice():
    from piper import PiperVoice
    vdir = Path(os.environ.get('VOICE_DIR', ROOT / '.voice'))
    onnx = next(vdir.glob('*.onnx'))
    return PiperVoice.load(str(onnx), config_path=str(onnx) + '.json')

def make_mp3(voice, text, out_mp3):
    wav_path = str(out_mp3) + '.wav'
    with wave.open(wav_path, 'wb') as w:
        voice.synthesize_wav(normalize(text), w)
    subprocess.run(['ffmpeg', '-y', '-loglevel', 'error', '-i', wav_path,
                    '-af', 'loudnorm=I=-16:TP=-1.5:LRA=11,apad=pad_dur=0.4',
                    '-ac', '1', '-ar', '22050', '-b:a', '64k', str(out_mp3)], check=True)
    os.remove(wav_path)

def main():
    plans = all_plans()
    if '--plan' in sys.argv:
        for p in plans:
            print('%s: %d stops, %d need audio, %d old files to remove%s' % (
                p['base'], len(p['stops']), len(p['todo']), len(p['orphans']),
                '' if p['manifest_ok'] else ', fingerprint file to update'))
        flag = 'true' if needed(plans) else 'false'
        print('needed=' + flag)
        if os.environ.get('GITHUB_OUTPUT'):
            with open(os.environ['GITHUB_OUTPUT'], 'a') as f:
                f.write('needed=%s\n' % flag)
        return
    voice = None
    for p in plans:
        for path in p['orphans']:
            path.unlink(); print('removed', path.name)
        for i in p['todo']:
            if voice is None: voice = load_voice()
            out = TURE / ('%s-%0*d.mp3' % (p['base'], p['width'], i))
            make_mp3(voice, p['stops'][i - 1], out)
            print('made', out.name)
        (TURE / (p['base'] + '.audio.json')).write_text(
            json.dumps({'voice': VOICE_ID, 'stops': p['hashes']}, indent=2) + '\n', encoding='utf-8')

if __name__ == '__main__':
    main()
