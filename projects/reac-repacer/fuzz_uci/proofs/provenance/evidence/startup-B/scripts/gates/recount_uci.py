#!/usr/bin/env python3
"""Deterministic re-count of the start-up gate numbers cited in the commit (VERIFY: exhaustive counts by a command).
Reads the collected hand-off files only (no regeneration)."""
import re, hashlib, glob

import os
G = os.environ['UCIB_GATEWORK'].rstrip('/') + '/'
IMG = {
    'cgifB-control': dict(f=G + 'in/cgif/YB01.v', main=0x80020, desc=(0xa2ae0, 0xc0), cf=0x137da8),
    'uciB': dict(f=G + 'in/gen/YB01.v', main=0x7ee48, desc=(0x9b9d0, 0x40), cf=0x130c28),
}
KW = re.compile(r'KWord \{\| a_base := ELit 0; a_off := (\d+) \|\} (\d+) \(ELit (\d+)\)')
KF = re.compile(r'KFill \{\| a_base := ELit 0; a_off := (\d+) \|\} \(ELit (\d+)\) (\d+)')


def byte_at(facts, addr):
    """value of the byte at addr from KWord / KFill facts (little endian); None if no such fact."""
    for a, w, v in facts['kw']:
        if a <= addr < a + w:
            return (v >> (8 * (addr - a))) & 0xff
    for a, n, v in facts['kf']:
        if a <= addr < a + n:
            return v
    return None


for img, d in IMG.items():
    t = open(d['f']).read()
    heads = [(m.start(), m.group(1)) for m in re.finditer(r'^Definition (\S+)', t, re.M)]
    defs = {}
    for i, (pos, name) in enumerate(heads):
        end = heads[i + 1][0] if i + 1 < len(heads) else len(t)
        chunk = t[pos:end]
        body = chunk[chunk.find(':=') + 2:].strip()
        defs[name] = body
    st = {n: b for n, b in defs.items() if re.fullmatch(r'HS_tfib_\d+', n)}
    kn = {n: b for n, b in defs.items() if re.fullmatch(r'HS_tfib_\d+_kn', n)}
    alias = [n for n, b in list(st.items()) + list(kn.items()) if re.fullmatch(r'HS_tfib_\d+(_kn)?\s*\.', b)]

    def ndup(ds):
        h = {}
        for n, b in ds.items():
            h.setdefault(hashlib.sha256(b.encode()).hexdigest(), []).append(n)
        return sum(len(v) - 1 for v in h.values() if len(v) > 1)

    ss = sorted(set(re.findall(r'SS (\d+)', t)))
    lo, ln = d['desc']
    slo = 0x7fff8000 + lo // 8
    print(img, 'states', len(st), 'kn lists', len(kn), 'aliases', len(alias),
          'duplicate state bodies', ndup(st), 'duplicate kn bodies', ndup(kn),
          'arrival SS values', ss, 'all == main %#x' % d['main'], ss == [str(d['main'])])
    # per kn list: the cells the gates name
    def facts_of(name, seen):
        """KWord / KFill facts of a definition, following the definitions its body names (seg, HS_tfib_N_kn ...)."""
        if name in seen or name not in defs:
            return [], []
        seen.add(name)
        b = defs[name]
        kw = [(int(a), int(w), int(v)) for a, w, v in KW.findall(b)]
        kf = [(int(a), int(c), int(v)) for a, c, v in KF.findall(b)]
        for r in set(re.findall(r'\b(seg\w*|HS_tfib_\d+_kn)\b', b)):
            k2, f2 = facts_of(r, seen)
            kw += k2
            kf += f2
        return kw, kf

    rows = []
    for n in sorted(kn, key=lambda s: int(re.search(r'\d+', s).group())):
        kw, kf = facts_of(n, set())
        facts = dict(kw=kw, kf=kf)
        mcs = byte_at(facts, d['cf'] + 36)
        lsan = byte_at(facts, d['cf'] + 0x4a)
        shadow = {byte_at(facts, slo + k) for k in range(ln // 8)}
        rows.append((n, mcs, lsan, shadow))
    print(img, 'malloc_context_size (cf+36) per kn list:', sorted({r[1] for r in rows}, key=str),
          '| cf+0x4a:', sorted({r[2] for r in rows}, key=str),
          '| descriptor-array shadow values:', sorted(set().union(*[r[3] for r in rows]), key=str),
          '| lists checked', len(rows))
    print(img, 'literal 1531 in AB01:', len(re.findall(r'\b1531\b', t)))
for k in ('in/gen',):
    fs = glob.glob(G + k + '/*.v')
    n = sum(len(re.findall(r'^(?!\(\*).*\bTfib(Syms|B|B_syms|B_ok)\b', open(p).read(), re.M)) for p in fs)
    print(k, 'generated .v files', len(fs), 'cgif record names left (outside comments)', n)
