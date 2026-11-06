#!/usr/bin/env python3
"""emit_col.py PLAN CGIF_AB1M HEADER_RULE OUT -- lib/A/AB05.v and AB1m.v of reac-repacer/fuzz_wire's image-A start-up layer.

DATA files (start-up facts); rule 24: this script proves no function. fuzz_uci's emit_col.py, not in the published tree,
with fuzz_wire's inputs:
  AB05.v  the collector's plan (cgif's A/AB05.v at origin/ossv/recipes 25e3d17bdb50, relocated onto fuzz_wire.asan, ranges
          and tail remade), PLAN pinned by sha256, minus its first line (the donor workspace's SCRATCH marker)
  AB1m.v  cgif's A/AB1m.v at 25e3d17bdb50 (CGIF_AB1M, pinned), unchanged but for module paths: the donor's checker on
          fuzz_wire's own states, plan and table returns cgif's startup_shape.
Module paths go to fuzz_wire's split library (lib.A / lib.ZReplyA -> lib.A, the lib root -> lib.Reusable, cgif's images ->
fuzz_wire's); the donor's header lines 1-3 stay byte for byte and NO line of ours is added (a lane script is not a tool
of record; the provenance is this script, its pins and the patch record). HEADER_RULE is unused (kept as an argument).
"""
import hashlib, os, re, subprocess, sys

PINS = {'AB05': '5c9f4ce94c54a927eb9f013e996cab888c6ff5796606d4fe114a9f6200c31b6b',
        'AB1m': 'f909bf41fb04e72d878b5944df954182a8cad296e4265c1b674d021af6455132'}
LIB_RX = re.compile(r'OssFuzzTheorems\.Proofs\.cgif\.cgif_file_fuzzer\.lib(?:\.(ZReplyA|A))?(?![\w.])')
IMG_RX = re.compile(r'OssFuzzTheorems\.cgif\.cgif_file_fuzzer\.images(?![\w])')


def map_modules(text):
    text, a = LIB_RX.subn(lambda m: 'OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib.'
                          + ('A' if m.group(1) else 'Reusable'), text)
    text, b = IMG_RX.subn('OssFuzzTheorems.reac_repacer.fuzz_wire.images', text)
    return text, a + b


def strip_comments(t):
    out, d, i = [], 0, 0
    while i < len(t):
        if t.startswith('(*', i):
            d += 1; i += 2; continue
        if d and t.startswith('*)', i):
            d -= 1; i += 2; continue
        if d == 0:
            out.append(t[i])
        i += 1
    return ''.join(out)


HOST_DIRS = ('home', 'mnt', 'tmp', 'dev/shm')  # top-level host directories a record must not name
DIRTY = re.compile(r'\bh-[a-z]+-[a-z0-9]+\b|\bcold/(?=[A-Za-z0-9])|/(?:%s)/' % '|'.join(HOST_DIRS))  # lane / worker / branch / host text


def emit(name, raw):
    lines = raw.decode().splitlines(keepends=True)
    dropped = 0
    if name == 'AB05':
        if not lines[0].startswith('(* SCRATCH input of '):
            sys.exit('emit_col: FAIL AB05 line 1 is not the SCRATCH marker')
        lines, dropped = lines[1:], 1
    # fail closed on COPIED text: every line this writer copies (the donor's header lines and the body) must carry no
    # lane / worker name, working branch or host path; checked before the pin, so a dirty input is refused as such
    bad = [(i + 1 + dropped, m.group(0)) for i, l in enumerate(lines) for m in [DIRTY.search(l)] if m]
    if bad:
        sys.exit('emit_col: REFUSED %s: copied text carries lane / branch / host text at input line(s) %s; nothing written'
                 % (name, ', '.join('%d (%s)' % b for b in bad[:5])))
    h = hashlib.sha256(raw).hexdigest()
    if h != PINS[name]:
        sys.exit('emit_col: FAIL pin %s: have %s' % (name, h))
    print('emit_col: pin ok %s %s' % (name, h))
    if not (lines[0].startswith('(* Copyright ') and lines[1].startswith('(* SPDX-License-Identifier: ')
            and lines[2].startswith('(* Modified by Theorem Labs')):
        sys.exit('emit_col: FAIL %s lines 1-3 are not Copyright / SPDX / Modified by' % name)
    body, n = map_modules(''.join(lines[3:]))
    left = len(re.findall(r'\bcgif|ZReplyA', strip_comments(body)))
    if n == 0 or left:
        sys.exit('emit_col: FAIL %s: %d paths mapped, %d cgif / ZReplyA names left' % (name, n, left))
    print('emit_col: gate module-map %s PASS (%d paths mapped, 0 cgif / ZReplyA names left outside comments)' % (name, n))
    new = ''.join(lines[:3]) + body      # the donor's lines 1-3 byte for byte; no line of ours (a lane script writes no notice)
    nd = len(raw.decode().splitlines())
    if len(new.splitlines()) != nd - dropped:
        sys.exit('emit_col: FAIL %s line count' % name)
    print('emit_col: gate shape %s PASS (lines 1-3 the donor\'s, byte for byte; no own line; %d lines = donor %d - %d)'
          % (name, len(new.splitlines()), nd, dropped))
    return new


def main():
    plan, ab1m, hr, out = sys.argv[1:5]
    news = [(name, emit(name, open(p, 'rb').read())) for name, p in (('AB05', plan), ('AB1m', ab1m))]
    os.makedirs(out, exist_ok=True)      # nothing is written unless both files pass every gate
    outs = []
    for name, new in news:
        o = os.path.join(out, name + '.v')
        open(o, 'w').write(new)
        outs.append((o, new))
    for o, new in outs:
        print('emit_col: wrote %s sha256 %s' % (os.path.basename(o), hashlib.sha256(new.encode()).hexdigest()))
    print('emit_col: ALL GATES PASS')


if __name__ == '__main__':
    main()
