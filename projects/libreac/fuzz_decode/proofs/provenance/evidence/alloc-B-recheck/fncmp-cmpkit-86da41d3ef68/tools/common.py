"""common.py -- the inputs every script of this record shares, from the environment (tools/run.sh sets them all):
  CMPREC        the record root (holds out/ and scans/; default: the parent of this script's directory)
  CMPKIT        the cmpkit 86da41d3ef68 files AS RUN (`git archive 98e50c029045 tools/cmpkit/86da41d3ef68`; default CMPREC/kit)
  CGIF_B_PIN, CGIF_B_TWIN, DECODE_B_PIN, DECODE_B_TWIN   the four images (sha256 in RECORD.md)
The kit's file names: CMP_PY (the one compare), CLOSURE_PY (the closure), JT_PY (the table check); the record's output
names for them: CMP_OUT, CLOSURE_OUT, REPORTED (the members the closure reports), JT_OUT."""
import os

HERE = os.environ.get('CMPREC') or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KIT = os.environ.get('CMPKIT') or os.path.join(HERE, 'kit')
OUT = os.path.join(HERE, 'out')
SCANS = os.path.join(HERE, 'scans')
CMP_PY, CLOSURE_PY, JT_PY = 'strictcmp3.py', 'closure_strict3.py', 'jtcheck.py'
CMP_OUT, CLOSURE_OUT, REPORTED, JT_OUT = 'strictcmp3-cmp.out', 'closure_strict3.out', 'closure-reported.txt', 'jtcheck.out'
CGIF_B_PIN = os.environ.get('CGIF_B_PIN', '<cgif-B-pin>')
CGIF_B_TWIN = os.environ.get('CGIF_B_TWIN', '<cgif-B-twin>')
DECODE_B_PIN = os.environ.get('DECODE_B_PIN', '<decode-B-pin>')
DECODE_B_TWIN = os.environ.get('DECODE_B_TWIN', '<decode-B-twin>')


def kit_module(name):
    """import a kit file (by file name) as a module"""
    import importlib.util
    p = os.path.join(KIT, name)
    spec = importlib.util.spec_from_file_location(name[:-3], p)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def closure_globals(roots):
    """the closure script's definitions (X, Y, starts, callees, member, ycounterpart, dc, I, ...) with its own argv,
    without running its main loop"""
    import sys
    src = open(os.path.join(KIT, CLOSURE_PY)).read()
    head = src[:src.index('\ncache = {}')]
    sys.argv = [CLOSURE_PY, CGIF_B_TWIN, DECODE_B_TWIN, ','.join(roots)]
    g = {'__file__': os.path.join(KIT, CLOSURE_PY), '__name__': 'closure'}
    exec(compile(head, g['__file__'], 'exec'), g)
    return g


def jump_cases(X, Y):
    """set X.cases / Y.cases (function address -> case offsets) from every rel4 jump table this record measured:
    out/tables.tsv TABLE-REL4-JUMP rows, out/switchbound.tsv RELJUMP rows and out/fulldiff.tsv RELJUMP rows (settle.py),
    each with its entry count and the table addresses in both images"""
    import re
    sc = kit_module(CMP_PY)
    rd = lambda n: [l.rstrip('\n').split('\t') for l in list(open(os.path.join(OUT, n)))[1:]] \
        if os.path.exists(os.path.join(OUT, n)) else []
    fd = rd('fulldiff.tsv')
    faddr = {r[0]: (int(r[1], 16), int(r[2], 16)) for r in fd}
    tabs = []
    for t in rd('tables.tsv'):
        if t[2] == 'TABLE-REL4-JUMP':
            tabs.append((t[0], int(t[3], 16), int(t[4], 16), int(re.match(r'(\d+) entries', t[5]).group(1))))
    for t in rd('switchbound.tsv'):
        if t[2] == 'RELJUMP':
            tabs.append((t[0], int(t[3], 16), int(t[4], 16), int(re.match(r'(\d+) entries', t[5]).group(1))))
    for r in fd:
        if r[5] == 'RELJUMP':
            tabs.append((r[0], int(r[6], 16), int(r[7], 16), int(re.match(r'(\d+) entries', r[8]).group(1))))
    for fn, tx, ty, n in tabs:
        for img, fa, tb in ((X, faddr[fn][0], tx), (Y, faddr[fn][1], ty)):
            img.cases.setdefault(fa, set()).update(
                tb + int.from_bytes(sc.frd(img.I, tb + 4 * k, 4), 'little', signed=True) - fa for k in range(n))
    return len(tabs)
