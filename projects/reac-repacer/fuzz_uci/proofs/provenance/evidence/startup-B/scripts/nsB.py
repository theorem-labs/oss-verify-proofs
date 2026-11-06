#!/usr/bin/env python3
"""nsB.py -- module paths and record names of a generated image-B start-up file for reac-repacer/fuzz_uci's lib/B
layout (fuzz_grant B's released layout at commit 4f87de75d67: lib/B per-image + lib/Reusable shared, the layout the B
core stages port_core 0e4e065eab9f in), then the committed-header rule on its comments (hdrfix.py).

The rewrite is port_core's OWN rename_text (pg-reloc 0e4e065eab9f, imported unchanged; a Require whose modules live in
two dirs becomes two sentences on the SAME line, so line numbers stay the donor's), with --reusable-dir B
--kernel-dir Reusable, and each module's dir taken from fuzz_grant B's released tree (4f87de75d67): lib/B/<M>.v -> lib.B,
lib/Reusable/<M>.v -> lib.Reusable. A module that tree does not hold falls back to port_core's own rule (kernel_split
over core-files-Y.txt, else where the trunk lib holds it, else the donor's split). Record names: --rename TfibB=UciB
TfibSyms=UciSyms TfibB_syms=UciB_syms TfibB_ok=UciB_ok (image A's names). Numerals are never touched. Paths come from
ucib_env.py (UCIB_OVPI, UCIB_LT, UCIB_TLIB, UCIB_CB, UCIB_OLDSYMS, UCIB_PGRELOC); none is written here.

  nsB.py IN.v OUT.v [--grant-twin NAME]
     prints the modules named per dir; with --grant-twin, also compares the (dir, module) set of every Require with
     fuzz_grant B's released lib/B/NAME.v (fuzz_grant -> fuzz_uci): exit 3 on any difference.
"""
import argparse, os, re, subprocess, sys, types

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ucib_env import need  # noqa: E402
import hdrfix  # noqa: E402
PG = need('UCIB_PGRELOC')
sys.path.insert(0, PG)
import port_core as P  # noqa: E402

HUB = need('UCIB_OVPI')
GREF = '4f87de75d6772f4c4d7a147cec9da775eaade18d'
GLIB = 'proofs/libreac/fuzz_grant/lib/'
LT = need('UCIB_LT')   # local scratch: donorlib/ = `git archive 25e3d17bdb50 proofs/cgif/cgif_file_fuzzer/lib`
TMOD = 'OssFuzzTheorems.Proofs.reac_repacer.fuzz_uci.lib'
a = types.SimpleNamespace(
    src_lib=LT + '/donorlib/proofs/cgif/cgif_file_fuzzer/lib',
    src_mod='OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib',
    src_images='OssFuzzTheorems.cgif.cgif_file_fuzzer.images',
    target_lib=need('UCIB_TLIB'),
    target_mod=TMOD,
    target_images='OssFuzzTheorems.reac_repacer.fuzz_uci.images',
    reusable_dir='B', kernel_dir='Reusable',
    kit={'YK18', 'YK0j', 'YK0t', 'YK1e', 'YK1g', 'YM08', 'YM09'} | {f'YQ0{i}' for i in range(7)},
    rename=['TfibB=UciB', 'TfibSyms=UciSyms', 'TfibB_syms=UciB_syms', 'TfibB_ok=UciB_ok'],
    old_elf=need('UCIB_CB'),
    kernel_image=[],
    old_syms=need('UCIB_OLDSYMS'),
)
tree = subprocess.run(['git', '-C', HUB, 'ls-tree', '-r', '--name-only', GREF, GLIB], check=True, capture_output=True,
                      text=True).stdout.split()
tree = {p[len(GLIB):] for p in tree}
files = [l.strip() for l in open(os.path.join(PG, 'core-files-Y.txt')) if l.strip() and not l.startswith('#')]
P.DONOR_DIRS.update(d for d in ('Reusable', 'ReusableB') if os.path.isdir(os.path.join(a.src_lib, d)))
img_specific = P.kernel_split(a, files)
for f in files:
    if not f.startswith('A/'):
        P.DIRMAP[f] = a.reusable_dir if f in img_specific else a.kernel_dir
GRANT_DIR = {}
for r, _, fs in os.walk(a.src_lib):
    for fn in fs:
        rel = os.path.relpath(os.path.join(r, fn), a.src_lib)
        if fn.endswith('.v') and not rel.startswith('A/'):
            for d in ('B', 'Reusable'):
                if d + '/' + rel in tree:
                    P.DIRMAP[rel] = d
                    GRANT_DIR[rel] = d
                    break
# SHARED kernel modules (build finding of record). DUP = the modules
# grant B's release (commit 4f87de75d67) carries in BOTH lib/B and lib/Reusable (33, derived from its tree). Placement
# rule: Require X from lib.B iff the merged B core tree's lib/B/X.v exists (the core's own placement), else lib.Reusable.
#   UCIB_BCORE_LIB set (the merged core's lib dir): that rule, read from the tree.
#   not set (the B core is not readable here): the EXPECTED placement, derived from grant's tree: X is PER-IMAGE when its
#   two grant copies differ in a hex numeral (an image bound: YCbq, YCe5, YImgTop) or its grant lib/B copy Requires a
#   per-image module from lib.B (YC5d, YCbp, YE01); every other DUP module is shared and comes from lib.Reusable.
#   With UCIB_BCORE_LIB set, the derived expectation is still computed and compared with the tree's placement.
# YA0e and YA09 were held in lib.B until the B core owner's commit 09ea58a92a8 made all 125 Zify flag redefinitions of
# their relocated lib/Reusable copies Local; they now route with the rest. The --grant-twin gate maps grant's lib.B.<M>
# to lib.Reusable.<M> for exactly the routed set.
DUP = sorted(p[2:] for p in tree if p.startswith('B/') and p.endswith('.v') and 'Reusable/' + p[2:] in tree)


def _gshow(rel):
    return subprocess.run(['git', '-C', HUB, 'show', '%s:%s%s' % (GREF, GLIB, rel)], check=True, capture_output=True,
                          text=True).stdout


def _body(t):
    t = re.sub(r'\(\*.*?\*\)', '', t, flags=re.S)   # grant's copies hold no nested comment
    t = re.sub(r'From\s+\S+\s+Require(?:\s+Import|\s+Export)?\s+[\w.\'\s]+?\.(?=\s|$)', '', t)
    return [l for l in t.split('\n') if l.strip()]


_greq = re.compile(r'From\s+OssFuzzTheorems\.Proofs\.libreac\.fuzz_grant\.lib\.B\s+Require(?:\s+Import|\s+Export)?\s+'
                   r'([\w.\'\s]+?)\.(?=\s|$)')
_per, _breq = set(), {}
for rel in DUP:
    bt, rt = _gshow('B/' + rel), _gshow('Reusable/' + rel)
    if any(re.search(r'0x[0-9a-fA-F]+', l) for l in set(_body(bt)) ^ set(_body(rt))):
        _per.add(rel)
    _breq[rel] = {n + '.v' for m in _greq.finditer(bt) for n in m.group(1).split()}
_grew = True
while _grew:
    _grew = False
    for rel in DUP:
        if rel not in _per and _breq[rel] & _per:
            _per.add(rel)
            _grew = True
EXPECTED = sorted(_per)
BCORE = os.environ.get('UCIB_BCORE_LIB')
if BCORE:
    PER_IMAGE = sorted(rel for rel in DUP if os.path.exists(os.path.join(BCORE, 'B', rel)))
    PLACEMENT = 'placement read from the merged B core tree (equals the placement derived from grant B: %s)' % (
        PER_IMAGE == EXPECTED)
else:
    PER_IMAGE = EXPECTED
    PLACEMENT = 'EXPECTED placement derived from grant B (the B core tree is not readable here)'
SHARED = [rel for rel in DUP if rel not in PER_IMAGE]
for rel in SHARED:
    P.DIRMAP[rel] = 'Reusable'
    GRANT_DIR[rel] = 'Reusable'
SHARED_NAMES = {rel[:-2].replace('/', '.') for rel in SHARED}

REQ = re.compile(r'From (OssFuzzTheorems\.Proofs\.(?:reac_repacer\.fuzz_uci|libreac\.fuzz_grant)\.lib)\.(\w+) '
                 r'Require(?:\s+Import|\s+Export)?\s+([\w.\'\s]+?)\.(?=\s|$)')


def pairs(t):
    return sorted({(m.group(2), n) for m in REQ.finditer(t) for n in m.group(3).split()})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('src'); ap.add_argument('dst'); ap.add_argument('--grant-twin')
    o = ap.parse_args()
    t = P.rename_text(open(o.src).read(), a)
    t, nfix = hdrfix.fix(t)
    code = '\n'.join(l for l in t.split('\n') if not l.lstrip().startswith('(*'))
    assert 'cgif' not in code, 'a cgif path survives outside comments'
    open(o.dst, 'w').write(t)
    where = {}
    for d, n in pairs(t):
        where.setdefault(d, []).append(n)
    print('nsB %s: %s; header rule: %d comment rewrites' % (os.path.basename(o.dst), '; '.join(
        'lib.%s: %s' % (d, ' '.join(ms)) for d, ms in sorted(where.items())), nfix))
    nogrant = sorted(n for d, n in pairs(t) if n.replace('.', '/') + '.v' not in GRANT_DIR)
    if nogrant:
        print('nsB %s: modules fuzz_grant B does not hold (port_core rule): %s' % (os.path.basename(o.dst), nogrant))
    if o.grant_twin:
        g = subprocess.run(['git', '-C', HUB, 'show', '%s:%sB/%s.v' % (GREF, GLIB, o.grant_twin)], check=True,
                           capture_output=True, text=True).stdout
        mine = set(pairs(t))
        theirs = {('Reusable' if (d == 'B' and n in SHARED_NAMES) else d, n) for d, n in pairs(g)}
        if mine != theirs:
            print('nsB %s: Require (dir, module) set DIFFERS from fuzz_grant B lib/B/%s.v at %s: only here %s; only '
                  'there %s' % (os.path.basename(o.dst), o.grant_twin, GREF[:11], sorted(mine - theirs),
                                sorted(theirs - mine)))
            sys.exit(3)
        moved = sorted(n for d, n in mine if d == 'Reusable' and n in SHARED_NAMES)
        print('nsB %s: Require (dir, module) set EQUAL to fuzz_grant B lib/B/%s.v at %s (%d modules); SHARED duplicate '
              'set derived from grant B: %d modules (%s): %d per-image stay lib.B (%s), 0 held, %d routed to '
              'lib.Reusable; this file Requires from lib.Reusable by that rule: %s'
              % (os.path.basename(o.dst), o.grant_twin, GREF[:11], len(mine), len(DUP), PLACEMENT, len(PER_IMAGE),
                 ' '.join(r[:-2] for r in PER_IMAGE), len(SHARED), ' '.join(moved) or '-'))


if __name__ == '__main__':
    main()
