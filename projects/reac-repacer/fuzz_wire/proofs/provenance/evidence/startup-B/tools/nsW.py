#!/usr/bin/env python3
"""nsW.py -- module paths and record names of a generated image-B start-up file for reac-repacer/fuzz_wire's lib/B
layout (fuzz_grant B's released layout at recipes commit 4f87de75d67: lib/B per image + lib/Reusable shared), and the
header rule: a Theorem Labs modification notice keeps its head as the file holds it, dated (`(* Modified by Theorem
Labs, YYYY-MM: `) or not; this writer undates nothing and counts the dated heads.

The module rewrite is port_core's OWN rename_text (pg-reloc 0e4e065eab9f, imported unchanged; a Require whose modules
live in two dirs becomes two sentences on the SAME line, so line numbers stay the donor's), with --reusable-dir B
--kernel-dir Reusable, and each module's dir taken from fuzz_grant B's released tree (4f87de75d67): lib/B/<M>.v -> lib.B,
lib/Reusable/<M>.v -> lib.Reusable. A module that tree does not hold falls back to port_core's own rule (kernel_split
over core-files-Y.txt, else where the trunk lib holds it, else the donor's split). Record names (image A's, confirmed):
TfibB=WireB TfibSyms=WireSyms TfibB_syms=WireB_syms TfibB_ok=WireB_ok, over the CODE text only (rename_code, below);
no shape rename (the trunk names checksum_shape). Numerals are never touched. Paths come from the environment
(env.sh): LT (local scratch holding the donor lib export), TR (the trunk
clone), CB (the donor image), HUB (the git hub), OLD_SYMS (the donor image's symbol recovery cache 978e0a064c5a4c6e).

  nsW.py IN.v OUT.v [--grant-twin NAME]
     prints the modules named per dir; with --grant-twin, also compares the (dir, module) set of every Require with
     fuzz_grant B's released lib/B/NAME.v (fuzz_grant -> fuzz_wire): exit 3 on any difference.
Fail-closed: --grant-twin must be a module name (Y + 3 letters or digits), and the text nsW would write (IN.v's copied
header and comments included) passes textguard.py first; either refusal is exit 2 with nothing written.
"""
import argparse, os, re, subprocess, sys, types

sys.dont_write_bytecode = True
PG = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'pg-reloc', '0e4e065eab9f')
sys.path.insert(0, PG)
# the refusal check beside this file (tools/textguard.py), else the lane's (a copy of nsW.py run from another directory,
# e.g. the gate runner's lanetools/, reads it from $W/tools); without it nsW does not run
for _d in (os.path.dirname(os.path.abspath(__file__)), os.path.join(os.environ.get('W', ''), 'tools')):
    if os.path.isfile(os.path.join(_d, 'textguard.py')):
        sys.path.insert(0, _d)
        break
import textguard  # noqa: E402
import port_core as P  # noqa: E402

HUB = os.environ['HUB']
GREF = '4f87de75d6772f4c4d7a147cec9da775eaade18d'
GLIB = 'proofs/libreac/fuzz_grant/lib/'
LT = os.environ['LT']
TMOD = 'OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib'
OLD_SYMS = os.environ['OLD_SYMS']
a = types.SimpleNamespace(
    src_lib=LT + '/donorlib/proofs/cgif/cgif_file_fuzzer/lib',
    src_mod='OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib',
    src_images='OssFuzzTheorems.cgif.cgif_file_fuzzer.images',
    target_lib=os.environ['TR'] + '/projects/reac-repacer/fuzz_wire/proofs/lib',
    target_mod=TMOD,
    target_images='OssFuzzTheorems.reac_repacer.fuzz_wire.images',
    reusable_dir='B', kernel_dir='Reusable',
    kit={'YK18', 'YK0j', 'YK0t', 'YK1e', 'YK1g', 'YM08', 'YM09'} | {f'YQ0{i}' for i in range(7)},
    rename=['TfibB=WireB', 'TfibSyms=WireSyms', 'TfibB_syms=WireB_syms', 'TfibB_ok=WireB_ok'],
    old_elf=os.environ['CB'],
    kernel_image=[],
    old_syms=OLD_SYMS,
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
# Placement rule (the B core owner's): Require X from lib.B if the unit's merged tree holds lib/B/X.v (the B core's own
# placement), else from lib.Reusable. fuzz_wire's B core does not exist yet, so the EXPECTED placement is used: of the
# modules grant B at 4f87de75d67 carries in BOTH lib/B and lib/Reusable (DUP, derived from the tree), the per-image ones
# stay lib/B (YCbq / YCe5 hold the image end, YC5d / YCbp / YE01 Require YCbq, YImgTop holds IMG_LO / IMG_TOP: lib/Reusable
# holds image A's copies) and the rest are SHARED (one copy, in lib/Reusable). Once lib/B exists in $TR with core files,
# its own placement replaces the expected list. ZIFY-HELD: YA0e and YA09 stay lib/B while the unit's shared lib/Reusable
# copies set a Zify flag globally (grant's lib/B copies use `Local Ltac`); they route with the rest once the shared copy
# the core keeps (read at commit $SHARED_REF, proofs/reac-repacer/fuzz_wire/lib/Reusable/<X>.v) has every
# `Ltac <name> ::=` site Local. Without $SHARED_REF both stay held.
DUP = {p[2:-2].replace('/', '.') for p in tree if p.startswith('B/') and p.endswith('.v') and 'Reusable/' + p[2:] in tree}
_tb = os.path.join(a.target_lib, 'B')
OURS = {'YB01', 'YB03', 'YB05', 'YB12', 'YB13', 'YB1h', 'YB1k', 'YB1l', 'YB1m', 'YB1v', 'YCej', 'YD1k', 'YD1y', 'YD2i',
        'YD2j', 'YE23', 'YE37', 'YE3i', 'YF0m'}   # this lane's 19 files are not the core's placement
_core = ({f[:-2] for f in os.listdir(_tb) if f.endswith('.v')} - OURS) if os.path.isdir(_tb) else set()
PER_IMAGE = ({x for x in DUP if x in _core} if _core else {'YCbq', 'YCe5', 'YC5d', 'YCbp', 'YE01', 'YImgTop'})
PLACEMENT = 'the B core tree' if _core else 'EXPECTED (no B core yet)'
SHARED_ALL = DUP - PER_IMAGE
SHARED_REF = os.environ.get('SHARED_REF')
ZIFY_SITE = re.compile(r'(Local\s+|Global\s+|#\[\s*\w+\s*\]\s*)?Ltac\s+[\w.]+\s*::=')
HELD, HELD_WHY = set(), {}
for _x in ('YA0e', 'YA09'):
    _src = None
    if SHARED_REF:
        _r = subprocess.run(['git', '-C', HUB, 'show', '%s:proofs/reac-repacer/fuzz_wire/lib/Reusable/%s.v' % (SHARED_REF, _x)],
                            capture_output=True, text=True)
        _src = _r.stdout if _r.returncode == 0 else None
    _sites = ZIFY_SITE.findall(_src) if _src is not None else None
    _glob = None if _sites is None else sum(1 for s in _sites if not s.strip().startswith('Local'))
    if _sites is None or _glob:
        HELD.add(_x)
    HELD_WHY[_x] = ('no shared copy read (SHARED_REF unset or path absent)' if _sites is None else
                    '%d Ltac ::= sites, %d not Local at %s' % (len(_sites), _glob, SHARED_REF[:12]))
SHARED_KERNEL = SHARED_ALL - HELD
GRANT_DIR = {}
for r, _, fs in os.walk(a.src_lib):
    for fn in fs:
        rel = os.path.relpath(os.path.join(r, fn), a.src_lib)
        if fn.endswith('.v') and not rel.startswith('A/'):
            for d in ('B', 'Reusable'):
                if d + '/' + rel in tree:
                    # a SHARED module (both lib/B and lib/Reusable in grant B): the core keeps one copy, in lib/Reusable,
                    # which the B core and image A Require; a lib/B duplicate would make a second copy of the same types
                    if rel[:-2].replace('/', '.') in SHARED_KERNEL and 'Reusable/' + rel in tree:
                        d = 'Reusable'
                    P.DIRMAP[rel] = d
                    GRANT_DIR[rel] = d
                    break

REQ = re.compile(r'From (OssFuzzTheorems\.Proofs\.(?:reac_repacer\.fuzz_wire|libreac\.fuzz_grant)\.lib)\.(\w+) '
                 r'Require(?:\s+Import|\s+Export)?\s+([\w.\'\s]+?)\.(?=\s|$)')
DATED = re.compile(r'\(\* Modified by Theorem Labs' + r', \d{4}-\d{2}(?:-\d{2})?:')
# The header rule: every notice head stays as the file holds it. The 19 files carry the dated head
# `(* Modified by Theorem Labs, YYYY-MM: ` (the date form of the publish scrub's comment pass, and the rule of the
# start-up set's own writers: a notice a tool writes keeps its month, an inherited one its date; docs/adding-a-proof.md
# requirement 7), and af0m writes the sha256 of the text it emits into lib/Reusable/DepotCfg.v, so this writer must be
# a byte identity on the committed text of every file. Undating a head here would undo the scrub's dated head.


def pairs(t):
    return sorted({(m.group(2), n) for m in REQ.finditer(t) for n in m.group(3).split()})


# The record renames are applied to the CODE text only, through port_core's own code_sub. A comment may state the
# rename MAPPING itself, and renaming its left side destroys it: the donor-namespace provenance notice
# `names TfibSyms -> WireSyms` (YF0m.v:4) had become `names WireSyms -> WireSyms`. So port_core's rename_text runs
# with an EMPTY rename list, and rename_idents' own rule (the whole identifier, or OLD as a whole `_`-separated part
# of a longer one) is applied outside Coq comments afterwards. A comment that names a renamed record in running text
# keeps the donor name, as the donor wrote it; the record names a comment STATES are provenance, not code.
NO_RENAME = types.SimpleNamespace(**dict(vars(a), rename=[]))
RENAME = dict(r.split('=', 1) for r in a.rename)
RENAME_PART = P.part_rx(RENAME)


def rename_code(t):
    def one(m):
        w = m.group(0)
        return RENAME[w] if w in RENAME else RENAME_PART.sub(lambda p: RENAME[p.group(1)], w)
    return P.code_sub(P.IDENT, one, t)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('src'); ap.add_argument('dst'); ap.add_argument('--grant-twin')
    o = ap.parse_args()
    if o.grant_twin is not None and not re.fullmatch(r'Y[0-9A-Za-z]{3}', o.grant_twin):
        sys.stderr.write('nsW: --grant-twin %r is not a module name (Y + 3 letters or digits): refused, nothing '
                         'written\n' % o.grant_twin[:60])
        sys.exit(2)
    t = rename_code(P.rename_text(open(o.src).read(), NO_RENAME))
    nd = len(DATED.findall(t))
    code = '\n'.join(l for l in t.split('\n') if not l.lstrip().startswith('(*'))
    assert 'cgif' not in code, 'a cgif path survives outside comments'
    textguard.refuse(t, o.dst)
    open(o.dst, 'w').write(t)
    where = {}
    for d, n in pairs(t):
        where.setdefault(d, []).append(n)
    print('nsW %s: %s; dated notices %s: %d; placement %s: %d grant B duplicates = %d per-image (lib.B: %s) + %d '
          'SHARED, %d routed to lib.Reusable (held in lib.B: %s; Zify check: %s)' % (
              os.path.basename(o.dst), '; '.join('lib.%s: %s' % (d, ' '.join(ms)) for d, ms in sorted(where.items())),
              'kept', nd,
              PLACEMENT, len(DUP), len(PER_IMAGE), sorted(PER_IMAGE), len(SHARED_ALL), len(SHARED_KERNEL), sorted(HELD),
              '; '.join('%s %s' % kv for kv in sorted(HELD_WHY.items()))))
    nogrant = sorted(n for d, n in pairs(t) if n.replace('.', '/') + '.v' not in GRANT_DIR)
    if nogrant:
        print('nsW %s: modules fuzz_grant B does not hold (port_core rule): %s' % (os.path.basename(o.dst), nogrant))
    if o.grant_twin:
        g = subprocess.run(['git', '-C', HUB, 'show', '%s:%sB/%s.v' % (GREF, GLIB, o.grant_twin)], check=True,
                           capture_output=True, text=True).stdout
        theirs0 = set(pairs(g))
        # grant B's twin Requires the shared kernel from lib.B; the unit takes it from lib.Reusable (SHARED_KERNEL)
        theirs = {('Reusable', n) if d == 'B' and n in SHARED_KERNEL else (d, n) for d, n in theirs0}
        mine = set(pairs(t))
        moved = sorted(n for d, n in theirs0 if d == 'B' and n in SHARED_KERNEL)
        if mine != theirs:
            print('nsW %s: Require (dir, module) set DIFFERS from fuzz_grant B lib/B/%s.v at %s (shared kernel mapped to '
                  'lib.Reusable): only here %s; only there %s' % (os.path.basename(o.dst), o.grant_twin, GREF[:11],
                                                                 sorted(mine - theirs), sorted(theirs - mine)))
            sys.exit(3)
        print('nsW %s: Require (dir, module) set EQUAL to fuzz_grant B lib/B/%s.v at %s (%d modules; shared kernel taken '
              'from lib.Reusable: %s)' % (os.path.basename(o.dst), o.grant_twin, GREF[:11], len(mine), moved or 'none'))


if __name__ == '__main__':
    main()
