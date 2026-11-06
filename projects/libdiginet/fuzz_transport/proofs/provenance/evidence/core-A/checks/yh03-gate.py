#!/usr/bin/env python3
"""yh03-gate.py WORK LIB OUT -- gate (e) of the libdiginet/fuzz_transport image-A core relocation (pool row TCA):
yh03check fb3bfbc1eea8 (v6.4, the version of record; + yh03regen 1254e5c96a44) on the unit's two YH03 files, each run
with --pinned (v6.4 refuses a run without it), with a planted row on each side, the unit identity, the pairing and
COPIED; then the cells the registry says v6.4 does not judge (its KNOWN LIMIT: the cells it lists as `not checked by any
rule`; its KNOWN GAP: NOSYM D cells), each read against the pin's twin by content. libdiginet/fuzz_decode's gate of
record checks/yh03-gate.py (sha256 50a3e05f26b4; internal record) with the unit, the pins, the paths and the tool
version changed.

  WORK    the relocation run dir (run.sh's WORK): its stage-out is searched for YH03-style files (a `Definition
          src0_A_ / src0_E_ / src0_D_ / ubs0_...` cell); each one found is listed as UNDECIDED (exit 1)
  LIB     the unit's lib (proofs/libdiginet/fuzz_transport/lib): LIB/Reusable/YH03.v (plain) and LIB/U/Reusable/YH03.v
          (ubsan) are checked. The gate reads LIB through a scratch checkout OUT/work/yh03/wt whose
          proofs/libdiginet/fuzz_transport/lib is a symlink to LIB (nothing is written under LIB)
  OUT     OUT/work/yh03/: one <case>.rows / <case>.err per run, the planted copies and the scratch checkout;
          OUT/records/yh03check.txt: the record (every result line and the rows of the two base runs)
Environment (defaults in brackets; no host path is written here):
  TIMG      fuzz_transport's image dir: stripped/fuzz_transport.{plain,ubsan} (the pins bb20ce415827 / af7b86991906)
            and unstripped/fuzz_transport.{plain,ubsan} (their twins) [required]
  HUB       the hub repository [required]
  YH03CHECK a directory holding yh03check.py fb3bfbc1eea8 and the yh03regen.py 1254e5c96a44 it imports
            [OUT/tools/yh03check/fb3bfbc1eea8, extracted from the hub HUB at TOOLS_REF when absent]
  PINS      the harness.yaml that pins the two builds [a stand-in OUT/work/yh03/wt/projects/libdiginet/fuzz_transport/
            harness.yaml written by this gate with the sha256 of TIMG's two stripped pins: the released harness.yaml
            (recipes) pins the OLD images, and no ref of the hub pins the new ones yet; give the harness of record when it
            exists]
Cases: base-<side> (the unit's file on its twin, --pinned, --pins), plant-<side> (a copy with src0_A_main moved by +4:
exactly one row must change, main OK -> BAD, and `rows not OK` by exactly +1), ident-<side> (--other-side, --proofs:
COPIED), mixed (the ubsan file on the plain twin with the plain pin: refused by the pairing, rc 2), and hand-<side>: each
NOSYM D cell and each `not checked by any rule` cell of base-<side> decided by content: D_const_<N>_0x<H> holds 0x<H>
(8 bytes); D_got_<s> holds the address of the symbol __<s> / <s>; D_debruijn32 is a permutation of 0..31 that is the
table of a de Bruijn ctz for the multiplier it encodes (read back from the table, then checked for all 32 indices); a D
cell whose annotation is <symbol>+0x0 and whose symbol name ends with the cell's name (without D_ and the donor's
symbol prefix, which the gate reads from the input: the first word of the cell YH03.v defines on its line 44) names
that symbol; src0_vmlock is None exactly when the twin has no vmlock symbol. Each content rule is controlled on a moved
address (a D_const cell + 8, the table + 1): it must refuse.
A released YH03 file carries rows no proof reads, by design; the control is the planted row, not a zero count.
Exit 0 when every pin holds and every control answers as above, 1 otherwise, 2 on a bad input.
rule: proves no function (kind: measurement). yh03regen.py --write is never run."""
import hashlib
import os
import re
import shutil
import subprocess
import sys


def refuse(msg):
    print(f'yh03-gate: REFUSED: {msg}', file=sys.stderr)
    sys.exit(2)


if len(sys.argv) != 4:
    refuse('usage: yh03-gate.py WORK LIB OUT')
RUN, LIB, OUT = (os.path.abspath(a) for a in sys.argv[1:4])
HUB = os.environ.get('HUB') or refuse('set HUB to the hub repository')
TOOLS_REF = os.environ.get('TOOLS_REF', '91ef630666824d85906ae28a461aec2ae1e9653d')
P = os.environ.get('TIMG') or refuse('set TIMG to the fuzz_transport image dir')
W = f'{OUT}/work/yh03'
os.makedirs(W, exist_ok=True)
os.makedirs(f'{OUT}/records', exist_ok=True)


def tooldir(env, ver):
    d = os.environ.get(env, f'{OUT}/tools/yh03check/{ver}')
    if env not in os.environ and not os.path.isdir(d):
        os.makedirs(f'{OUT}/tools', exist_ok=True)
        a = subprocess.run(['git', '-C', HUB, 'archive', TOOLS_REF, f'tools/yh03check/{ver}'], capture_output=True)
        t = subprocess.run(['tar', '-x', '-C', f'{OUT}/tools', '--strip-components=1'], input=a.stdout, capture_output=True)
        if a.returncode or t.returncode:
            refuse(f'cannot extract tools/yh03check/{ver} from {HUB} at {TOOLS_REF}')
    return d


TOOL = tooldir('YH03CHECK', 'fb3bfbc1eea8')
UNIT = 'proofs/libdiginet/fuzz_transport'
HARNESS = 'projects/libdiginet/fuzz_transport/harness.yaml'
FILE = {'plain': f'{UNIT}/lib/Reusable/YH03.v', 'ubsan': f'{UNIT}/lib/U/Reusable/YH03.v'}
TWIN = {s: f'{P}/unstripped/fuzz_transport.{s}' for s in FILE}
PIN = {s: f'{P}/stripped/fuzz_transport.{s}' for s in FILE}
TWIN_SHA = {'plain': 'c2d42d895415', 'ubsan': 'c53d4b20cfc1'}
PIN_SHA = {'plain': 'bb20ce415827', 'ubsan': 'af7b86991906'}
TOOL_SHA = ('fb3bfbc1eea8', '1254e5c96a44')
rec, fail = [], 0


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()[:12]


def say(s):
    rec.append(s)
    print(s)


def bad(s):
    global fail
    fail = 1
    say(f'WRONG: {s}')


got = (sha(f'{TOOL}/yh03check.py'), sha(f'{TOOL}/yh03regen.py'))
if got != TOOL_SHA:
    refuse(f'{TOOL} holds yh03check {got[0]} + yh03regen {got[1]}, not {TOOL_SHA}')
for s in FILE:
    for what, p, want in (('twin', TWIN[s], TWIN_SHA[s]), ('pin', PIN[s], PIN_SHA[s])):
        if sha(p) != want:
            refuse(f'{s} {what} {p} is not {want}')
    if not os.path.isfile(f'{LIB}/{FILE[s][len(UNIT) + 5:]}'):
        refuse(f'no {s} file LIB/{FILE[s][len(UNIT) + 5:]}')
# the scratch checkout: the unit's lib is LIB (a symlink), the unit's harness.yaml the pins file
WT = f'{W}/wt'
shutil.rmtree(WT, ignore_errors=True)
os.makedirs(f'{WT}/{UNIT}')
os.symlink(LIB, f'{WT}/{UNIT}/lib')
os.makedirs(os.path.dirname(f'{WT}/{HARNESS}'))
if os.environ.get('PINS'):
    shutil.copyfile(os.environ['PINS'], f'{WT}/{HARNESS}')
    pins_src = f'{os.environ["PINS"]} (sha256 {sha(os.environ["PINS"])})'
else:
    full = {s: hashlib.sha256(open(PIN[s], 'rb').read()).hexdigest() for s in FILE}
    open(f'{WT}/{HARNESS}', 'w').write(
        '# STAND-IN written by yh03-gate.py: the builds block of the unit\'s harness.yaml with the sha256 of the new pins\n'
        'name: fuzz_transport\nbuilds:\n' + ''.join(
            f'  {s}:\n    file: fuzz_transport.{s}\n    bytes: {os.path.getsize(PIN[s])}\n    sha256: {full[s]}\n' for s in FILE))
    pins_src = 'a STAND-IN written by this gate from the sha256 of TIMG/stripped/fuzz_transport.{plain,ubsan}'
harness = open(f'{WT}/{HARNESS}').read()
for s in FILE:
    m = re.search(rf'^  {s}:\n(?:    .*\n)*?    sha256: ([0-9a-f]+)', harness, re.M)
    if not m or m.group(1)[:12] != PIN_SHA[s]:
        refuse(f'{HARNESS} does not pin {s} = {PIN_SHA[s]}')
# the YH03.v:44 cell of each side, read from the input: line 44 of the unit's YH03.v defines `src0_D_<prefix>_<rest>`, an
# internal library symbol. Its name is written CELL44 in the record (as D9's), and <prefix>_ is the donor's symbol prefix
# that hand-<side> drops from a D cell's name. Neither is written in this script.
CELL44 = {}
for s in FILE:
    l44 = (open(f'{WT}/{FILE[s]}').read().split('\n') + [''] * 44)[43]
    m = re.match(r'^Definition src0_D_(([A-Za-z0-9]+)_\w+) : Z := 0x[0-9a-fA-F]+\.$', l44)
    if not m:
        refuse(f'{FILE[s]}:44 is not a `Definition src0_D_<prefix>_<name> : Z := 0x...` cell')
    CELL44[s] = (m.group(1), m.group(2) + '_')


def tidy(s):
    return s.replace(P, '$TIMG').replace(WT + '/', '').replace(W + '/', '')


say(f'# command: {os.path.abspath(__file__)} {RUN} {LIB} {OUT} (TIMG={P} YH03CHECK={TOOL})')
say('# gate (e): yh03check fb3bfbc1eea8 (v6.4, + yh03regen 1254e5c96a44), every run with --pinned and --pins')
say(f'# images: plain twin {TWIN_SHA["plain"]} of pin {PIN_SHA["plain"]}, ubsan twin {TWIN_SHA["ubsan"]} of pin '
    f'{PIN_SHA["ubsan"]} ($TIMG/unstripped, $TIMG/stripped)')
say(f'# the pins file {HARNESS} of the scratch checkout: {pins_src}')
say(f'# LIB = {LIB} (read as {UNIT}/lib of the scratch checkout)')
for s, f in FILE.items():
    say(f'# LIB/{f[len(UNIT) + 5:]} sha256 {hashlib.sha256(open(f"{WT}/{f}", "rb").read()).hexdigest()}')


def run(case, tool, args, cwd):
    r = subprocess.run([sys.executable, f'{tool}/yh03check.py'] + args, cwd=cwd, capture_output=True, text=True)
    open(f'{W}/{case}.rows', 'w').write(r.stdout)
    open(f'{W}/{case}.err', 'w').write(r.stderr + f'rc={r.returncode}\n')
    lines = [x for x in r.stderr.splitlines() if x.startswith('#') and not x.startswith('# self-test')]
    selftest = next((x for x in r.stderr.splitlines() if x.startswith('# self-test')), '# self-test: NONE')
    say(f'{case}: rc {r.returncode}; rows printed {len(r.stdout.splitlines())}; {selftest[2:]}')
    for x in lines:
        say(f'  {tidy(x)}')
    if r.returncode == 2:
        for x in r.stderr.splitlines():
            if not x.startswith('#'):
                say(f'  {tidy(x)}')
    return r.returncode, r.stdout, r.stderr


def count(err):
    m = re.search(r'^# rows checked: (\d+); rows not OK: (\d+)$', err, re.M)
    return (int(m.group(1)), int(m.group(2))) if m else None


def strip(rows):
    return [re.sub(r'^[^\t]*:(\d+)\t', r'\1\t', x) for x in rows.splitlines()]


def plant(s):
    """a copy of the side's file at a path that names its build, src0_A_main moved by +4"""
    t = open(f'{WT}/{FILE[s]}').read()
    m = re.findall(r'Definition src0_A_main : Z := (0x[0-9a-f]+)\.', t)
    if len(m) != 1:
        refuse(f'{FILE[s]} has {len(m)} src0_A_main cells')
    old, new = m[0], hex(int(m[0], 16) + 4)
    root = f'{W}/plant-{s}'
    dst = f'{root}/{FILE[s]}'
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    open(dst, 'w').write(t.replace(f'Definition src0_A_main : Z := {old}.', f'Definition src0_A_main : Z := {new}.'))
    say(f'# plant-{s}: copy of {FILE[s]} with src0_A_main {old} -> {new} (one row moved)')
    return root, new


def judge_plant(case, base, planted, new):
    (_, bo, be), (prc, po, pe) = base, planted
    cb, cp = count(be), count(pe)
    b, p = strip(bo), strip(po)
    pairs = [(x, y) for x, y in zip(b, p) if x != y] if len(b) == len(p) else [(x, None) for x in b]
    gone, came = [x for x, _ in pairs], [y for _, y in pairs if y is not None]
    ok = (cb and cp and cp[0] == cb[0] and cp[1] == cb[1] + 1 and prc == 1 and len(gone) == 1 and len(came) == 1
          and re.match(r'^\d+\tmain\tOK(?: [A-Z0-9-]+)*\t', gone[0])
          and re.match(rf'^\d+\tmain\tBAD(?: [A-Z0-9-]+)*\tA={new} \(main\+0x4\)', came[0]))
    say(f'  {case}: rows not OK {cb and cb[1]} -> {cp and cp[1]}; rows that differ: {len(gone)} -> {len(came)}')
    for x in gone:
        say(f'    < {x}')
    for x in came:
        say(f'    > {x}')
    say(f'  {case}: control {"CAUGHT" if ok else "NOT CAUGHT"}')
    if not ok:
        bad(f'{case}: the planted row is not the one changed row (count +1, main OK -> BAD, rc 1)')


# the YH03-style files the core run staged
cell = re.compile(r'Definition (?:src0|ubs0)_[ADE]_')
staged = []
for d, _, fs in os.walk(f'{RUN}/stage-out'):
    for n in sorted(fs):
        if n.endswith('.v') and cell.search(open(os.path.join(d, n), errors='replace').read()):
            staged.append(os.path.relpath(os.path.join(d, n), RUN))
say(f'# staged YH03-style files (a src0_ / ubs0_ A, E or D cell) in RUN/stage-out: {len(staged)}')
for f in staged:
    bad(f'{f}: UNDECIDED (a staged YH03-style file; which image it names is not decided by this gate)')

def pinned(s, harness=HARNESS):
    return ['--pinned', PIN[s], '--pins', harness]


base, plants = {}, {}
for s in FILE:
    base[s] = run(f'base-{s}', TOOL, pinned(s) + [TWIN[s], FILE[s]], WT)
    c = count(base[s][2])
    if base[s][0] == 2 or c is None:
        bad(f'base-{s}: refused or no count line')
    if not re.search(rf"^# unit identity: .*: the image's \d+ PT_LOADs equal the {s} pin {PIN_SHA[s]} ", base[s][2], re.M):
        bad(f'base-{s}: no unit-identity line for the {s} pin {PIN_SHA[s]}')
for s in FILE:
    root, new = plant(s)
    plants[s] = (root, new)
    shutil.copyfile(f'{WT}/{HARNESS}', f'{root}/harness.yaml')
    judge_plant(f'plant-{s}', base[s], run(f'plant-{s}', TOOL, pinned(s, 'harness.yaml') + [TWIN[s], FILE[s]], root), new)
other = {'plain': 'ubsan', 'ubsan': 'plain'}
for s in FILE:
    # --proofs the unit's lib: os.walk follows the lib symlink only when it is the walk's top
    r = run(f'ident-{s}', TOOL, pinned(s) + ['--other-side', FILE[other[s]], '--proofs', f'{UNIT}/lib', TWIN[s], FILE[s]],
            WT)
    if not re.search(r'^# COPIED: \d+ of the \d+ code cells', r[2], re.M):
        bad(f'ident-{s}: no COPIED line')
    if count(r[2]) != count(base[s][2]):
        bad(f'ident-{s}: count {count(r[2])} differs from base-{s}\'s {count(base[s][2])}')
r = run('mixed', TOOL, pinned('plain') + [TWIN['plain'], FILE['ubsan']], WT)
ok = r[0] == 2 and not r[1] and re.search(r'ubsan', r[2]) and re.search(r'plain', r[2]) and 'REFUSED' in r[2]
say(f'  mixed: control {"CAUGHT" if ok else "NOT CAUGHT"} (the ubsan file on the plain twin with the plain pin: '
    f'refused, rc 2)')
if not ok:
    bad('mixed: the ubsan file on the plain twin is not refused')


# hand-<side>: the cells v6.4 does not judge (registry: KNOWN LIMIT `not checked by any rule`, KNOWN GAP NOSYM), read
# against the side's twin by content (the twin's PT_LOADs equal the pin's: the unit-identity line above)
def elf_reader(path):
    from elftools.elf.elffile import ELFFile
    e = ELFFile(open(path, 'rb'))
    segs = [(p['p_vaddr'], p['p_filesz'], p.data()) for p in e.iter_segments() if p['p_type'] == 'PT_LOAD']
    syms = {}
    st = e.get_section_by_name('.symtab')
    for x in (st.iter_symbols() if st else []):
        syms.setdefault(x.name, x['st_value'])

    def rd(a, n):
        for va, fs, d in segs:
            if va <= a and a + n <= va + fs:
                return d[a - va:a + n - va]
        return None
    return rd, syms


def hand(s):
    rd, syms = elf_reader(TWIN[s])
    text = open(f'{WT}/{FILE[s]}').read()
    rows = [x.split('\t') for x in base[s][1].splitlines()]
    nosym = [x for x in rows if len(x) > 3 and x[2] == 'NOSYM']
    unchecked = []
    for x in base[s][2].splitlines():
        m = re.match(r'^# not checked by any rule: [^:]+: (.*)$', x)
        if m:
            unchecked += [n.strip() for n in m.group(1).split(',') if n.strip()]
    say(f'hand-{s}: {len(nosym)} NOSYM D cell(s), {len(unchecked)} cell(s) `not checked by any rule` ({", ".join(unchecked)})')
    for x in nosym:
        where, name, ann = x[0], x[1], x[3]
        v = int(re.match(r'V=(0x[0-9a-f]+)', ann).group(1), 16)
        verdict, how = 'OPEN', 'no content rule for this cell form'
        m = re.match(r'^D_const_\w*?_0x([0-9a-fA-F]{16})$', name)
        g = re.match(r'^D_got_(\w+)$', name)
        a = re.match(r'^V=0x[0-9a-f]+ \((\S+)\+0x0\)$', ann)
        if m:
            b = rd(v, 8)
            want = int(m.group(1), 16)
            got = int.from_bytes(b, 'little') if b else None
            verdict = 'OK' if got == want else 'BAD'
            how = f'the 8 bytes at {v:#x}: {got:#018x} (the name says {want:#018x})' if b else f'{v:#x} is not file-backed'
        elif g:
            target = syms.get('__' + g.group(1), syms.get(g.group(1)))
            b = rd(v, 8)
            got = int.from_bytes(b, 'little') if b else None
            verdict = 'OK' if target is not None and got == target else 'BAD'
            how = (f'the 8 bytes at {v:#x}: {got:#x}; the symbol __{g.group(1)} is at '
                   f'{target:#x}' if target is not None and b else f'no symbol __{g.group(1)} or no bytes at {v:#x}')
        elif name == 'D_debruijn32':
            # the table of a de Bruijn ctz: table[((x & -x) * M mod 2^32) >> 27] = ctz(x). M is read back from the table
            # itself (bit b of M is the top bit of the index that holds 31 - b) and the property is then checked for
            # every i: a 32-byte permutation that is not such a table fails it.
            b = rd(v, 32)
            perm = b is not None and sorted(b) == list(range(32))
            prop, mul = False, None
            if perm:
                inv = {b[p]: p for p in range(32)}
                mul = sum(((inv[31 - k] >> 4) & 1) << k for k in range(32))
                prop = all(b[(((1 << i) * mul) & 0xffffffff) >> 27] == i for i in range(32))
            verdict = 'OK' if prop else 'BAD'
            how = (f'the 32 bytes at {v:#x} are a permutation of 0..31: {perm}; the multiplier the table encodes: '
                   f'{mul:#010x}; table[((1 << i) * {mul:#010x} mod 2^32) >> 27] = i for i = 0..31: {prop}'
                   if perm else f'the 32 bytes at {v:#x} are not a permutation of 0..31')
        elif a:
            sym = a.group(1)
            tail = re.sub(r'^D_(' + re.escape(CELL44[s][1]) + r')?', '', name)
            norm = re.sub(r'[^0-9A-Za-z]', '_', sym)
            verdict = 'OK' if norm.endswith(tail) and syms.get(sym) == v else 'OPEN'
            how = f'{v:#x} is {sym}+0x0 (twin symtab); its name, `.` written `_`, ends with `{tail}`: {norm.endswith(tail)}'
        say(f'  {tidy(where)}\t{name}\t{verdict}\t{how}')
        if verdict != 'OK':
            bad(f'hand-{s}: {name} {verdict}')
    # control: the two content rules on a moved address must refuse (a D_const cell moved by +8; the de Bruijn table
    # moved by +1)
    ctl = []
    for x in nosym:
        name, v = x[1], int(re.match(r'V=(0x[0-9a-f]+)', x[3]).group(1), 16)
        m = re.match(r'^D_const_\w*?_0x([0-9a-fA-F]{16})$', name)
        if m and not any(c[0] == 'const' for c in ctl):
            b = rd(v + 8, 8)
            ctl.append(('const', f'{name} at {v + 8:#x}', b is None or int.from_bytes(b, 'little') != int(m.group(1), 16)))
        if name == 'D_debruijn32':
            b = rd(v + 1, 32)
            ok = b is not None and sorted(b) == list(range(32))
            if ok:
                inv = {b[p]: p for p in range(32)}
                mul = sum(((inv[31 - k] >> 4) & 1) << k for k in range(32))
                ok = all(b[(((1 << i) * mul) & 0xffffffff) >> 27] == i for i in range(32))
            ctl.append(('debruijn', f'{name} at {v + 1:#x}', not ok))
    for kind, what, refused in ctl:
        say(f'  hand-{s} control ({kind} rule, {what}): {"CAUGHT" if refused else "NOT CAUGHT"}')
        if not refused:
            bad(f'hand-{s}: the {kind} rule accepts a moved address')
    for n in unchecked:
        m = re.search(rf'Definition {re.escape(n)} : (?:option )?Z := ([^.]+)\.', text)
        val = m.group(1).strip() if m else None
        if n == 'src0_vmlock':
            vs = [k for k in syms if re.search(r'(^|_)vmlock$', k)]
            want = 'None' if not vs else f'Some {syms[vs[0]]:#x}'
            verdict = 'OK' if val is not None and val.replace('(', '').replace(')', '') == want else 'BAD'
            say(f'  {n}\t{verdict}\tthe file states {val}; the twin symtab has {"no vmlock symbol" if not vs else vs}, so '
                f'the right value is {want}')
        elif n == 'src0_debruijn_len':
            dv = re.search(r'Definition src0_D_debruijn32 : Z := (0x[0-9a-f]+)\.', text)
            verdict = 'OK' if val == '32' and dv else 'OPEN'
            say(f'  {n}\t{verdict}\tthe file states {val}; the table D_debruijn32 is 32 one-byte entries (hand-{s} above)')
        else:
            verdict = 'OPEN'
            say(f'  {n}\tOPEN\tthe file states {val}; no content rule for this cell')
        if verdict != 'OK':
            bad(f'hand-{s}: {n} {verdict}')


for s in FILE:
    hand(s)
say(f'yh03-gate: {"PASS" if not fail else "FAILED"}')
for s in FILE:
    say(f'# rows of base-{s} (yh03check fb3bfbc1eea8, {FILE[s]} on the {s} twin {TWIN_SHA[s]})')
    for x in base[s][1].splitlines():
        rec.append(tidy(x))
# as D9's record: the name of the YH03.v:44 cell (an internal library symbol name) is written CELL44 in the record
# (the raw rows stay in OUT/work/yh03/*.rows)
out = '\n'.join(rec) + '\n'
red = out
for c in sorted({CELL44[s][0] for s in FILE}):
    red = re.sub(r'_*' + re.escape(c), 'CELL44', red)
if red != out:
    red = ('# Note: the name of the unit\'s YH03.v:44 cell (an internal library symbol name) is written CELL44 in this '
           'record.\n' + red)
open(f'{OUT}/records/yh03check.txt', 'w').write(red)
sys.exit(fail)
