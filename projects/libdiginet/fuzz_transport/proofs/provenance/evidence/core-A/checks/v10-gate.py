#!/usr/bin/env python3
"""v10-gate.py WORK LIB OUT -- gate (d) of the libdiginet/fuzz_transport image-A core relocation (pool row TCA):
global_settings v10 439f8e3bd463 over the files this core adds and their released donor files (checks/v10_table.py beside
this file), the counts before / after reusable-local.py on the two shared files, run.sh's normalised DON against the
released files, and a planted kernel-level setting. libdiginet/fuzz_decode's gate of record checks/v10-gate.py
(sha256 f37f6847d7ad; internal record) with only the unit, the paths and the inputs changed.

  WORK    the relocation run dir (run.sh's WORK)
  LIB     the unit's lib the run used (proofs/libdiginet/fuzz_transport/lib): its Reusable/YImgTop.v is taken by path
  OUT     OUT/work/v10/: working output (the plant's copy of WORK/stage-out, the before-copies, the plant's table, the
          extracted released donor tree); OUT/records/v10-donor-lines.tsv and OUT/records/settings-count.txt: the records
Environment (defaults in brackets):
  GS     a directory holding global_settings.py 439f8e3bd463, its SHA256SUMS and the control files SHA256SUMS names
         [OUT/tools/global_settings/439f8e3bd463, extracted from the hub HUB at TOOLS_REF when absent]
  DONWT  a tree holding fuzz_grant's released lib at 25e3d17bdb50 (proofs/libreac/fuzz_grant/lib, NOT normalised)
         [OUT/work/v10/donwt, extracted from the hub at 25e3d17bdb50 when absent]
  DON    run.sh's DON, the same lib normalised: every donor file read must equal its released file once the module text
         ...fuzz_grant.lib.Reusable is written ...fuzz_grant.lib [required]
  HUB    the hub repository [required; no host path is written here]
Expected (exit 0): the table's rc 0 and 0 unpaired rows; KERNEL 0; the donor rows with no target row are exactly the
`Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=` rows of Reusable/YA09.v and YA0e.v that
reusable-local.py made Local, so target ESCAPES = donor ESCAPES - their number; the plant (`Unset Guard Checking.`
appended to a copy of one staged file, in a copy of WORK/stage-out) gives exactly one KERNEL row, global_settings rc 5,
and exactly one UNPAIRED row, that one. Exit 1 otherwise, 2 on a bad input.
rule: proves no function (kind: measurement)."""
import hashlib
import os
import re
import shutil
import subprocess
import sys


def refuse(msg):
    print(f'v10-gate: REFUSED: {msg}', file=sys.stderr)
    sys.exit(2)


if len(sys.argv) != 4:
    refuse('usage: v10-gate.py WORK LIB OUT')
RUN, LIB, OUT = (os.path.abspath(a) for a in sys.argv[1:4])
HUB = os.environ.get('HUB') or refuse('set HUB to the hub repository')
TOOLS_REF = os.environ.get('TOOLS_REF', '91ef630666824d85906ae28a461aec2ae1e9653d')
DON_REF = '25e3d17bdb50'
W = f'{OUT}/work/v10'
os.makedirs(W, exist_ok=True)
os.makedirs(f'{OUT}/records', exist_ok=True)


def extract(ref, path, dest, strip):
    os.makedirs(dest, exist_ok=True)
    a = subprocess.run(['git', '-C', HUB, 'archive', ref, path], capture_output=True)
    t = subprocess.run(['tar', '-x', '-C', dest, f'--strip-components={strip}'], input=a.stdout, capture_output=True)
    if a.returncode or t.returncode:
        refuse(f'cannot extract {ref}:{path} from {HUB}: {a.stderr.decode()[-300:]}{t.stderr.decode()[-300:]}')


GSD = os.environ.get('GS', f'{OUT}/tools/global_settings/439f8e3bd463')
if 'GS' not in os.environ and not os.path.isdir(GSD):
    extract(TOOLS_REF, 'tools/global_settings/439f8e3bd463', f'{OUT}/tools', 1)
DONWT = os.environ.get('DONWT', f'{W}/donwt')
if 'DONWT' not in os.environ and not os.path.isdir(f'{DONWT}/proofs/libreac/fuzz_grant/lib'):
    extract(DON_REF, 'proofs/libreac/fuzz_grant/lib', DONWT, 0)
DON = os.environ.get('DON') or refuse('set DON to the released fuzz_grant lib, normalised')
HERE = os.path.dirname(os.path.abspath(__file__))
TAB, GS = f'{HERE}/v10_table.py', f'{GSD}/global_settings.py'
TL, DL = 'proofs/libdiginet/fuzz_transport/lib/', 'proofs/libreac/fuzz_grant/lib/'
FLAG = 'Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::='
SHARED = ('Reusable/YA09.v', 'Reusable/YA0e.v')
KERNEL_PLANT = 'Unset Guard Checking.'


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


if sha(GS) != '439f8e3bd4637640d6d40fb668716c081c3ba202aa831f31f0120de0b4e39242':
    refuse(f'{GS} is not global_settings 439f8e3bd463')
# the tool directory's SHA256SUMS (sha256 e0d40ab468e9; internal record) names every file of the tool directory; its own line cannot
# match itself, every other line must
sums = [x.split(None, 1) for x in open(f'{GSD}/SHA256SUMS').read().splitlines() if x.strip()]
sums_bad = [n for h, n in sums if n != 'SHA256SUMS' and (not os.path.exists(f'{GSD}/{n}') or sha(f'{GSD}/{n}') != h)]
if sums_bad:
    refuse(f'{GSD}: SHA256SUMS lines that fail: {sums_bad}')
SUMS_LINE = (f'SHA256SUMS {sha(f"{GSD}/SHA256SUMS")[:12]}: {len(sums) - 1} of {len(sums) - 1} files OK (its own line '
             'excluded)')
fail = 0
log = []


def bad(s):
    global fail
    fail = 1
    log.append(f'# WRONG: {s}')
    print(f'WRONG: {s}')


def table(run_dir, out, files=None):
    r = subprocess.run([sys.executable, TAB, run_dir, GS, LIB, DONWT, out] + ([files] if files else []),
                       capture_output=True, text=True)
    t = r.stdout

    def one(pat):
        m = re.search(pat, t, re.M)
        return m.groups() if m else None
    return {'rc': r.returncode, 'out': t, 'err': r.stderr,
            'target': one(r'^target: (SUMMARY: .*) rc (\d+)$'), 'donor': one(r'^donor:  (SUMMARY: .*) rc (\d+)$'),
            'unpaired': int(one(r'^unpaired target rows: (\d+)$')[0]),
            'unpaired_rows': re.findall(r'^UNPAIRED (.*)$', t, re.M),
            'donor_only': [(f, int(n), rest) for f, n, rest in re.findall(r'^DONOR-ONLY (\S+): (\d+) x (.*)$', t, re.M)],
            'kept': re.findall(r'^kept by LIB \(not added, not read\): (.*)$', t, re.M)}


def gs(root, rels):
    r = subprocess.run([sys.executable, GS, root] + list(rels), capture_output=True, text=True)
    m = re.search(r'^(SUMMARY: .*)$', r.stdout, re.M)
    return r.returncode, m and m.group(1), re.findall(r'^   :(\d+) KERNEL: (.*)$', r.stdout, re.M)


def num(summary, key):
    return int(re.search(rf'\b{key} (\d+)', summary).group(1))


# 1. the record run
rec = table(RUN, f'{OUT}/records/v10-donor-lines.tsv', f'{W}/files.txt')
files = open(f'{W}/files.txt').read().split()
if not rec['target'] or not rec['donor']:
    refuse(f'v10_table.py printed no SUMMARY (rc {rec["rc"]}): {rec["err"][-500:]}')
tsum, trc = rec['target'][0], int(rec['target'][1])
dsum, drc = rec['donor'][0], int(rec['donor'][1])
rows = [x.split('\t') for x in open(f'{OUT}/records/v10-donor-lines.tsv').read().splitlines()
        if x and not x.startswith('#') and not x.startswith('file\t')]
nA = sum(f.startswith('A/') for f in files)
nR = len(files) - nA - 1
if rec['rc'] or trc or drc or rec['unpaired']:
    bad(f'the record table: rc {rec["rc"]}, target rc {trc}, donor rc {drc}, unpaired {rec["unpaired"]}')
for x in rec['unpaired_rows']:
    bad(f'UNPAIRED {x}')
if num(tsum, 'KERNEL') or num(dsum, 'KERNEL'):
    bad('a KERNEL row in the target or donor files')

# 2. the two shared files: before / after reusable-local.py, and fuzz_grant's released copies
before_root = f'{W}/before'
made_local = {}
for f in SHARED:
    if f not in files:
        bad(f'{f} is not among the files read')
    t = open(f'{RUN}/stage-out/{f}').read()
    made_local[f] = t.count('Local ' + FLAG)
    os.makedirs(os.path.dirname(f'{before_root}/{TL}{f}'), exist_ok=True)
    open(f'{before_root}/{TL}{f}', 'w').write(t.replace('Local ' + FLAG, FLAG))
local_elsewhere = {f'{where}:{f}': open(p).read().count('Local ' + FLAG)
                   for f in SHARED for where, p in (('RUN/stage', f'{RUN}/stage/{f}'), ('released', f'{DONWT}/{DL}{f}'))
                   if os.path.exists(p)}
b_rc, b_sum, _ = gs(before_root, [TL + f for f in SHARED])
a_rc, a_sum, _ = gs(f'{RUN}/stage-out', SHARED)
r_rc, r_sum, _ = gs(DONWT, [DL + f for f in SHARED])
n_local = sum(made_local.values())
if any(local_elsewhere.values()):
    bad(f'a `Local` Zify redefinition in port_core\'s input or the released copies: {local_elsewhere}')
if num(b_sum, 'ESCAPES') != num(r_sum, 'ESCAPES') or num(b_sum, 'ESCAPES') - num(a_sum, 'ESCAPES') != n_local:
    bad(f'shared files: before {b_sum} / after {a_sum} / released {r_sum} / made Local {n_local}')

# 3. the other files and the donor-only rows
t_other = num(tsum, 'ESCAPES') - num(a_sum, 'ESCAPES')
d_other = num(dsum, 'ESCAPES') - num(r_sum, 'ESCAPES')
if t_other != d_other:
    bad(f'the other files: target ESCAPES {t_other} != donor {d_other}')
only_ok = all(f in SHARED and rest == f'ESCAPES TACTIC: {FLAG}' for f, _, rest in rec['donor_only'])
only_n = {f: n for f, n, _ in rec['donor_only']}
if not only_ok or only_n != {f: made_local[f] for f in SHARED if made_local[f]}:
    bad(f'the donor rows with no target row are not exactly the Zify redefinitions made Local: {rec["donor_only"]}')
if num(dsum, 'ESCAPES') - num(tsum, 'ESCAPES') != n_local:
    bad(f'ESCAPES target {num(tsum, "ESCAPES")} != donor {num(dsum, "ESCAPES")} - {n_local}')
unmeasured = [r for r in rows if r[2] == 'UNMEASURED']


def src_lines(path, cache={}):
    if path not in cache:
        cache[path] = open(path).read().splitlines()
    return cache[path]


# 3b. the whole source line of each paired row against its donor file's line (not only the setting text)
line_diff = []
for r in rows:
    if r[4] == 'UNPAIRED':
        continue
    tp = f'{LIB}/{r[0]}' if r[0] == 'Reusable/YImgTop.v' else f'{RUN}/stage-out/{r[0]}'
    tl, dl = src_lines(tp)[int(r[1]) - 1], src_lines(f'{DONWT}/{r[4]}')[int(r[5]) - 1]
    if tl != dl:
        line_diff.append(f'{r[0]}:{r[1]} `{tl.strip()}` vs donor {r[4]}:{r[5]} `{dl.strip()}`')
for x in line_diff:
    bad(f'a paired row whose source line is not its donor line: {x}')

# 4. run.sh's normalised DON against the released files
don_line = None
if DON:
    same, diff = 0, []
    for f in files:
        d = f'{DON}/{f}' if f.startswith('A/') else f'{DON}/{f[len("Reusable/"):]}'
        want = open(f'{DONWT}/{DL}{f}').read().replace('OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib.Reusable',
                                                     'OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib')
        if os.path.exists(d) and open(d).read() == want:
            same += 1
        else:
            diff.append(f)
    don_line = (f'# run.sh\'s normalised DON: {same} of {len(files)} donor files equal their released file with the module '
                f'text ...fuzz_grant.lib.Reusable written ...fuzz_grant.lib' + (f'; differ: {" ".join(diff)}' if diff else ''))
    if diff:
        bad(f'DON differs from the released files: {diff}')

# 5. the plant: one kernel-level setting appended to a copy of one staged file, in a copy of RUN/stage-out
pf = next(f for f in files if f.startswith('A/'))
prun = f'{W}/plant-run'
shutil.rmtree(prun, ignore_errors=True)
shutil.copytree(f'{RUN}/stage-out', f'{prun}/stage-out')
t = open(f'{prun}/stage-out/{pf}').read()
t = t if t.endswith('\n') else t + '\n'
pline = t.count('\n') + 1
open(f'{prun}/stage-out/{pf}', 'w').write(t + KERNEL_PLANT + '\n')
p_rc, p_sum, p_kernel = gs(f'{prun}/stage-out', [pf])
plant = table(prun, f'{W}/plant-v10-donor-lines.tsv')
p_t = plant['target']
want_unpaired = f'{pf}:{pline} KERNEL KERNEL: {KERNEL_PLANT}'
caught = (p_rc == 5 and p_kernel == [(str(pline), KERNEL_PLANT)] and p_t and int(p_t[1]) == 5
          and num(p_t[0], 'KERNEL') == 1 and plant['unpaired'] == 1 and plant['unpaired_rows'] == [want_unpaired]
          and plant['rc'] == 1 and num(p_t[0], 'ESCAPES') == num(tsum, 'ESCAPES'))
if not caught:
    bad(f'the plant is not caught as one KERNEL row: file rc {p_rc} kernel {p_kernel}; table {p_t} '
        f'unpaired {plant["unpaired_rows"]} rc {plant["rc"]}')


def src_line(path, ln):
    return open(path).read().splitlines()[int(ln) - 1].strip()


um = []
for r in unmeasured:
    tl = src_line(f'{LIB}/{r[0]}' if r[0] == 'Reusable/YImgTop.v' else f'{RUN}/stage-out/{r[0]}', r[1])
    dl = src_line(f'{DONWT}/{r[4]}', r[5])
    um.append(f'lib/{r[0]}:{r[1]} `{tl}`, ' + (f'the same line as fuzz_grant\'s released {r[4][len("proofs/libreac/fuzz_grant/"):]}:{r[5]}'
              if tl == dl else f'fuzz_grant\'s released {r[4]}:{r[5]} reads `{dl}`'))
    if tl != dl:
        bad(f'UNMEASURED row lib/{r[0]}:{r[1]} is not its donor line')


def listsha(root, rels):
    return hashlib.sha256(''.join(f'{sha(os.path.join(root, f))}  {f}\n' for f in rels).encode()).hexdigest()[:12]


# 6. the files the unit writes itself for this core (no donor file): env UNIT_FILES (space-separated paths), default
# LIB/A/TransportDrvG.v and LIB/A/TransportDriver.v where present. global_settings over each; a KERNEL row fails the gate
unit_files = os.environ.get('UNIT_FILES', '').split() or [
    p for p in (f'{LIB}/A/TransportDrvG.v', f'{LIB}/A/TransportDriver.v') if os.path.exists(p)]
unit_lines = []
for p in unit_files:
    u_rc, u_sum, u_kernel = gs(os.path.dirname(p), [os.path.basename(p)])
    unit_lines.append(f'#   {os.path.basename(p)} (sha256 {sha(p)[:12]}): {u_sum} rc {u_rc}')
    if u_kernel or u_sum is None or num(u_sum, 'KERNEL'):
        bad(f'{os.path.basename(p)}: a KERNEL row or no SUMMARY')

out = [
    f'# command: {os.path.abspath(__file__)} {RUN} {LIB} {OUT} (GS={GSD} DONWT={DONWT} DON={DON})',
    '# global_settings v10 (sha256 439f8e3bd4637640d6d40fb668716c081c3ba202aa831f31f0120de0b4e39242), checks/v10_table.py '
    f'{sha(TAB)[:12]}; {SUMS_LINE}',
    f'# inputs: the {len(files) - 1} staged files (sha256 of their sorted `sha256  path` list) '
    f'{listsha(f"{RUN}/stage-out", files[:-1])}; LIB/Reusable/YImgTop.v {sha(f"{LIB}/Reusable/YImgTop.v")[:12]}; '
    f'donor tree fuzz_grant lib at {DON_REF} (git archive of the hub), the {len(files)} donor files '
    f'{listsha(f"{DONWT}/{DL}", files)}',
    f'# this core: the {len(files) - 1} files of the run\'s stage-out (A/ {nA}, Reusable/ {nR}) + lib/Reusable/YImgTop.v '
    f'(taken by path); kept by lib (not added): {len(rec["kept"])}',
    f'{tsum} rc {trc}',
    f'# fuzz_grant\'s released counterparts of the same {len(files)} (released at 25e3d17bdb50, lib/A/X.v and '
    'lib/Reusable/X.v)',
    f'{dsum} rc {drc}',
    f'# every one of the {len(rows)} target rows is paired with the identical setting of its donor file '
    f'(v10-donor-lines.tsv); {rec["unpaired"]} unpaired; the whole source line equals the donor file\'s line in '
    f'{sum(r[4] != "UNPAIRED" for r in rows) - len(line_diff)} of {sum(r[4] != "UNPAIRED" for r in rows)} paired rows',
    '# the difference is reusable-local.py on the two SHARED files lib/Reusable/YA09.v and YA0e.v:',
    f'#   before (as port_core wrote them): {b_sum}',
    f'#   after (as staged):               {a_sum}',
    f'#   fuzz_grant\'s released copies:     {r_sum}',
    f'#   ("before" = the staged copies with the `Local` of each of the {" + ".join(str(made_local[f]) for f in SHARED)}'
    f' = {n_local} Local Zify redefinitions removed; port_core\'s input copies (RUN/stage) and the released copies '
    f'carry {sum(local_elsewhere.values())} Local ones)',
    f'# so the other {len(files) - 2} files carry ESCAPES {t_other} = {num(dsum, "ESCAPES")} - {num(r_sum, "ESCAPES")}, '
    f'equal to their donors\' ({d_other}); the donor rows with no target row are exactly those {n_local} '
    f'({", ".join(f"{f} {n}" for f, n, _ in rec["donor_only"])})',
    (f'# the one UNMEASURED row is {um[0]}' if len(um) == 1 else f'# UNMEASURED rows: {len(um)}: ' + '; '.join(um)),
    f'# KERNEL rows: target {num(tsum, "KERNEL")}, donor {num(dsum, "KERNEL")}',
    f'# files the unit writes itself for this core (no donor file; UNIT_FILES): {len(unit_files)}',
] + unit_lines + [
]
if don_line:
    out.append(don_line)
out += [
    f'# PLANT (control): `{KERNEL_PLANT}` appended as line {pline} of a copy of {pf}, in a copy of RUN/stage-out:',
    f'#   global_settings on that file: {len(p_kernel)} KERNEL row(s) '
    f'({"; ".join(f":{n} KERNEL: {s}" for n, s in p_kernel)}), rc {p_rc}',
    f'#   checks/v10_table.py on the copy: target {p_t[0] if p_t else None} (rc {p_t[1] if p_t else None}); '
    f'UNPAIRED {plant["unpaired"]}: {"; ".join(plant["unpaired_rows"])}; exit {plant["rc"]}',
    f'#   control {"CAUGHT" if caught else "NOT CAUGHT"}',
] + log + [f'# v10-gate: {"PASS" if not fail else "FAILED"}']
open(f'{OUT}/records/settings-count.txt', 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
sys.exit(fail)
