#!/usr/bin/env python3
"""mk_evidence.py OUT_DIR -- builds the fuzz_uci image-B start-up evidence slice (proofs/reac-repacer/fuzz_uci/
provenance/evidence/startup-B/) from the writers of record, by running them; nothing in the slice is edited by hand.

What it writes (MANIFEST.md, also written here, names each file's role):
  scripts/, exitdrv/   this slice's own writers, copied from the lane, each checked to hold no machine path
  env.example.sh       every variable the writers read, without values (the lane env file holds the values)
  tables/              per-value tables, each written by re-running its writer now:
                         yb13.slots.tsv (ucib_yb13.py --table), exitdrv-numerals.md (gen_exitB.py), af0m-base-audit.tsv
                         (relocownUciB.py), af0m-adds.txt (addsB.py), pac-fill-triage.txt (pac_fill.py on the gate's
                         port_addr_check cb0e TSV), YCej.universe.json (the YCej run's table, as written by ycej_json.py)
  gates/GATE-RECORD.md the gate record, written by gate_record() from the gate runs' own output (gates/logs of the
                       lane): every RESULT line and the summary lines of each gate, machine paths replaced by the
                       variable that names them, build-machine names dropped
A frozen or third-party tool is CITED (name, sha256, the commit and path that hold that exact copy), never copied:
its own text carries host-path patterns and would fail the lint as shipped. Only this slice's writers ship. The
writer of provenance/evidence/MANIFEST.md and MANIFEST (the shared index above this slice) is a registered tool of
the shared tool set, so it too is cited, not copied: no slice holds a second copy of it.

Checks before it exits 0 (CHECKS in MANIFEST.md): every file of the slice is text, holds none of oft lint's
private-data shapes (tools/oft/lint.py HOST_PATH, PRIVATE_IP, PRIVATE_HOST_NAME, REPOSITORY_PATH, EMAIL, TOKEN,
PRIVATE_KEY; read from the checkout), no tmp or mnt path, no build-machine name, no Tailscale name, and no derived
suffix (.vo .glob .pyc .gz ...).

  mk_evidence.py OUT_DIR        (needs the lane env file sourced: ucib_env.py names every variable)
"""
import hashlib, importlib.util, json, os, re, shutil, subprocess, sys, tempfile

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ucib_env import need  # noqa: E402

W = need('UCIB_W')
OVPI = need('UCIB_OVPI')
TLIB = need('UCIB_TLIB')
REPO = os.path.abspath(os.path.join(TLIB, '..', '..', '..', '..'))   # the checkout holding the unit lib
SLICE_REL = 'proofs/reac-repacer/fuzz_uci/provenance/evidence/startup-B'

# lane path (under $UCIB_W) -> slice path, role
SCRIPTS = [
    ('tools/ucib_env.py', 'scripts/ucib_env.py', 'every machine-specific path the writers read, from the environment'),
    ('tools/nsB.py', 'scripts/nsB.py', 'module paths of a generated file in the lib/B layout (port_core rename_text) + '
     'the header rule (hdrfix.py); the gate: Require (dir, module) set = fuzz_grant B\'s released twin'),
    ('tools/hdrfix.py', 'scripts/hdrfix.py', 'the committed-header rule on comments (undated Theorem Labs notice, no '
     'agent / lane / branch names, no dates, no host paths); code untouched'),
    ('tools/hdrscan.py', 'scripts/hdrscan.py', 'counts host paths, agent / lane names, branch names and dates in comments'),
    ('tools/stripcmp.py', 'scripts/stripcmp.py', 'comment-stripped diff of two .v files (comments-only proof)'),
    ('tools/ucib_yb13.py', 'scripts/ucib_yb13.py', 'YB13.v: image numerals by the donor\'s rules (decode gen.py slots '
     '+ segment 1 base); control on cgif\'s image; --table writes tables/yb13.slots.tsv'),
    ('tools/uci_ab1hk_drive.py', 'scripts/uci_ab1hk_drive.py', 'YB1h.v / YB1k.v / YB1l.v through gen_ab1hk.py (cited)'),
    ('tools/mk_yb05_uci.py', 'scripts/mk_yb05_uci.py', 'YB05.v: hsform header + the plan the collected pass 2 ran'),
    ('tools/addhdr.py', 'scripts/addhdr.py', 'the modification notice and pin line of YB1v.v / YB1m.v (boxb1 output)'),
    ('tools/elfinfo.py', 'scripts/elfinfo.py', 'nm / section / program-header listings of an ELF (pyelftools)'),
    ('tools/trunk_missing.py', 'scripts/trunk_missing.py', 'Required modules the trunk lib does not hold (build check)'),
    ('tools/run_restB.sh', 'scripts/run_restB.sh', 'YB12 / YD2i / YD2j / YD1k / YE3i: atable, gen_ad2, gen_ad1k, ae3i '
     '(cited) with their cgif controls and the planted atable control'),
    ('tools/hdr.YB12.txt', 'scripts/hdr.YB12.txt', 'the header atable writes into YB12.v'),
    ('tools/af0mB/run_af0mB.sh', 'scripts/af0mB/run_af0mB.sh', 'YF0m.v: af0m (cited) on the derived base, its '
     'controls, refused-row decisions and --add cells, each with its reason'),
    ('tools/af0mB/relocownUciB.py', 'scripts/af0mB/relocownUciB.py', 'the base\'s Tfib_owned_static re-derived by '
     'name (decode B\'s relocownB.py rule, cited); writes tables/af0m-base-audit.tsv'),
    ('tools/af0mB/addsB.py', 'scripts/af0mB/addsB.py', 'af0m --add cells mapped by name from decode B\'s list'),
    ('tools/af0mB/ab01log_B.py', 'scripts/af0mB/ab01log_B.py', 'cgif\'s released YB01 states in log form (af0m '
     'control input)'),
    ('sub/exitdrv/gen_exitB.py', 'exitdrv/gen_exitB.py', 'YE23.v / YD1y.v / YE37.v (exit-driver relocation; all 8 '
     'descriptor words in YE37); its controls first; writes tables/exitdrv-numerals.md'),
    ('sub/exitdrv/run.sh', 'exitdrv/run.sh', 'the exit-driver run (binmatch, gen_exitB, controls, nsB)'),
    ('sub/exitdrv/run_binmatch_uciB.py', 'exitdrv/run_binmatch_uciB.py', 'binmatch.py (cited) cgif -> fuzz_uci, the '
     'identical-function map gen_exitB reads'),
    ('sub/acej/run.sh', 'scripts/acej/run.sh', 'YCej.v: gen_traces + acej (cited), controls, negative controls, '
     'members check, the universe json'),
    ('sub/acej/header-B.txt', 'scripts/acej/header-B.txt', 'the header acej writes into YCej.v'),
    ('sub/acej/drv_check.py', 'scripts/acej/drv_check.py', 'the 8 driver traces derived from the universe json'),
    ('sub/gates/run_gates.sh', 'scripts/gates/run_gates.sh', 'every gate G0-G12, each control first'),
    ('sub/gates/codeptr-decl.sh', 'scripts/gates/codeptr-decl.sh', 'codeptr pass-2 declarations, each with its role '
     'in both images (1 --same, 18 --not-address)'),
    ('sub/gates/pac_table.py', 'scripts/gates/pac_table.py', 'port_addr_check flag classes per file vs the control'),
    ('sub/gates/tools/pac_fill.py', 'scripts/gates/pac_fill.py', 'triage of every GENERATOR-FILL row'),
    ('sub/gates/tools/pac_moved.py', 'scripts/gates/pac_moved.py', 'row join of two port_addr_check runs on the same inputs: moved, new and gone rows'),
    ('sub/gates/tools/symname_check.py', 'scripts/gates/symname_check.py', 'independent .symtab check of every symbol-named definition (<x>_(A|D|E)_<symbol>, src0_D_*)'),
    ('sub/gates/tools/recount_uci.py', 'scripts/gates/recount_uci.py', 'hand-off state recount (decode recount rule)'),
    ('sub/gates/tools/keyed_scan_uci.py', 'scripts/gates/keyed_scan_uci.py', 'keyed-table scan (stack classes)'),
    ('sub/gates/tools/decl_evidence.py', 'scripts/gates/decl_evidence.py', 'evidence for each codeptr declaration'),
    ('sub/gates/tools/classify/plant_uciB.py', 'scripts/gates/plant_uciB.py', 'planted control of the by-role check'),
    ('tools/mk_evidence.py', 'scripts/mk_evidence.py', 'this builder'),
    ('tools/core_check.py', 'scripts/core_check.py', 'records from git that the layer is built in the image-B core: head, merge, build record, shared MANIFEST.md'),
]

# cited tools: name, the lane copy whose bytes are hashed, candidate (commit, tree path) homes searched for those bytes.
# SET: = the extracted start-up set of commit dbb5a97ad14 ($FT, set by the lane env file), so no lane directory name is
# written here
CITED = [
    ('af0m.py', 'SET:frozen/af0m.py.frozen-238598b380f1'),
    ('atable.py (YB12)', 'SET:frozen/atable.py.frozen-42e18a7eef50'),
    ('atable.py (first generation, byte-equal output)', 'tools/frozen-set/atable.py'),
    ('gen_ad2.py', 'SET:frozen/gen_ad2.py.frozen-979c52cd71c6'),
    ('gen_ad1k.py', 'SET:frozen/gen_ad1k.py.frozen-43a0cf0abc67'),
    ('hsform.py (YB01, YB03, YB05 header)', 'tools/frozen-set/hsform.py'),
    ('plantail.py', 'tools/frozen-set/plantail.py'),
    ('codeptr.py', 'SET:frozen/codeptr.py.frozen-12348302dfd2'),
    ('pins.py', 'SET:frozen/pins.py.frozen-4778073f01be'),
    ('keyset.py', 'SET:frozen/keyset.py.frozen-f050b43e480e'),
    ('ifchk.py', 'SET:frozen/ifchk.py.frozen-f5cde600cc18'),
    ('tr0.py', 'SET:frozen/tr0.py.frozen-14f49a0b2243'),
    ('ColA.v (collector)', 'tools/frozen-set/coq/ColA.v'),
    ('ae3i.py', 'PROV:tools/ae3i.py'),
    ('gen_ab1hk.py', 'PROV:tools/gen_ab1hk.py'),
    ('boxb1.py', 'PROV:tools/boxb1.py'),
    ('port_core.py (pg-reloc 0e4e065eab9f)', 'tools/pg-reloc/0e4e065eab9f/port_core.py'),
    ('gen.py (decode, as gen_dec.py)', 'tools/gen_dec.py'),
    ('relocownB.py (decode B)', 'tools/af0mB/relocownB.decode.py'),
    ('colrun.py', 'PROV:tools/colrun.py'),
    ('itabranges.py', 'PROV:tools/itabranges.py'),
    ('replyscratch.py', 'PROV:tools/replyscratch.py'),
    ('kimg_overlap.py', 'sub/gates/tools/kimg_overlap-acfd7418176d.py'),
    ('port_addr_check.py (16f8a030c869)', 'sub/gates/tools/pac/port_addr_check.py'),
    ('port_addr_check.py (cb0e067e3bae)', 'sub/gates/tools/pac-cb0e/port_addr_check.py'),
    ('port_addr_check.py (e165063a0081)', 'sub/gates/tools/pac-e165/port_addr_check.py'),
    ('port_addr_check.py (efa19b81e92b, of record)', 'sub/gates/tools/pac-efa1/port_addr_check.py'),
    ('global_settings.py (v10)', 'GS10'),
    ('ownedcheck.py (352fb92f)', 'sub/gates/tools/ownedcheck-352fb92f/ownedcheck.py'),
    ('shadowcheck.py (542898b2)', 'sub/gates/tools/shadowcheck-542898b2/shadowcheck.py'),
    ('classify.py (by-role check, unit uciB config)', 'sub/gates/tools/classify/classify.py'),
    ('lowbeg.py', 'sub/gates/tools/lowbeg.py'),
    ('acej.py', 'sub/acej/acej.py'),
    ('ycej_json.py (decode B)', 'sub/acej/ycej_json.py'),
    ('mk_top_manifest.py (writer of record of provenance/evidence/MANIFEST.md and MANIFEST)',
     'GIT:4f2904dd062:tools/mk_top_manifest/a0ba0eb66d66/mk_top_manifest.py'),
]
HOMES = [   # (commit, tree prefix) searched in this order for a blob with the cited copy's bytes
    ('dbb5a97ad14', 'tools/startup-set/2026-10-30'),
    ('8cd71d3a4bb', 'tools/startup-set/2026-10-29'),
    ('7f0e4b05267', 'tools/pg-reloc/0e4e065eab9f'),
    ('7eb81ddb186', 'proofs/libreac/fuzz_decode/provenance/startup-gen/B'),
    ('1148f2311f82', 'proofs/libreac/fuzz_decode/provenance/startup-gen/A'),
    ('a8fc5eedae69', 'proofs/reac-repacer/fuzz_uci/provenance'),
    ('534cebca43a', 'proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B'),
    ('463af5742a39', 'tools/global_settings/439f8e3bd463'),
    ('33b974797adf', 'proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/gates/tools'),
    ('bc04213653c8', 'proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/gates/tools'),
    ('4f2904dd062', 'tools/mk_top_manifest/a0ba0eb66d66'),
]
DERIVED = ('.vo', '.vos', '.vok', '.glob', '.aux', '.hex', '.cache', '.pyc', '.pyo', '.gz', '.zip', '.json.gz')
VM_NAME = re.compile(r'\b(?:open-u\d+|disco-\w+|decbox-a\d+-v\d+|ossv-agent-\w+)\b')


def sha256(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def git(*a):
    return subprocess.run(['git', '-C', OVPI] + list(a), check=True, capture_output=True).stdout


def homes_index():
    """sha256 -> (commit, path) for every blob under HOMES (first home wins)."""
    idx = {}
    for commit, prefix in HOMES:
        lines = git('ls-tree', '-r', commit, prefix).decode().splitlines()
        objs = [(l.split()[2], l.split('\t', 1)[1]) for l in lines if ' blob ' in l]
        if not objs:
            continue
        inp = ''.join(o + '\n' for o, _ in objs).encode()
        out = subprocess.run(['git', '-C', OVPI, 'cat-file', '--batch'], input=inp, capture_output=True, check=True).stdout
        pos = 0
        for o, path in objs:
            nl = out.index(b'\n', pos)
            size = int(out[pos:nl].split()[2])
            data = out[nl + 1:nl + 1 + size]
            pos = nl + 1 + size + 1
            idx.setdefault(hashlib.sha256(data).hexdigest(), (commit, path))
    return idx


def lint_shapes():
    """oft lint's own private-data regular expressions, read from the checkout's tools/oft/lint.py."""
    src = open(os.path.join(REPO, 'tools', 'oft', 'lint.py')).read()
    ns = {'re': re}
    for name in ('HOST_PATH', 'PRIVATE_IP', 'PRIVATE_SUFFIXES', 'PRIVATE_HOST_NAME', 'EMAIL', 'PRIVATE_KEY', 'TOKEN'):
        m = re.search(r'^%s = (.*?)(?=^\S)' % name, src, re.M | re.S)
        exec('%s = %s' % (name, m.group(1)), ns)
    m = re.search(r'^REPOSITORY_PATH = (.*?)(?=^\S)', src, re.M | re.S)
    exec('REPOSITORY_PATH = ' + m.group(1), ns)
    return hashlib.sha256(src.encode()).hexdigest(), [(k, ns[k]) for k in ('HOST_PATH', 'PRIVATE_IP', 'PRIVATE_HOST_NAME',
                                                                       'REPOSITORY_PATH', 'EMAIL', 'PRIVATE_KEY', 'TOKEN')]


EXTRA = [('a tmp or mnt path', re.compile(r'(?<![\w.~-])/(?:tmp|mnt)/[\w.@+-]+')),
         ('a build-machine name', VM_NAME), ('a Tailscale name', re.compile(r'(?i)ts' + r'\.net'))]


def scan_text(t, shapes):
    out = []
    for no, line in enumerate(t.split('\n'), 1):
        for what, rx in shapes + EXTRA:
            for m in rx.finditer(line):
                if what == 'REPOSITORY_PATH' and (m.group(1) or m.group(2) or '').lower().rstrip('.') in (
                        'oss-verify', 'oss-verify-proofs', 'rocq-linux-process-semantics', 'rocq-read-file', 'static-asan'):
                    continue
                out.append((no, what, m.group(0)[:60]))
    return out


def run(cmd, env=None, cwd=None):
    r = subprocess.run(cmd, capture_output=True, text=True, env=env, cwd=cwd)
    if r.returncode != 0:
        raise SystemExit('mk_evidence: %s failed rc %d:\n%s' % (cmd[:3], r.returncode, (r.stdout + r.stderr)[-2000:]))
    return r.stdout


VARMAP = None


def var_paths(text):
    """machine paths in a gate log -> the variable that names them (longest value first); then any remaining
    /home /mnt /tmp path is cut to its last two components behind <path>/."""
    global VARMAP
    if VARMAP is None:
        VARMAP = sorted(((v.rstrip('/'), '$' + k) for k, v in os.environ.items()
                         if (k.startswith('UCIB_') or k in ('W', 'WK', 'LT', 'DON', 'DLIB', 'DLIBC', 'S', 'FT', 'PROV',
                                                             'TR', 'TLIB', 'KIT', 'U'))
                         and v.startswith('/') and len(v) > 4), key=lambda kv: -len(kv[0]))
    for v, k in VARMAP:
        text = text.replace(v, k)
    text = re.sub(r'(?<![\w.~$-])/(?:home|mnt|tmp|data|srv|root|Users)/[\w.@+/-]*?([\w.@+-]+/[\w.@+-]+)(?=[\s\'":,)\]]|$)',
                  r'<path>/\1', text)
    # a proof-attempt branch name is internal: replaced by <branch>, the commit sha that follows it is kept
    text = re.sub(r'(?<![\w.-])(?:origin/)?cold/[\w./-]+', '<branch>', text)
    return VM_NAME.sub('<build VM>', text)


# the gate runs the record is built from, in order (gates/logs of the lane; LANE: = the lane's logs/)
GATE_LOGS = [
    ('FINAL: full run on the 19 committed files, port_addr_check e165063a0081 included (G0-G12)', 'run.e165.out'),
    ('FINAL: G7 re-run after the harness fix of its pins --pair input (G0 reads image A\'s AF0m from core f47e2a8927b9)',
     'run.e165.G7.out'),
    ('FINAL: port_addr_check e165063a0081 vs cb0e067e3bae, moved / new / gone rows, GENERATOR-FILL triage, .symtab check',
     'G3e.triage.uciB.log'),
    ('FINAL: the relocation gate re-run on port_addr_check efa19b81e92b, control first (G3g)', 'G3g.out'),
    ('FINAL: port_addr_check e165063a0081 vs efa19b81e92b, moved / new / gone rows, GENERATOR-FILL triage, .symtab check',
     'G3g.triage.uciB.log'),
    ('FINAL: global_settings v10 439f8e3bd463 over the 19 files', 'LANE:gs/v10.uciB19.log'),
    ('FINAL: global_settings v10 over the core\'s lib/Reusable YA0e.v + YA09.v (09ea58a92a88)', 'LANE:gs/v10.core09ea.YA0e-YA09.log'),
    ('FINAL: global_settings v10 control, grant\'s released lib/Reusable YA0e.v + YA09.v (4f87de75d67)',
     'LANE:gs/v10.grantReusable.control.log'),
    ('FINAL: global_settings v8 7897f5fb9f8f over the 19 files', 'LANE:gs/v8.uciB19.log'),
    ('FINAL: Required modules present in the merged tree (09ea58a92a88 + the 19 files)', 'LANE:missing.core09ea.log'),
    ('FINAL: the layer is built in the image-B core: core head, merge, build record, shared MANIFEST.md (core_check.py)',
     'LANE:core_check.f47e.log'),
    ('Earlier: full run on the 19 files before the Require-map changes (G0-G12)', 'run.final.out'),
    ('Earlier: re-run of the gates touching YE37 after the 8-word change (G2 G3 G4 G7 G8 G11)', 'run-8w/run.out'),
    ('Earlier: G11 re-run with a9\'s control texts read from its core commit', 'run-8w/run.G11.out'),
]


def gate_record(dst):
    logs = os.path.join(W, 'sub', 'gates', 'logs')
    keep = re.compile(r'^RESULT |FINDINGS|UNMEASURED|EQUAL|DIFFER|overlapping write bytes|KImg ranges|stated|UNEXPLAINED|'
                      r'GENERATOR-FILL|ACCEPTED|PASS|REFUSED|hull_bound|cells, 0 wrong|UNOWNED|misses|classes|lowbeg|'
                      r'states \d+|mcs|arrival|forbidden|stack_malloc|E2b|rodata_chk|planted|^SUMMARY|^UNION|^TOOL |missing in the trunk|'
                      r'MOVED|NEW |GONE |FLAGGED|FLAG-CLASSES|TRIAGE')
    parts = ['# Gate record: fuzz_uci image B start-up set', '',
             'Written by scripts/mk_evidence.py gate_record() from the gate runs\' own output (the lane\'s gate logs, which stay '
             'on the proof-attempt branch with the generation logs): every RESULT line and the summary lines of each gate, in run order. '
             'A machine path is replaced by the variable that names it (env.example.sh), or cut to `<path>/` and its last two '
             'components; a build-machine name is replaced by `<build VM>`; a proof-attempt branch name by `<branch>` (the '
             'commit sha beside it stays). Harness: scripts/gates/run_gates.sh.', '']
    lane_logs = os.path.join(W, 'logs')
    for title, f in GATE_LOGS:
        p = os.path.join(logs, f) if not f.startswith('LANE:') else os.path.join(lane_logs, f[5:])
        if not os.path.exists(p):
            continue
        lines = [l for l in open(p).read().split('\n') if (f.startswith('LANE:') and l.strip()) or keep.search(l)]
        parts += ['## ' + title, '', '```'] + [var_paths(l)[:400] for l in lines] + ['```', '']
    open(dst, 'w').write('\n'.join(parts))


def main():
    out = os.path.abspath(sys.argv[1])
    if os.path.exists(out):
        shutil.rmtree(out)
    os.makedirs(out)
    roles = []
    # 1. scripts
    for src, dst, role in SCRIPTS:
        d = os.path.join(out, dst)
        os.makedirs(os.path.dirname(d), exist_ok=True)
        shutil.copyfile(os.path.join(W, src), d)
        roles.append((dst, 'script', role))
    # 2. env.example.sh: the variable names of the lane env file, no values
    env_lines = ['# The variables the writers of this slice read (scripts/ucib_env.py documents each UCIB_ one).',
                 '# Values are machine paths; set them for your machine. No value is shipped.']
    for l in open(os.path.join(W, 'env.sh')).read().split('\n'):
        for m in re.finditer(r'(?:^|;\s*)([A-Za-z_][A-Za-z0-9_]*)=', l):
            if l.lstrip().startswith(('#', 'export')):
                continue
            env_lines.append('%s=' % m.group(1))
    env_lines = list(dict.fromkeys(env_lines))
    open(os.path.join(out, 'env.example.sh'), 'w').write('\n'.join(env_lines) + '\nexport ' + ' '.join(
        l[:-1] for l in env_lines if l.endswith('=')) + '\n')
    roles.append(('env.example.sh', 'config', 'every variable name the writers read, without values'))
    # 3. tables, each by re-running its writer
    tdir = os.path.join(out, 'tables')
    os.makedirs(tdir)
    tmp = tempfile.mkdtemp(prefix='ucib-ev-', dir=need('UCIB_LT'))
    env = dict(os.environ)
    run([sys.executable, os.path.join(W, 'tools', 'ucib_yb13.py'), '--out', tmp, '--table',
         os.path.join(tdir, 'yb13.slots.tsv')], env, cwd=need('UCIB_LT'))
    roles.append(('tables/yb13.slots.tsv', 'table', 'YB13.v: cgif token -> fuzz_uci token per slot, occurrences'))
    env2 = dict(env, UCIB_EXITWORK=os.path.join(tmp, 'exitdrv'))
    run([sys.executable, os.path.join(W, 'sub', 'exitdrv', 'gen_exitB.py')], env2, cwd=os.path.join(W, 'sub', 'exitdrv'))
    shutil.copyfile(os.path.join(tmp, 'exitdrv', 'out', 'numerals.md'), os.path.join(tdir, 'exitdrv-numerals.md'))
    roles.append(('tables/exitdrv-numerals.md', 'table', 'YE23 / YD1y / YE37: every numeral, cgif value | kind | '
                  'fuzz_uci value | source'))
    run([sys.executable, os.path.join(W, 'tools', 'af0mB', 'relocownUciB.py')], env, cwd=need('UCIB_AF0MB'))
    shutil.copyfile(os.path.join(need('UCIB_AF0MB'), 'baseaudit.tsv'), os.path.join(tdir, 'af0m-base-audit.tsv'))
    roles.append(('tables/af0m-base-audit.tsv', 'table', 'YF0m base: each donor Tfib_owned_static row, its key and '
                  'its fuzz_uci row (class b kept / c regenerated / d dropped)'))
    adds = run([sys.executable, os.path.join(W, 'tools', 'af0mB', 'addsB.py'),
                os.path.join(need('UCIB_AF0MB'), 'base.patched.YF0m.v')], env)
    open(os.path.join(tdir, 'af0m-adds.txt'), 'w').write(adds)
    roles.append(('tables/af0m-adds.txt', 'table', 'YF0m --add cells: decode B\'s list mapped by name, each row\'s '
                  'fate and reason'))
    tsv = os.path.join(W, 'sub', 'gates', 'logs', 'G3b.pac-cb0e.uciB.tsv')
    fill = run([sys.executable, os.path.join(W, 'sub', 'gates', 'tools', 'pac_fill.py'), tsv,
                os.path.join(TLIB, 'B', 'YF0m.v'), os.path.join(need('UCIB_LT'), 'donorlib', 'proofs', 'cgif',
                                                                 'cgif_file_fuzzer', 'lib', 'YF0m.v'),
                need('UCIB_UB'), os.path.join(W, 'work', 'nm', 'uciB.nmS.txt'), need('UCIB_CB'),
                os.path.join(need('UCIB_LT'), 'cgifB.recovered.nm')], env)
    open(os.path.join(tdir, 'pac-fill-triage.txt'), 'w').write(var_paths(fill))
    roles.append(('tables/pac-fill-triage.txt', 'table', 'every GENERATOR-FILL row of port_addr_check cb0e067e3bae '
                  'with its measured reason (0 unexplained)'))
    shutil.copyfile(os.path.join(W, 'work', 'gen', 'YCej.universe.json'), os.path.join(tdir, 'YCej.universe.json'))
    roles.append(('tables/YCej.universe.json', 'table', 'the allocation-trace universe of YCej.v (ycej_json.py, cited); '
                  'af0m reads DRV_TRACES from it'))
    shutil.rmtree(tmp)
    # 4. gate record
    os.makedirs(os.path.join(out, 'gates'))
    gate_record(os.path.join(out, 'gates', 'GATE-RECORD.md'))
    roles.append(('gates/GATE-RECORD.md', 'gate record', 'every gate\'s RESULT and summary lines, controls first'))
    # 5. cited tools
    idx = homes_index()
    cited = []
    prov = os.path.join(TLIB, '..', 'provenance', 'startup-gen', 'B')
    for name, lane in CITED:
        if lane.startswith('GIT:'):
            commit, path = lane[4:].split(':', 1)
            h = hashlib.sha256(git('show', '%s:%s' % (commit, path))).hexdigest()
        else:
            p = (os.path.join(prov, lane[5:]) if lane.startswith('PROV:') else
                 os.path.join(need('FT'), lane[4:]) if lane.startswith('SET:') else
                 os.path.join(need('UCIB_LT'), 'gs10v', 'tools', 'global_settings', '439f8e3bd463', 'global_settings.py') if lane == 'GS10'
                 else os.path.join(W, lane))
            if not os.path.exists(p):
                raise SystemExit('mk_evidence: cited copy missing: ' + lane)
            h = sha256(p)
        home = idx.get(h)
        cited.append((name, h, home))
    # 6. manifest
    lintsha, shapes = lint_shapes()
    man = ['# provenance/evidence/startup-B: fuzz_uci image-B start-up set (lib/B, 19 files)', '',
           'Written by scripts/mk_evidence.py; not edited by hand. What a reader needs to re-derive the numbers of '
           'lib/B/{YB01,YB03,YB05,YB12,YB13,YB1h,YB1k,YB1l,YB1m,YB1v,YCej,YD1k,YD1y,YD2i,YD2j,YE23,YE37,YE3i,YF0m}.v: '
           'the writers of record, the per-value tables and the gate record. Generation logs are not here.', '',
           'Pipeline of every file: its writer (below) -> scripts/nsB.py (module paths + header rule) -> pins.py stamp '
           '(10 files) -> lib/B. Re-running the pipeline reproduces all 19 committed files byte for byte.', '',
           '## Files', '', '| file | kind | role |', '|---|---|---|']
    man += ['| `%s` | %s | %s |' % r for r in sorted(roles)]
    man += ['', '## Cited tools (not shipped: their text carries host-path patterns and would fail the lint)', '',
            'Fetch the exact copy with `git show <commit>:<path>`; the sha256 is of that copy.', '',
            '| tool | sha256 | commit | path |', '|---|---|---|---|']
    for name, h, home in cited:
        man.append('| %s | `%s` | %s | %s |' % (name, h, home[0] if home else '-', ('`%s`' % home[1]) if home else
                                                 'not in a searched commit'))
    # 7. checks
    findings, n = [], 0
    for dp, _, fs in os.walk(out):
        for f in sorted(fs):
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, out)
            n += 1
            if f.endswith(DERIVED):
                findings.append((rel, 0, 'a derived file', f))
                continue
            data = open(p, 'rb').read()
            if b'\0' in data[:8192]:
                findings.append((rel, 0, 'a binary file', f))
                continue
            for no, what, tok in scan_text(data.decode('utf-8', 'replace'), shapes):
                findings.append((rel, no, what, tok))
    man += ['', '## Checks run by the builder', '',
            '%d files; oft lint private-data shapes (tools/oft/lint.py sha256 %s: HOST_PATH, PRIVATE_IP, '
            'PRIVATE_HOST_NAME, REPOSITORY_PATH, EMAIL, PRIVATE_KEY, TOKEN) plus /tmp and /mnt paths, build-machine '
            'names, Tailscale names, derived suffixes and binary content: %d findings.' % (n + 1, lintsha[:12], len(findings))]
    open(os.path.join(out, 'MANIFEST.md'), 'w').write('\n'.join(man) + '\n')
    for rel, no, what, tok in findings:
        print('FINDING %s:%d %s %s' % (rel, no, what, tok))
    print('mk_evidence: %d files, %d cited tools (%d located in a commit), %d findings' % (
        n + 1, len(cited), sum(1 for c in cited if c[2]), len(findings)))
    sys.exit(1 if findings else 0)


if __name__ == '__main__':
    main()
