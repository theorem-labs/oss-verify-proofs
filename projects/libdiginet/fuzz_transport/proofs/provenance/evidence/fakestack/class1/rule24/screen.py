#!/usr/bin/env python3
"""Rule-24 screen (compare first, then choose): every released donor of astack_malloc_realizes at class 1 / 2 found by
lookup.sh whose pinned image is on this box, compared range by range and whole function by whole function (../clscmp.py,
cmpkit 86da41d3ef68) against fuzz_transport's image of the same build (the donor build is the one whose
__asan_stack_malloc_<class> starts a range of the table). One output directory per candidate under screen/, and one
line per candidate on stdout (screen.out):
  pin            the donor file's sha256 against its harness.yaml at REF
  PASS / FAIL    clscmp.py's verdict (every range paired and clean; the FAIL lines say why)
  range / fn     differing words (pc-relative only: real and unmeasured are 0 in every PASS) over all walked ranges /
                 over the whole functions holding them
  common         the same two counts over the 8 functions every candidate walks: __asan_stack_malloc_<class> and its 7
                 helpers (__interceptor___tls_get_addr, __tls_get_addr, GetCurrentThread, AsanTSDGet, pthread_getspecific,
                 DTLS_on_tls_get_addr, MemToShadow), so that candidates with different tables compare like for like
usage: HUB=<hub> AGENTS=<pipeline stores> LIBREAC_V190=<libreac v1.9.0 images> CGIF_BIN=<cgif pins> CGIF_TWINS=<cgif twins>
       PINS=<fuzz_transport port2 pins> screen.py > screen.out"""
import os, re, subprocess, sys, hashlib, yaml
from elftools.elf.elffile import ELFFile
HERE = os.path.dirname(os.path.abspath(__file__))
# the released set the lookup read (ref.txt): origin/ossv/recipes at lookup time; every unit at projects/P/U/proofs/lib
E = os.environ
HUB = E['HUB']; REF = open(os.path.join(HERE, 'ref.txt')).read().strip()[:12]
CMP = os.path.join(HERE, '..', 'clscmp.py')
OUT = os.path.join(HERE, 'screen')
COMMON = ('__interceptor___tls_get_addr', '__tls_get_addr', '_ZN6__asan16GetCurrentThreadEv', '_ZN6__asan10AsanTSDGetEv',
          '__pthread_getspecific', '_ZN11__sanitizer20DTLS_on_tls_get_addrEPvS0_mm', '_ZN6__asanL11MemToShadowEm')
P = E['AGENTS'] + '/pau-pipeline'
N = E['AGENTS'] + '/pau-pipeline-next3'
V = E['LIBREAC_V190']
IMG = {
    'libreac/fuzz_grant': (P + '/libreac/bin/fuzz_grant', P + '/libreac/unstripped/fuzz_grant'),
    'libreac/fuzz_disco': (P + '/libreac/bin/fuzz_disco', P + '/libreac/unstripped/fuzz_disco'),
    'libreac/fuzz_scene': (P + '/libreac/bin/fuzz_scene', P + '/libreac/unstripped/fuzz_scene'),
    'libreac/fuzz_knock': (P + '/libreac/bin/fuzz_knock', P + '/libreac/unstripped/fuzz_knock'),
    'libreac/fuzz_pcap': (V + '/s/fuzz_pcap', V + '/x/unstripped/fuzz_pcap'),
    'libreac/fuzz_ctrl': (V + '/s/fuzz_ctrl', V + '/x/unstripped/fuzz_ctrl'),
    'plugin-hostd/fuzz_command': (P + '/plugin-hostd/bin/fuzz_command', P + '/plugin-hostd/unstripped/fuzz_command'),
    'cgif/cgif_file_fuzzer': (E['CGIF_BIN'] + '/cgif/bin/cgif_file_fuzzer',
                              E['CGIF_TWINS'] + '/cgif_file_fuzzer'),
    'reac-pw/fuzz_pin': (N + '/reac-pw/result/bin/fuzz_pin', N + '/reac-pw/result/unstripped/fuzz_pin'),
    'reac-repacer/fuzz_uci': (N + '/reac-repacer/result/bin/fuzz_uci', N + '/reac-repacer/result/unstripped/fuzz_uci'),
}
# cgif/cgif_rgb_fuzzer (YF97.v / YF99.v, YF9s.v / YF9u.v) is not screened: no file of its pins (0d102754e9d2 /
# ed3b5ad58f4b) in the pipeline stores, the internal image store, or its delivery directories on this box
TP = E['PINS']
TGT = {'asan': (TP + '/stripped/fuzz_transport.asan', TP + '/unstripped/fuzz_transport.asan'),
       'asan-ubsan': (TP + '/stripped/fuzz_transport.asan-ubsan', TP + '/unstripped/fuzz_transport.asan-ubsan')}
# (unit, class, table file): the code table the class's contract file walks (grep'd Require / tbl_fs use)
CANDS = [
    ('libreac/fuzz_grant', 1, 'A/Rt/AF0r.v'), ('libreac/fuzz_grant', 2, 'A/Rt/AF0r.v'),
    ('libreac/fuzz_grant', 1, 'B/Rt/YF0r.v'), ('libreac/fuzz_grant', 2, 'B/Rt/YF0r.v'),
    ('libreac/fuzz_disco', 1, 'A/AF0r.v'), ('libreac/fuzz_disco', 2, 'A/AF0r.v'),
    ('libreac/fuzz_disco', 1, 'Reusable/YF0r.v'), ('libreac/fuzz_disco', 2, 'Reusable/YF0r.v'),
    ('libreac/fuzz_scene', 1, 'A/AF0r.v'), ('libreac/fuzz_scene', 2, 'A/AF0r.v'),
    ('libreac/fuzz_scene', 1, 'AU/YF0r.v'), ('libreac/fuzz_scene', 2, 'AU/YF0r.v'),
    ('libreac/fuzz_knock', 1, 'A/AF0r.v'), ('libreac/fuzz_knock', 1, 'AU/YF0r.v'),
    ('libreac/fuzz_pcap', 1, 'A/AF0r.v'), ('libreac/fuzz_pcap', 1, 'Reusable/YF0r.v'),
    ('libreac/fuzz_ctrl', 1, 'A/Rt/StackMalloc1Tbl.v'), ('libreac/fuzz_ctrl', 2, 'A/Rt/StackMalloc2Tbl.v'),
    ('libreac/fuzz_ctrl', 1, 'B/Rt/StackMalloc1Tbl.v'), ('libreac/fuzz_ctrl', 2, 'B/Rt/StackMalloc2Tbl.v'),
    ('plugin-hostd/fuzz_command', 1, 'A/Rt/RtSM1T.v'), ('plugin-hostd/fuzz_command', 1, 'B/Rt/RtSM1T.v'),
    ('cgif/cgif_file_fuzzer', 1, 'A/AF0r.v'), ('cgif/cgif_file_fuzzer', 2, 'A/AF0r.v'),
    ('cgif/cgif_file_fuzzer', 1, 'YF0r.v'), ('cgif/cgif_file_fuzzer', 2, 'YF0r.v'),
    ('reac-pw/fuzz_pin', 1, 'A/AF0r.v'), ('reac-pw/fuzz_pin', 1, 'AU/YF0r.v'),
    ('reac-repacer/fuzz_uci', 1, 'A/Rt/AF0r.v'), ('reac-repacer/fuzz_uci', 1, 'B/Rt/YF0r.v'),
]


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def entry(path, cls):
    st = ELFFile(open(path, 'rb')).get_section_by_name('.symtab')
    return {s['st_value'] for s in st.iter_symbols() if s.name == '__asan_stack_malloc_%d' % cls}


os.makedirs(OUT, exist_ok=True)
model = os.path.join(OUT, 'empty-model.txt'); open(model, 'w').write('')
rows = []
for unit, cls, tf in CANDS:
    hy = yaml.safe_load(subprocess.check_output(['git', '-C', HUB, 'show', '%s:projects/%s/harness.yaml' % (REF, unit)]))
    txt = subprocess.check_output(['git', '-C', HUB, 'show', '%s:projects/%s/proofs/lib/%s' % (REF, unit, tf)]).decode()
    starts = {int(s, 16) for s in re.findall(r'\((0x[0-9a-f]+),\s*\d+%nat\)', txt)}
    sd, ud = IMG[unit]
    u = unit.split('/')[1]
    build = None
    for b in ('asan', 'asan-ubsan'):
        if entry(os.path.join(ud, '%s.%s' % (u, b)), cls) & starts:
            build = b if build is None else 'AMBIG'
    if build in (None, 'AMBIG'):
        # knock / pin / uci: both builds share the body address; the table's other starts decide
        hits = {b: len(starts & {s['st_value'] for s in ELFFile(open(os.path.join(ud, '%s.%s' % (u, b)), 'rb'))
                                 .get_section_by_name('.symtab').iter_symbols() if s['st_info']['type'] == 'STT_FUNC'})
                for b in ('asan', 'asan-ubsan')}
        build = max(hits, key=hits.get) if len(set(hits.values())) > 1 else 'AMBIG'
    if build == 'AMBIG':
        rows.append((unit, cls, tf, '?', 'donor build not determined')); continue
    dp, du = os.path.join(sd, '%s.%s' % (u, build)), os.path.join(ud, '%s.%s' % (u, build))
    pin_ok = sha(dp) == hy['builds'][build]['sha256']
    img = 'A' if build == 'asan' else 'B'
    out = os.path.join(OUT, '%s-%s-c%d-%s' % (u, tf.replace('/', '_'), cls, img))
    r = subprocess.run([sys.executable, CMP, '--hub', HUB, '--ref', REF, '--src', unit, '--cls', str(cls), '--img', img,
                        '--tables', tf + ':fs_ranges', '--reloc', tf, '--model', model, '--donor', dp, du,
                        '--target', *TGT[build], '--out', out], capture_output=True, text=True)
    tsv = os.path.join(out, 'class%d-%s.tsv' % (cls, img))
    pc = fpc = cpc = cfpc = nr = nc = 0
    if os.path.exists(tsv):
        for line in open(tsv).read().split('\n')[1:]:
            f = line.split('\t')
            if len(f) > 15:
                m = re.match(r'\S+ \((\d+), (\d+), (\d+)\) (\d+)', f[15])
                nr += 1; pc += int(f[11]); fpc += int(m.group(1))
                if f[3] in COMMON or f[3] == '__asan_stack_malloc_%d' % cls:
                    nc += 1; cpc += int(f[11]); cfpc += int(m.group(1))
    fails = [l for l in r.stdout.split('\n') if l.startswith('FAIL')]
    rows.append((unit, cls, tf, build, 'pin %s; %s; %d ranges: range %d, fn %d; common (%d of 8): range %d, fn %d%s'
                 % ('OK' if pin_ok else 'MISMATCH', 'PASS' if r.returncode == 0 else 'FAIL', nr, pc, fpc, nc, cpc, cfpc,
                    ('; ' + ' | '.join(fails)) if fails else '')))
for row in rows:
    print('\t'.join(map(str, row)))
