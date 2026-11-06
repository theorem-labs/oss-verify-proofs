#!/usr/bin/env python3
"""wire_ab1hk_drive.py -- runs gen_ab1hk.py (imported UNCHANGED, sha256 0f51cb9cdb18...; its directory is $GEN_AB1HK_DIR)
for reac-repacer/fuzz_wire image B (asan-ubsan): the B twin of fuzz_decode B's dec_ab1hk_drive.py (sha256 19a5fd9f0976, not in the published tree).
It sets gen_ab1hk's configuration globals only:

  CGIF   the donor images ($CB's directory; sha256 asserted equal to the tool's csha)
  DONOR  the donor text's ref: recipes commit 25e3d17bdb50 (the donor of record; for YB1h / YB1k /
         YB1l the blobs equal c8557374ad2e's, asserted below)
  PAU / TWIN / SIDE['B']: fuzz_wire's pinned asan-ubsan image + unstripped twin ($UB / $UBs), its x_envscan / x_pnscan
  RENAME []: the files are written with the donor's module paths; port_core's own rename_text (tools/nsB.py)
         (tools/nsW.py)
         rewrites them afterwards, so the per-image / kernel split is port_core's B convention.

  control --outdir DIR   target = cgif_file_fuzzer.asan-ubsan itself: DIR/YB1h.cgif.v, DIR/YB1k.cgif.v (gen_h / gen_k
                         text, before header and rename) for a byte diff with cgif's released lib/YB1h.v / YB1k.v.
                         cgif has no unstripped twin here: gen_ab1hk.sym answers with the tool's own cgif constants
                         (SIDE['B']['gmuva'] 0x64fac, GMUVA_SIZE 280), exactly as dec_ab1hk_drive.py does.
  wire --outdir DIR --envscan HEX --pnscan HEX
                         target = fuzz_wire.asan-ubsan + twin: DIR/YB1h.v, DIR/YB1k.v, DIR/YB1l.v (donor text,
                         module paths only: cgif's YB1l carries no image numeral).
"""
import argparse, os, re, subprocess, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.environ['GEN_AB1HK_DIR'])
import gen_ab1hk as G  # noqa: E402

G.CGIF = os.environ['CB'][:-len('asan-ubsan')]
G.DONOR = '25e3d17bdb50'
CGIF_B = G.CGIF + 'asan-ubsan'
CGIF_SHA = '1c29845fe6058de6e1dbf3f6ec6abd566ea612d76b65ea5435d7ff77c63e08ef'
U_BIN = os.environ['UB'][:-len('asan-ubsan')]
U_TWIN = os.environ['UBs'][:-len('asan-ubsan')]
U_SHA = 'af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6'
U_TWIN_SHA = '51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3'


def blob(ref, f):
    return subprocess.run(['git', '-C', G.HUB, 'rev-parse', '%s:%s%s.v' % (ref, G.DP, f)], check=True,
                          capture_output=True, text=True).stdout.strip()


def same_blobs():
    for f in ('YB1h', 'YB1k', 'YB1l'):
        a, b = blob('25e3d17bdb50', f), blob('c8557374ad2e', f)
        assert a == b, (f, a, b)
    print('donor blobs YB1h / YB1k / YB1l: 25e3d17bdb50 == c8557374ad2e')


def control(outdir):
    same_blobs()
    s = dict(G.SIDE['B'])
    ce, cp = s['envscan'][0], s['pnscan'][0]
    s.update(sha=CGIF_SHA, envscan=(ce, ce), pnscan=(cp, cp))
    assert G.sha(CGIF_B) == CGIF_SHA == s['csha']
    G.RENAME = []
    G.sym = lambda twin, name: (s['gmuva'], G.GMUVA_SIZE) if name == G.GMUVA else None
    cimg, img = G.Img(CGIF_B), G.Img(CGIF_B)
    h, hi = G.gen_h(s, cimg, img)
    k, ki = G.gen_k(s, cimg, img, None)
    for txt, name in ((h, 'YB1h'), (k, 'YB1k')):
        open(os.path.join(outdir, name + '.cgif.v'), 'w').write(txt)
    print('control cgif B: YB1h %s; YB1k %s' % (hi, ki))


def wire(outdir, envscan, pnscan):
    same_blobs()
    s = dict(G.SIDE['B'])
    s.update(sha=U_SHA, twin=U_TWIN_SHA, envscan=(s['envscan'][0], envscan), pnscan=(s['pnscan'][0], pnscan))
    G.PAU, G.TWIN, G.RENAME = U_BIN, U_TWIN, []
    ip, tp, cp = G.PAU + s['b'], G.TWIN + s['b'], G.CGIF + s['b']
    assert G.sha(ip) == s['sha'], G.sha(ip)
    assert G.sha(tp) == s['twin'], G.sha(tp)
    assert G.sha(cp) == s['csha'], G.sha(cp)
    cimg, img = G.Img(cp), G.Img(ip)
    h, hi = G.gen_h(s, cimg, img)
    k, ki = G.gen_k(s, cimg, img, tp)
    out = []
    for txt, path, what in ((h, s['h'], 'its image constants (segments_reserved, their sum, segment 2/3 sizes, rw '
                             'window) recomputed from'), (k, s['k'], 'its GetMaxUserVirtualAddress addresses moved to '
                             'that function in')):
        line = ('(* Modified by Theorem Labs: generated from proofs/cgif/cgif_file_fuzzer/lib/%s.v (commit '
                '25e3d17bdb50), with its module paths changed and %s reac-repacer/fuzz_wire\'s %s image (sha256 '
                '%s) by gen_ab1hk.py (sha256 0f51cb9cdb18); every fetched word checked equal. *)') % (path, what, s['b'],
                                                                                                  s['sha'])
        out.append((path, G.header(txt, line)))
    lt = G.donor('YB1l')
    assert not re.search(r'0x[0-9a-f]+', lt), 'YB1l carries a hex numeral; the namespace-only rule does not hold'
    line = ('(* Modified by Theorem Labs: generated from proofs/cgif/cgif_file_fuzzer/lib/YB1l.v (commit '
            '25e3d17bdb50), module paths changed only: the file carries no image numeral (SEALEDTOP_PC / '
            'SEALEDTOP_END and xn_sealedtop are YB1k\'s). *)')
    out.append(('YB1l', G.header(lt, line)))
    for path, txt in out:
        open(os.path.join(outdir, os.path.basename(path) + '.v'), 'w').write(txt)
    print('gen_ab1hk B wire: YB1h %s; YB1k %s; YB1l namespaces only' % (hi, ki))


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['control', 'wire'])
    ap.add_argument('--outdir', required=True)
    ap.add_argument('--envscan', type=lambda x: int(x, 16))
    ap.add_argument('--pnscan', type=lambda x: int(x, 16))
    a = ap.parse_args()
    if a.mode == 'control':
        control(a.outdir)
    else:
        wire(a.outdir, a.envscan, a.pnscan)
