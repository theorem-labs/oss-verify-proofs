#!/usr/bin/env python3
"""cmpkit-sm1.py KITDIR OUTDIR: re-run this slice's 13 function pairs (BYTECMP.md, fuzz_grant.asan vs fuzz_uci.asan)
on the comparison kit 4bbd3a74be89 (tools/cmpkit/4bbd3a74be89 at commit 3c3e62ee278), with its controls.

KITDIR must hold exactly the kit's seven pinned files and its SHA256SUMS (sha256(SHA256SUMS)[:12] = 4bbd3a74be89); this
script lives outside it and adds no compare: every verdict is the kit's strictcmp2 (tcmp per function pair).
  twins.out          drvcmp.py twins: each side's unstripped twin against its stripped pin
  pairs.out          strictcmp2.py cmp over the 12 pairs named once in each image (the kit's own command line)
  pairs-by-address.out  strictcmp2's tcmp on the two pairs a name does not fix: the __asan::MemToShadow copy
                     stack_malloc_1 +0x144 calls (5 copies of the name in each image; fsym takes the first), and the 2
                     words of RegisterCommonFlags at +0x358 that AF0r.v's code table covers
  region.out         the one target strictcmp2 reports different, measured: both regions' lengths and first difference
  fulllist.out       strictcmp2's tcmp called directly on all 13 pairs: the full differing-target list and acceptance
                     counts per pair, checked identical to the printed lists
  control-N.out      strictcmp2.py cmp of the planted function on a FILE copy of the target twin with one change
  summary.out        one line per pair: EQUAL (bytecmp verdict EQUAL or EQUAL-mod-pcrel, target-differ 0) or NOT EQUAL
env: P (libreac's pinned image tree), R (reac-repacer's). Host paths in the outputs are written <P>, <R>, <kit>, <out>."""
import hashlib, importlib.util, os, shutil, subprocess, sys

sys.dont_write_bytecode = True   # nothing is written into KITDIR (no __pycache__), here or in the kit's subprocesses
os.environ['PYTHONDONTWRITEBYTECODE'] = '1'

KIT, OUT = (os.path.abspath(x) for x in sys.argv[1:3])
P, R = os.environ['P'], os.environ['R']
KIT_ID = '4bbd3a74be89'
MEMBERS = {'strictcmp2.py', 'drvcmp.py', 'repin_check-4c05cadaeba3.py', 'bytecmp-1480ca2faea0.py', 'closure_strict2.py',
           'paircl.py', 'jtcheck.py'}
GA, UA = P + '/unstripped/fuzz_grant/fuzz_grant.asan', R + '/result/unstripped/fuzz_uci/fuzz_uci.asan'
GS, US = P + '/bin/fuzz_grant/fuzz_grant.asan', R + '/result/bin/fuzz_uci/fuzz_uci.asan'
NAMED = ['__asan_stack_malloc_1', '__interceptor_trampoline___tls_get_addr', '___interceptor___tls_get_addr',
         '_ZN6__asan18TryAsanInitFromRtlEv', '__tls_get_addr', '_ZN6__asan16GetCurrentThreadEv', '_ZN6__asan10AsanTSDGetEv',
         '__pthread_getspecific', '_ZN11__sanitizer20DTLS_on_tls_get_addrEPvS0_mm',
         '_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE', '_ZN6__asan9FakeStack2GCEm',
         '_ZN6__asan10AsanThread32AsyncSignalSafeLazyInitFakeStackEv']
RCF = '_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE'
# (number, function, target-twin address, bytes, what it tests)
CONTROLS = [
    (1, '__asan_stack_malloc_1', 0x3c24c, 'b368e600', 'an instruction word: `or` for the `and` at FS_LOOP'),
    (2, '__asan_stack_malloc_1', 0x3c280, 'eff0c102', 'a re-pointed call: the donor\'s own jal word at the GetCurrentThread call'),
    (3, '_ZN6__asan18TryAsanInitFromRtlEv', 0x58454, '13040500', 'the donor\'s own `addi s0, a0, 0` at +0x10 (auipc pair to asan_inited)'),
    (4, '__asan_stack_malloc_1', 0x97d00, '02', 'the module id of the .got tls_index stack_malloc_1 +0x18 takes, 1 -> 2'),
    (5, '__asan_stack_malloc_1', 0x97d00, 'b8c1030000000000', 'the same .got cell holding __asan_stack_malloc_1\'s address'),
    (6, '_ZN6__asan10AsanTSDGetEv', 0x117a4, '54', 'one byte of the C string AsanTSDGet +0x2c takes ("((tsd_key_inited)) != (0)", t -> T)'),
]


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def neutral(s):
    return s.replace(KIT, '<kit>').replace(OUT, '<out>').replace(P, '<P>').replace(R, '<R>')


def run(args):
    r = subprocess.run([sys.executable] + args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    return neutral(r.stdout) + 'rc=%d\n' % r.returncode


def put(name, text):
    open(os.path.join(OUT, name), 'w').write(text)


def verdict_rows(text):
    """(fn, pair, bytecmp verdict, unmeasured, target-differ) of each pair row of strictcmp2's cmp output"""
    out = []
    for l in text.splitlines():
        f = l.split('\t')
        if len(f) >= 12 and f[0] not in ('fn', 'CSTR') and not f[0].startswith('#'):
            out.append((f[0], f[1], f[6], f[9], f[11]))
        elif len(f) >= 7 and f[6] in ('ABSENT', 'SIZE'):
            out.append((f[0], f[1], f[6], '', ''))
    return out


def equal(v, um, td):
    return v in ('EQUAL', 'EQUAL-mod-pcrel') and td == '0'


have = set(os.listdir(KIT))
if have != MEMBERS | {'SHA256SUMS'}:
    sys.exit('cmpkit-sm1: %s holds %s, not exactly the kit files' % (KIT, sorted(have ^ (MEMBERS | {'SHA256SUMS'}))))
for l in open(os.path.join(KIT, 'SHA256SUMS')):
    h, f = l.split()
    if sha(os.path.join(KIT, f)) != h:
        sys.exit('cmpkit-sm1: %s does not match SHA256SUMS' % f)
if sha(os.path.join(KIT, 'SHA256SUMS'))[:12] != KIT_ID:
    sys.exit('cmpkit-sm1: SHA256SUMS is not kit %s' % KIT_ID)
os.makedirs(OUT, exist_ok=True)
S2 = os.path.join(KIT, 'strictcmp2.py')
put('twins.out', '# kit %s: SHA256SUMS checked, %s holds exactly its files\n' % (KIT_ID, '<kit>') +
    run([os.path.join(KIT, 'drvcmp.py'), 'twins', GS, GA, US, UA]))
pairs = run([S2, 'cmp', ','.join(NAMED), 'GA=' + GA, 'UA=' + UA, 'GA:UA'])
put('pairs.out', pairs)

spec = importlib.util.spec_from_file_location('strictcmp2_kit', S2)
K = importlib.util.module_from_spec(spec)
spec.loader.exec_module(K)
I = {'GA': K.Img(GA), 'UA': K.Img(UA)}


def jal_target(img, a):
    w = int.from_bytes(K.frd(img, a, 4), 'little')
    assert w & 0x7f == 0x6f, hex(w)
    imm = ((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11 | ((w >> 21) & 0x3ff) << 1
    return a + (imm - (1 << 21) if imm & (1 << 20) else imm)


def row(label, a1, a2, n):
    """strictcmp2's own tcmp on one pair given by address, printed in its cmp row format"""
    fb = []
    v, c, t3, diff = K.tcmp(I, 'GA', a1, 'UA', a2, n, fb)
    lines = ['%s\tGA:UA\t%#x\t%#x\t%d\t%d\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s'
             % (label, a1, a2, n, n, v, c[0] if c else '', c[1] if c else '', c[2] if c else '', t3,
                diff if diff else 0, K.fb_text(fb),
                ' '.join('%s@%#x|%#x=%r' % (o, x1, x2, s) for k, o, x1, x2, s in fb if k == 'cstr'))]
    return lines + K.cstr_rows(label, 'GA:UA', fb)


sg, su = I['GA'].fsym('__asan_stack_malloc_1'), I['UA'].fsym('__asan_stack_malloc_1')
mg, mu = jal_target(I['GA'], sg[0] + 0x144), jal_target(I['UA'], su[0] + 0x144)
zg = [z for v, z, t in I['GA'].byname['_ZN6__asanL11MemToShadowEm'] if v == mg][0]
zu = [z for v, z, t in I['UA'].byname['_ZN6__asanL11MemToShadowEm'] if v == mu][0]
rg, ru = I['GA'].fsym(RCF), I['UA'].fsym(RCF)
byaddr = ['# strictcmp2 tcmp by address (kit %s); columns as pairs.out' % KIT_ID,
          '# _ZN6__asanL11MemToShadowEm: the copy the jal at __asan_stack_malloc_1 +0x144 lands on (%#x / %#x); copies '
          'in GA %s, in UA %s' % (mg, mu, [hex(v) for v, z, t in I['GA'].byname['_ZN6__asanL11MemToShadowEm']],
                                  [hex(v) for v, z, t in I['UA'].byname['_ZN6__asanL11MemToShadowEm']])]
byaddr += row('_ZN6__asanL11MemToShadowEm@stack_malloc_1+0x144', mg, mu, zg) if zg == zu else \
    ['_ZN6__asanL11MemToShadowEm@stack_malloc_1+0x144\tGA:UA\t%#x\t%#x\t%d\t%d\tSIZE' % (mg, mu, zg, zu)]
byaddr += ['# %s +0x358, 8 bytes: the 2 words AF0r.v fs_ranges covers ((0x61ccc, 2) / (0x60904, 2))' % RCF]
byaddr += row(RCF + '+0x358[8]', rg[0] + 0x358, ru[0] + 0x358, 8)
put('pairs-by-address.out', '\n'.join(byaddr) + '\n')

reg = ['# the targets strictcmp2 reports different in pairs.out / pairs-by-address.out, measured with its own region()']
for f, pr, v, um, td in verdict_rows(pairs):
    if td not in ('0', ''):
        for d in eval(td):   # the cmp row prints the difference list as a Python literal
            off = int(d[0], 16)
            s1, s2 = I['GA'].fsym(f), I['UA'].fsym(f)
            t1, t2 = K.targets(s1[0], K.frd(I['GA'], s1[0], s1[1])), K.targets(s2[0], K.frd(I['UA'], s2[0], s2[1]))
            w = K.bc_words(K.frd(I['GA'], s1[0], s1[1]))
            k = [i for i, x in enumerate(w) if x[0] == off][0]
            x1, x2 = t1[k][1], t2[k][1]
            r1, r2 = K.region(I['GA'], x1), K.region(I['UA'], x2)
            fd = next((i for i in range(min(len(r1), len(r2))) if r1[i] != r2[i]), None)
            reg.append('%s +%s: %s, targets %#x / %#x (%s / %s); region lengths %d / %d; first 32 bytes %s / %s; first '
                       'differing byte at region offset %s; C string at the target: %r / %r'
                       % (f, d[0], d[3], x1, x2, I['GA'].sec(x1), I['UA'].sec(x2), len(r1), len(r2), r1[:32].hex(),
                          r2[:32].hex(), fd, K.cstring(I['GA'], x1), K.cstring(I['UA'], x2)))
put('region.out', '\n'.join(reg) + '\n')

# the FULL lists, from strictcmp2's tcmp called directly (its cmp command prints the whole list too; closure_strict2
# and paircl print only the first 2): every differing / unmeasured target and every acceptance, per pair
full = ['# kit %s: strictcmp2.tcmp called directly on each of the 13 pairs; per pair: the number of differing or '
        'unmeasured targets and each of them, the acceptances by kind (each C-string acceptance is also a CSTR row of '
        'pairs.out / pairs-by-address.out), and whether the list equals the one the record prints' % KIT_ID]
printed = {f: td for f, pr, v, um, td in verdict_rows(pairs)}
printed.update({f: td for f, pr, v, um, td in verdict_rows(open(os.path.join(OUT, 'pairs-by-address.out')).read())})
for label, a1, a2, n in [(f, I['GA'].fsym(f)[0], I['UA'].fsym(f)[0], I['GA'].fsym(f)[1]) for f in NAMED] + \
        [('_ZN6__asanL11MemToShadowEm@stack_malloc_1+0x144', mg, mu, zg), (RCF + '+0x358[8]', rg[0] + 0x358, ru[0] + 0x358, 8)]:
    fb = []
    v, c, t3, diff = K.tcmp(I, 'GA', a1, 'UA', a2, n, fb)
    kinds = {}
    for k, *_ in fb:
        kinds[k] = kinds.get(k, 0) + 1
    same = (str(diff) if diff else '0') == printed.get(label)
    full.append('%s\tverdict %s\tdiffering-or-unmeasured %d\tacceptances %s\tprinted list identical: %s'
                % (label, v, len(diff), dict(sorted(kinds.items())), same))
    for d in diff:
        full.append('  differs: %r' % (d,))
put('fulllist.out', '\n'.join(full) + '\n')

summ = ['# kit %s, strictcmp2 16982e3ef42b: one line per pair (EQUAL = bytecmp verdict EQUAL / EQUAL-mod-pcrel and '
        'target-differ 0)' % KIT_ID]
for f, pr, v, um, td in verdict_rows(pairs) + verdict_rows(open(os.path.join(OUT, 'pairs-by-address.out')).read()):
    summ.append('%s\t%s\t%s\t%s\t%s' % ('EQUAL' if equal(v, um, td) else 'NOT EQUAL', f, pr, v,
                                         'target-differ %s' % (td if td in ('0', '') else len(eval(td)))))
for n, f, a, hx, what in CONTROLS:
    seg = [g for g in I['UA'].e.iter_segments() if g['p_type'] == 'PT_LOAD' and g['p_vaddr'] <= a < g['p_vaddr'] + g['p_filesz']][0]
    pl = os.path.join(OUT, 'plant-%d' % n)
    shutil.copyfile(UA, pl)
    with open(pl, 'r+b') as fh:
        fh.seek(seg['p_offset'] + a - seg['p_vaddr'])
        fh.write(bytes.fromhex(hx))
    text = '# control %d: %s; UA copy with %s written at %#x (file bytes)\n' % (n, what, hx, a)
    text += run([S2, 'cmp', f, 'GA=' + GA, 'UA=' + pl, 'GA:UA'])
    put('control-%d.out' % n, text)
    os.remove(pl)
    vr = verdict_rows(text)
    summ.append('control %d\t%s\t%s' % (n, 'CAUGHT' if vr and not equal(*vr[0][2:]) else 'MISSED', what))
put('summary.out', '\n'.join(summ) + '\n')
print('\n'.join(summ))
