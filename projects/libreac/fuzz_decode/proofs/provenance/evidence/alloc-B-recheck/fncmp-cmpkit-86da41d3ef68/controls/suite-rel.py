#!/usr/bin/env python3
"""suite.py -- the comparison kit's ONE planted-control suite: <agent>'s plants (C1, P1, P1b, P2, P2b, P2c, P3-P11, P13,
P13b, P14, K1; P12 / J1-J3 are the jtcheck cells of C1 / P2 / P7 / P1, and a1's P16 is A2 here) and <agent>'s three
(A1 .rodata window across p_filesz, A2 TLS GD tls_index, A3 unnamed .data.rel.ro cell), each run under every tool it
applies to, OLD version and KIT version.

Every plant is a FILE copy (written under PLANTED_DIR, sha256 in OUT/planted.sha256), so in-process target passes and
file-based tools see the same bytes. a1's plants are ported from <agent> strictcmp/review/plants.py and q4.py (same
addresses, same words; P13 / P13b's in-memory symbol moves are .symtab st_value patches here). Each tool also runs on the
plant's BASELINE pair (the same images without the plant's change).
Verdicts:
  target pass (tcmp):   EQUAL = bytecmp EQUAL / EQUAL-mod-pcrel and no target difference; caught = a difference at a
                        planted word offset (or bytecmp DIFFERENT); noteq-elsewhere = not equal, nothing at the offset.
                        The baseline column is the same verdict on the baseline pair.
  paircl / closure:     caught = a reported row (function not EQUAL, or a pairing conflict) that the baseline run lacks.
  jtcheck:              caught = a DIFF / UNPAIRED / REAL / SKIP line or a larger 'target differs' / 'unpaired' count
                        that the baseline run lacks.
  noteq-both (paircl / closure / jtcheck): no new row, but the planted run reports the plant's function as not equal (so
                        did the baseline): the tool calls it equal neither before nor after the plant.
  else EQUAL (not caught).
usage: suite.py KIT_DIR OUT_DIR PLANTED_DIR [JOBS]"""
import os, sys, re, hashlib, struct, shutil, subprocess, importlib.util, bisect, concurrent.futures as cf
sys.dont_write_bytecode = True
from elftools.elf.elffile import ELFFile

KIT, OUT, PL = os.path.abspath(sys.argv[1]), sys.argv[2], sys.argv[3]
JOBS = int(sys.argv[4]) if len(sys.argv) > 4 else 20
R = 'src1'
UP, UA, LP = R + '/fuzz_uci/fuzz_uci.plain', R + '/fuzz_uci/fuzz_uci.asan', R + '/fuzz_lock/fuzz_lock.plain'
# the OLD comparers, from sha-pinned copies beside this file (oldtools/SHA256SUMS): <agent>'s driver dir (strictcmp 77da,
# closure_strict 1653, jtcheck_strict eff2 + their loader) and <agent>'s egress-b-alloc tools as of paircl a88c (paircl,
# closure.py b509, jtcheck.py f95c + their e548 loader); the lanes' own directories have since moved on
OLDT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'oldtools')
S, A7 = os.path.join(OLDT, 'dgn-f1-driver'), os.path.join(OLDT, 'a7-va88c2822a0f2')
for _l in open(os.path.join(OLDT, 'SHA256SUMS')):
    _h, _n = _l.split(); assert hashlib.sha256(open(os.path.join(OLDT, _n), 'rb').read()).hexdigest() == _h, _n
E548 = 'e548/repin_check.py'
os.makedirs(OUT, exist_ok=True); os.makedirs(PL, exist_ok=True); os.makedirs(os.path.join(OUT, 'raw'), exist_ok=True)
ENV = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')

def sha(p): return hashlib.sha256(open(p, 'rb').read()).hexdigest()
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

# ---- the passes run in-process: the kit's (repin_check's tcmp IS the kit compare's) and the old ones
OLDK = os.environ.get('SUITE_OLD_KIT')    # set: old = the members of that kit dir, new = KIT's (kit-version mode)
s2 = load('kit_strictcmp2', os.path.join(OLDK or KIT, 'strictcmp2.py'))     # plant helpers (the old kit's compare in kit mode)
if OLDK:
    os2 = s2
    XCHK = os.environ.get('SUITE_XCHK_JT')   # optional cross-check jtcheck (not a kit member), run from its own directory
    s3 = load('kit_strictcmp3', os.path.join(KIT, 'strictcmp3.py'))
    rc = load('kit_repin_check', os.path.join(KIT, 'repin_check.py'))
    assert rc.tcmp is rc.S2.tcmp and os.path.samefile(rc.S2.__file__, s3.__file__)
    TC = {'strictcmp2-OLD': (os2.Img, os2.tcmp, os.path.join(OLDK, 'strictcmp2.py')),
          'strictcmp3-NEW': (s3.Img, s3.tcmp, os.path.join(KIT, 'strictcmp3.py')),
          'repin_check-NEW': (rc.S2.Img, rc.tcmp, os.path.join(KIT, 'repin_check.py'))}   # repin_check's tcmp = strictcmp3's
    SUB = {'paircl-OLD': os.path.join(OLDK, 'paircl.py'), 'paircl-NEW': os.path.join(KIT, 'paircl.py'),
           'closure_strict2-OLD': os.path.join(OLDK, 'closure_strict2.py'), 'closure_strict3-NEW': os.path.join(KIT, 'closure_strict3.py'),
           'jtcheck-OLD': os.path.join(OLDK, 'jtcheck.py'), 'jtcheck-NEW': os.path.join(KIT, 'jtcheck.py'),
           **({'jtcheck_strict2-XCHK': XCHK} if XCHK else {}),
           'cmp-strictcmp2-OLD': os.path.join(OLDK, 'strictcmp2.py'), 'cmp-strictcmp3-NEW': os.path.join(KIT, 'strictcmp3.py')}
    FAMILY = [('target pass', ['strictcmp2-OLD'], ['strictcmp3-NEW', 'repin_check-NEW']),
              ('paircl', ['paircl-OLD'], ['paircl-NEW']),
              ('closure', ['closure_strict2-OLD'], ['closure_strict3-NEW']),
              ('jtcheck', ['jtcheck-OLD'], ['jtcheck-NEW'] + (['jtcheck_strict2-XCHK'] if XCHK else [])),
              ('verdict column (cmp CLI)', ['cmp-strictcmp2-OLD'], ['cmp-strictcmp3-NEW'])]
else:
    RCF = [f for f in os.listdir(KIT) if f.startswith('repin_check-')][0]
    rc = load('kit_repin_check', os.path.join(KIT, RCF))
    st = load('old_strictcmp', os.path.join(S, 'strictcmp.py'))
    _e = open(E548).read().split('\n')
    _g = dict(ELFFile=ELFFile, bisect=bisect, bc_words=s2.bc_words, bc_cmp=s2.bc_cmp, bc_states=s2.bc_states)
    exec('\n'.join(_e[30:59]), _g); exec('\n'.join(_e[187:247]), _g)      # e548 class Img + sx..w_off, bytecmp 1480ca2faea0
    TC = {'repin_check-e548': (_g['Img'], _g['tcmp'], E548),
          'repin_check-NEW': (rc.S2.Img, rc.tcmp, os.path.join(KIT, RCF)),        # repin_check's tcmp = its strictcmp2's
          'strictcmp-77da': (st.Img, st.tcmp, os.path.join(S, 'strictcmp.py')),
          'strictcmp2-NEW': (s2.Img, s2.tcmp, os.path.join(KIT, 'strictcmp2.py'))}
    assert rc.tcmp is rc.S2.tcmp and os.path.samefile(rc.S2.__file__, s2.__file__)
    SUB = {'paircl-a88c': os.path.join(A7, 'paircl.py'), 'paircl-NEW': os.path.join(KIT, 'paircl.py'),
           'closure-b509': os.path.join(A7, 'closure.py'), 'closure_strict-1653': os.path.join(S, 'closure_strict.py'),
           'closure_strict2-NEW': os.path.join(KIT, 'closure_strict2.py'),
           'jtcheck-f95c': os.path.join(A7, 'jtcheck.py'), 'jtcheck_strict-eff2': os.path.join(S, 'jtcheck_strict.py'),
           'jtcheck_strict2-NEW': os.path.join(KIT, 'jtcheck_strict2.py')}
    FAMILY = [('target pass', ['repin_check-e548', 'strictcmp-77da'], ['repin_check-NEW', 'strictcmp2-NEW']),
              ('paircl', ['paircl-a88c'], ['paircl-NEW']),
              ('closure', ['closure-b509', 'closure_strict-1653'], ['closure_strict2-NEW']),
              ('jtcheck', ['jtcheck-f95c', 'jtcheck_strict-eff2'], ['jtcheck_strict2-NEW'])]
    # more jtcheck candidates, run as KIT-side columns: SUITE_EXTRA_JT="name=/dir/jtcheck.py,..." (each runs from its own dir)
    for e in filter(None, os.environ.get('SUITE_EXTRA_JT', '').split(',')):
        k, p = e.split('=', 1); SUB[k] = p; FAMILY[3][2].append(k)
FAMKEY = {'target pass': 't', 'paircl': 'p', 'closure': 'c', 'jtcheck': 'j', 'verdict column (cmp CLI)': 'v'}

# ---- plant helpers (encoders as in a1's tools.py)
def sx(v, b): return v - (1 << b) if v & (1 << (b - 1)) else v
def enc_jal(pc, tgt, rd):
    off = tgt - pc; assert -(1 << 20) <= off < (1 << 20) and off % 2 == 0; o = off & 0x1fffff
    return (((o >> 20) & 1) << 31) | (((o >> 1) & 0x3ff) << 21) | (((o >> 11) & 1) << 20) | (((o >> 12) & 0xff) << 12) | (rd << 7) | 0x6f
def word(I, a): return int.from_bytes(I.rd(a, 4), 'little')
def w4(x): return x.to_bytes(4, 'little')
def jal_tgt(pc, x): return pc + sx(((x >> 31) & 1) << 20 | ((x >> 12) & 0xff) << 12 | ((x >> 20) & 1) << 11 | ((x >> 21) & 0x3ff) << 1, 21)
def auipc_of(I, fn, o):
    a, z = I.fsym(fn); w = s2.bc_words(I.rd(a, z)); stt = s2.bc_states(w)
    i = [k for k, (oo, x, n) in enumerate(w) if oo == o][0]
    return w[stt[i][(w[i][1] >> 15) & 31]][0]
def repoint(I, auipc_pc, lo_pc, tgt):
    ax, lx = word(I, auipc_pc), word(I, lo_pc); d = tgt - auipc_pc; lo = sx(d & 0xfff, 12); hi = (d - lo) >> 12
    na = (ax & 0xfff) | ((hi & 0xfffff) << 12)
    nl = (lx & 0x01fff07f) | (((lo >> 5) & 0x7f) << 25) | ((lo & 31) << 7) if lx & 0x7f in (0x23, 0x27) else (lx & 0x000fffff) | ((lo & 0xfff) << 20)
    return [(auipc_pc, w4(na)), (lo_pc, w4(nl))]
def callsite(I, fn, tgt):
    a, z = I.fsym(fn); b = I.rd(a, z); t = s2.targets(a, b)
    return [a + o for i, (o, x, n) in enumerate(s2.bc_words(b)) if i in t and x & 0x7f == 0x6f and t[i][1] == tgt][0]
def tgt_off(I, fn, tgt):
    a, z = I.fsym(fn); b = I.rd(a, z); t = s2.targets(a, b)
    return [o for i, (o, x, n) in enumerate(s2.bc_words(b)) if i in t and t[i][1] == tgt][0]

IMG = {}
def kimg(p):
    if p not in IMG: IMG[p] = s2.Img(p)
    return IMG[p]

def mkcopy(src, dst, patches=(), phdr=None, syms=None):
    """dst = src with each (vaddr, bytes) written at its file offset; phdr = (PT_LOAD index, new p_filesz); syms = {symbol
    name: new st_value} written into .symtab (another image's layout for those symbols)"""
    e = ELFFile(open(src, 'rb')); segs = [g for g in e.iter_segments() if g['p_type'] == 'PT_LOAD']
    b = bytearray(open(src, 'rb').read())
    for a, data in patches:
        g = [g for g in segs if g['p_vaddr'] <= a and a + len(data) <= g['p_vaddr'] + g['p_filesz']][0]
        o = g['p_offset'] + a - g['p_vaddr']; b[o:o + len(data)] = data
    if phdr:
        k, fz = phdr; idx = [i for i, g in enumerate(e.iter_segments()) if g['p_type'] == 'PT_LOAD'][k]
        o = e['e_phoff'] + idx * e['e_phentsize'] + 32; b[o:o + 8] = struct.pack('<Q', fz)
    if syms:
        tab = e.get_section_by_name('.symtab'); hit = set()
        for k, y in enumerate(tab.iter_symbols()):
            if y.name in syms:
                o = tab['sh_offset'] + k * tab['sh_entsize'] + 8; b[o:o + 8] = struct.pack('<Q', syms[y.name]); hit.add(y.name)
        assert hit == set(syms), (set(syms) - hit)
    open(dst, 'wb').write(bytes(b)); return dst

LI = '_ZN11__sanitizer10Symbolizer14LateInitializeEv'
P = []   # (id, what, X file, Y file, Xbase, Ybase, fn, offset, paircl/closure root, tools: 'tpcjv')
def plant(pid, what, xbase, ybase, fn, off, xp=(), yp=(), xphdr=None, yphdr=None, root=None, tools='tpcjv', bx=None, by=None,
          xsyms=None, ysyms=None, watch=None, xaddr=None, yaddr=None, print_off=None, expect='caught', listed=None):
    x = mkcopy(xbase, os.path.join(PL, pid + '-X.elf'), xp, xphdr, xsyms) if (xp or xphdr or xsyms) else xbase
    y = mkcopy(ybase, os.path.join(PL, pid + '-Y.elf'), yp, yphdr, ysyms) if (yp or yphdr or ysyms) else ybase
    P.append(dict(id=pid, what=what, x=x, y=y, bx=bx or xbase, by=by or ybase, fn=fn, off=off, root=root or fn, tools=tools,
                  watch=watch or fn, xaddr=xaddr, yaddr=yaddr, print_off=print_off, expect=expect, listed=listed))

ua, up, lp = kimg(UA), kimg(UP), kimg(LP)
# C1
a, z = ua.fsym('main'); mal, fre = ua.fsym('__wrap_malloc')[0], ua.fsym('__wrap_free')[0]; pc = callsite(ua, 'main', mal)
plant('C1', 'uci.asan main+%#x jal __wrap_malloc -> jal __wrap_free' % (pc - a), UA, UA, 'main', pc - a,
      yp=[(pc, w4(enc_jal(pc, fre, (word(ua, pc) >> 7) & 31)))])
# P1
fa = ua.fsym('pthread_atfork')[0]; ao = auipc_of(ua, 'pthread_atfork', 0x3c); assert ua.res(0x5f37f8) == 'lock+0x0'
plant('P1', 'uci.asan pthread_atfork+%#x/+0x3c lock{pthread_atfork.c} -> lock{__tz.c} 0x5f37f8' % ao, UA, UA, 'pthread_atfork', 0x3c,
      yp=repoint(ua, fa + ao, fa + 0x3c, 0x5f37f8))
# P1b
fa = ua.fsym('__asan_poison_memory_region')[0]; x = word(ua, fa + 0x58); cur = jal_tgt(fa + 0x58, x)
other = [v for v in sorted(v for v, zz, t in ua.byname['_ZN6__asanL11MemToShadowEm']) if v != cur][0]
plant('P1b', 'uci.asan __asan_poison_memory_region+0x58 jal MemToShadow %#x -> the copy at %#x' % (cur, other), UA, UA,
      '__asan_poison_memory_region', 0x58, yp=[(fa + 0x58, w4(enc_jal(fa + 0x58, other, (x >> 7) & 31)))])
# P2 / P2b / P2c
for pid, base, I_, fn, lo, tgt in (('P2', UP, up, 'target_run', 0x140, 0x103bf), ('P2b', UP, up, '__libc_free', 0x5c, 0x103bf),
                                   ('P2c', UA, ua, '__assert_fail', 0x20, 0x20a4a)):
    fa = I_.fsym(fn)[0]; ao = auipc_of(I_, fn, lo)
    plant(pid, '%s %s+%#x/+%#x named object -> unnamed %#x (%s)' % (os.path.basename(base), fn, ao, lo, tgt, I_.res(tgt)),
          base, base, fn, lo, yp=repoint(I_, fa + ao, fa + lo, tgt))
# P3 / P4
la = ua.fsym(LI)[0]; dl = ua.byname['dlsym'][0][0]; pc = callsite(ua, LI, dl)
plant('P3', 'uci.asan %s+%#x jal -> X 0x9298c / Y 0x85d00 whose first 32 bytes are 0x9298c\'s' % (LI, pc - la), UA, UA, LI, pc - la,
      xp=[(pc, w4(enc_jal(pc, 0x9298c, 1)))], yp=[(pc, w4(enc_jal(pc, 0x85d00, 1))), (0x85d00, ua.rd(0x9298c, 32))])
st0 = ua.byname['_start'][0][0]
plant('P4', 'uci.asan %s+%#x jal -> X dlsym+4 / Y _start+0x18 (both 6f 00 40 00)' % (LI, pc - la), UA, UA, LI, pc - la,
      xp=[(pc, w4(enc_jal(pc, dl + 4, 1)))], yp=[(pc, w4(enc_jal(pc, st0 + 0x18, 1)))])
# P5-P8
plant('P5', 'uci.asan 0x103a4..a7 -> 11 22 33 44 (Allocator::ReInitialize+0x308 8-byte ld of 0x103a0)', UA, UA,
      '_ZN6__asan9Allocator12ReInitializeERKNS_16AllocatorOptionsE', 0x308, yp=[(0x103a4, bytes.fromhex('11223344'))])
plant('P6', 'uci.asan 0x1881d+100 -> X (InitializeFlags+0x318, a 144-byte string)', UA, UA, '_ZN6__asan15InitializeFlagsEv', 0x318,
      yp=[(0x1881d + 100, b'X')])
plant('P7', 'uci.plain 0x10444+20 15 -> 16 (__libc_malloc_impl+0xec, 32-byte a_ctz_32 table)', UP, UP, '__libc_malloc_impl', 0xec,
      yp=[(0x10444 + 20, b'\x16')])
plant('P8', 'uci.asan relative jump table 0x204e0 entry 1 := entry 2 (AddressDescription::Print+0x14)', UA, UA,
      '_ZNK6__asan18AddressDescription5PrintEPKc', 0x14, yp=[(0x204e4, ua.rd(0x204e8, 4))])
# P9
ya, yz = lp.fsym('pop_arg'); b = lp.rd(ya, yz); t = s2.targets(ya, b)
tab = [t[i][1] for i, (o, x, n) in enumerate(s2.bc_words(b)) if i in t and t[i][0] != 'jal' and lp.sec(t[i][1]) == '.rodata'][0]
plant('P9', 'lock.plain pop_arg table %#x entry 9 := entry 0, vs uci.plain pop_arg' % tab, UP, LP, 'pop_arg', 0x14,
      yp=[(tab + 36, lp.rd(tab, 4))])
# P10
fa = up.fsym('printf_core')[0]; x = word(up, fa + 0x5a0)
plant('P10', 'uci.plain printf_core+0x5a0 auipc %08x -> +1 page (a jump-table case; its consumer +0x5a8 stays equal)' % x, UP, UP,
      'printf_core', (0x5a0, 0x5a8), yp=[(fa + 0x5a0, w4((x & 0xfff) | ((((x >> 12) + 1) & 0xfffff) << 12)))])
# P11
fn = '_ZN11__sanitizer29SealedHangOnAllocationFailureEv'; fa, fz = ua.fsym(fn); b = ua.rd(fa, fz); t = s2.targets(fa, b)
cell = [t[i][1] for i, (o, x, n) in enumerate(s2.bc_words(b)) if i in t and o == 0xc][0]
plant('P11', 'uci.asan .got %#x 0x1 -> 0x100000001 (SealedHangOnAllocationFailure+0xc)' % cell, UA, UA, fn, 0xc,
      yp=[(cell, (0x100000001).to_bytes(8, 'little'))])
# P13 / P13b (a1, a13 pattern 2): a .got VALUE named through a symbol; the symbol layout of the other image is a .symtab plant
ABS1 = {'__asan_wrap_list_present': 2, '__sanitizer_sealed_init': 2, '__sanitizer_silent_reports': 2}
plant('P13', 'uci.asan %s+0xc .got %#x 1 -> 2 in Y, and Y\'s absolute symbols %s = 1 -> 2 (.symtab)' % (fn, cell, '/'.join(ABS1)),
      UA, UA, fn, 0xc, yp=[(cell, (2).to_bytes(8, 'little'))], ysyms=ABS1)
plant('P13b', 'uci.asan %s+0xc .got %#x holds 9 in X (dtls+0x1) and 0x11 in Y, where Y\'s .symtab moves dtls 8 -> 0x10 and '
      'disable_counter 16 -> 0x18' % (fn, cell), UA, UA, fn, 0xc, xp=[(cell, (9).to_bytes(8, 'little'))],
      yp=[(cell, (0x11).to_bytes(8, 'little'))], ysyms={'_ZN11__sanitizerL4dtlsE': 0x10, '_ZN6__lsan15disable_counterE': 0x18})
# P14 (a1, a13 pattern 1): an 8-byte ld re-pointed to 0x97d14 (last 4 file bytes of .got, then zero-fill) in X and to an
# unnamed .rodata address holding 8 zero bytes in Y
RI = '_ZN6__asan9Allocator12ReInitializeERKNS_16AllocatorOptionsE'; fa = ua.fsym(RI)[0]; ao = auipc_of(ua, RI, 0x308)
ro = [x for x in ua.secs if x[0] == '.rodata'][0]
z8 = next(a for a in range(ro[1] + 0x200, ro[1] + ro[2] - 8, 8) if ua.rd(a, 8) == bytes(8) and ua.res(a).startswith('(')
          and not s2.atname(ua, a))
plant('P14', 'uci.asan %s+%#x/+0x308 ld -> X 0x97d14 (4 file bytes of .got + 4 zero-fill bytes) / Y %#x (unnamed .rodata, 8 zero '
      'bytes)' % (RI, ao, z8), UA, UA, RI, 0x308, xp=repoint(ua, fa + ao, fa + 0x308, 0x97d14), yp=repoint(ua, fa + ao, fa + 0x308, z8))
# K1 (closure tools and paircl only: the change is in a callee, not in the root)
za, zz = 0x52b24, 316; o = [o for o, x, n in s2.bc_words(ua.rd(za, zz)) if n == 4 and x & 0xfe00707f == 0x33][0]; x = word(ua, za + o)
plant('K1', 'uci.asan MemToShadow{asan_poisoning.cpp} %#x+%#x add -> sub (a REAL difference in one of 5 same-named copies); root '
      '__asan_poison_memory_region' % (za, o), UA, UA, '__asan_poison_memory_region', None, yp=[(za + o, w4(x | (1 << 30)))], tools='pc',
      watch='_ZN6__asanL11MemToShadowEm')
# A1 (a13 #1): PT_LOAD[0] p_filesz cut at 0x103a0 on BOTH sides (the baseline pair too); Y's "/dev/null" -> "/dev/Null"
cut = (0, 0x103a0 - 0x10000)
bx = mkcopy(UP, os.path.join(PL, 'A1-base.elf'), (), cut)
plant('A1', 'uci.plain, PT_LOAD[0] p_filesz cut to 0x3a0 on both sides; Y 0x10383 n -> N ("/dev/Null"); __init_libc+0x194 addi '
      '0x1037e: its 64-byte window crosses p_filesz', UP, UP, '__init_libc', 0x194, xphdr=cut, yphdr=cut,
      yp=[(0x10383, b'N')], bx=bx, by=bx)
# A2 (a13 #2): GD tls_index at .got 0x97d00 = {module 1, dtprel -0x800}: dtprel -> -0x7f8 (fake_stack_tls -> dtls)
fn = '_ZN6__asan15SetTLSFakeStackEPNS_9FakeStackE'
plant('A2', 'uci.asan GD tls_index .got 0x97d00 {1, 0xfffffffffffff800}: Y offset word -> 0xfffffffffffff808 (fake_stack_tls -> '
      'dtls); %s addi' % fn, UA, UA, fn, tgt_off(ua, fn, 0x97d00), yp=[(0x97d08, (0xfffffffffffff808).to_bytes(8, 'little'))])
# A2b (<agent> 14:2xZ, a13 pattern 2): a plain 8-byte ld of a .got cell holding DIFFERENT values inside ONE STT_TLS symbol
# (8 vs 0xc, both in dtls [8,16)): equal only if a value were named as a TLS offset instead of compared raw
SH = '_ZN11__sanitizer29SealedHangOnAllocationFailureEv'
plant('A2b', 'uci.asan %s+0xc ld of .got %#x: X holds 8, Y holds 0xc (both inside STT_TLS dtls [8,16))' % (SH, cell), UA, UA,
      SH, 0xc, xp=[(cell, (8).to_bytes(8, 'little'))], yp=[(cell, (0xc).to_bytes(8, 'little'))])
# A3 (a13 #3): unnamed .data.rel.ro pointer table 0x96be0 (GetHandleSignalMode+0x24): entries 0 and 1 swapped
fn = '_ZN11__sanitizer19GetHandleSignalModeEi'
plant('A3', 'uci.asan unnamed .data.rel.ro table 0x96be0 (8-byte pointers into common_flags_dont_use): entries 0 and 1 swapped '
      '(GetHandleSignalMode+0x24)', UA, UA, fn, 0x24, yp=[(0x96be0, ua.rd(0x96be8, 8) + ua.rd(0x96be0, 8))])
# T3 (<agent>, next kit): a function with 3 differing targets where the THIRD is real. fuzz_ctrl asan twin vs asan-ubsan
# twin, __nl_langinfo_l has 2 natural differing targets (+0x5c, +0xf8); Y's tail call at +0x114 `j __lctrans` (0x8f968)
# -> `j __mo_lookup` (0x8f9b8). A tool catches it only if it PRINTS the +0x114 target (print_off), not only a changed count.
CU = 'bin/fuzz_ctrl'; cb = kimg(CU + '/fuzz_ctrl.asan-ubsan')
assert word(cb, 0x9b97c) == 0xfedf306f
plant('T3', 'fuzz_ctrl asan vs asan-ubsan __nl_langinfo_l (2 natural differing targets): Y +0x114 j __lctrans -> j __mo_lookup '
      '(the third differing target is the real one)', CU + '/fuzz_ctrl.asan', CU + '/fuzz_ctrl.asan-ubsan', '__nl_langinfo_l',
      0x114, yp=[(0x9b97c, w4(enc_jal(0x9b97c, 0x8f9b8, 0)))], print_off=0x114)
# AMB (kno-7's case, next kit): an ambiguous name. X = uci.asan with a REAL difference (the K1 add -> sub) in
# MemToShadow{asan_poisoning.cpp} @0x52b24; five sized copies carry the name. Target passes compare 0x52b24 with 0x52b24;
# the name-taking tools (paircl root, closure root, jtcheck fn) get the bare name: picking any copy is wrong, refusing is right.
za = 0x52b24; o = [o for o, x, n in s2.bc_words(ua.rd(za, 316)) if n == 4 and x & 0xfe00707f == 0x33][0]; x = word(ua, za + o)
plant('AMB', 'uci.asan, X MemToShadow{asan_poisoning.cpp} %#x+%#x add -> sub; tools that take a name get the bare, 5-copy name'
      % (za, o), UA, UA, '_ZN6__asanL11MemToShadowEm', None, xp=[(za + o, w4(x | (1 << 30)))], xaddr=za, yaddr=za)

# ---- the plants of strictcmp3's rules (<agent> strictcmp/lui LUI.md sec. 1-5), as FILE copies; expect='equal' marks
# a NEGATIVE (the right answer is EQUAL); listed = the acceptance kind that must be printed with that EQUAL
def enc_lui(rd, v): return ((v & 0xfffff) << 12) | (rd << 7) | 0x37
def enc_i(op, f3, rd, rs1, imm): return ((imm & 0xfff) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op
def enc_s(op, f3, rs1, rs2, imm): return (((imm >> 5) & 0x7f) << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | ((imm & 31) << 7) | op
def enc_r(f7, f3, rd, rs1, rs2): return (f7 << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | 0x33
def hilo(a):
    lo = sx(a & 0xfff, 12); return ((a - lo) >> 12) & 0xfffff, lo
# A5: <agent>'s weakplant, rebuilt: reac_frame_clean_len's first 8 bytes `lui t0,0x5f3; ld t1,0x750(t0)` in copies of
# fuzz_wire.asan (X) and fuzz_decode.asan (Y); 0x5f3750 = __stack_chk_guard+0x0 in X, builtin_tls+0x1fac0 in Y
WA, DA = R + '/fuzz_wire/fuzz_wire.asan', 'src2/fuzz_decode/fuzz_decode.asan'
wa, da = kimg(WA), kimg(DA); W8 = w4(enc_lui(5, 0x5f3)) + w4(enc_i(0x03, 3, 6, 5, 0x750))
plant('A5', "<agent>'s weakplant: reac_frame_clean_len+0 `lui t0,0x5f3; ld t1,0x750(t0)` in both (fuzz_wire.asan X, "
      'fuzz_decode.asan Y); 0x5f3750 names different objects', WA, DA, 'reac_frame_clean_len', (0x0, 0x4),
      xp=[(wa.fsym('reac_frame_clean_len')[0], W8)], yp=[(da.fsym('reac_frame_clean_len')[0], W8)])
# L*/N*: a1's lui plants on __libc_calloc (uci.plain X, lock.plain Y, the same words at its start in both); 0x10398 =
# MARGIN_MAX+0x0 in uci.plain, RATES+0x8 in lock.plain
HOST = '__libc_calloc'; AD = 0x10398; hi, lo = hilo(AD); hx, hy = up.fsym(HOST)[0], lp.fsym(HOST)[0]
def lplant(pid, what, words_, off, **kw):
    b = b''.join(w4(x) for x in words_)
    plant(pid, what, UP, LP, HOST, off, xp=[(hx, b)], yp=[(hy, b)], **kw)
lplant('L1', 'lui t0,hi; ld t1,lo(t0) -> 0x10398 (MARGIN_MAX+0 | RATES+8)', [enc_lui(5, hi), enc_i(0x03, 3, 6, 5, lo)], (0x0, 0x4))
mh, ml = hilo(up.fsym('main')[0])
lplant('L4', 'lui t0,hi(main); jalr ra,lo(t0): an absolute call', [enc_lui(5, mh), enc_i(0x67, 0, 1, 5, ml)], (0x0, 0x4))
ja = next(o for o, x, n in s2.bc_words(up.rd(hx, up.fsym(HOST)[1])) if n == 4 and x & 0x7f == 0x6f and (x >> 7) & 31)
lplant('L5', 'call-argument lui: lui a0,hi; addi a0,a0,lo; jal ra,+%#x (0x10398 leaves the function as a0)' % ja,
       [enc_lui(10, hi), enc_i(0x13, 0, 10, 10, lo), enc_jal(8, ja, 1)], (0x0, 0x4, 0x8))
lplant('N1', 'NEGATIVE mask lui: lui t0,0xfffff; and a0,a0,t0 (value in no section)', [enc_lui(5, 0xfffff), enc_r(0, 7, 10, 10, 5)],
       None, expect='equal')
lplant('N4', 'NEGATIVE mask lui IN a section: lui t0,0x11; and a0,a0,t0 (0x11000 in .rodata, only `and`)',
       [enc_lui(5, 0x11), enc_r(0, 7, 10, 10, 5)], None, expect='equal', listed='lui-const')
lplant('N4b', 'the same value 0x11000 used as an address: lui t0,0x11; ld t1,0(t0)', [enc_lui(5, 0x11), enc_i(0x03, 3, 6, 5, 0)],
       (0x0, 0x4))
# E*: rule 3 with ESC (<agent> 15:19Z), uci.plain vs uci.plain: an addi pair re-pointed in both to an unnamed read-only
# address holding a planted object (a1's esc_site / esc_plant)
def esc_site(I):
    st_ = s2._meta(I)['starts']; ro = [x for x in I.secs if x[0] == '.rodata'][0]
    base = next(a for a in range(ro[1] + 0x100, ro[1] + ro[2] - 0x40)
                if (s2.qres(I, a) or '').startswith('(') and not s2.atname(I, a)
                and min((s for s in st_ if s > a), default=ro[1] + ro[2]) >= a + 32 and s2.readonly(I, a))
    for nm in sorted(n for n in I.byname if I.fsym(n)):
        fa, fz = I.fsym(nm); b = s2.frd(I, fa, fz)
        if b is None: continue
        w = s2.bc_words(b); t = s2.targets(fa, b); stt = s2.bc_states(w)
        for i in sorted(t):
            o_, x_, n_ = w[i]
            if t[i][0] == 'lo12' and x_ & 0x7f == 0x13 and not s2.execsec(I, t[i][1]):
                return nm, o_, w[stt[i][(x_ >> 15) & 31]][0], base
FE, OE, AE_, BE = esc_site(up); fe = up.fsym(FE)[0]
def eplant(pid, what, bx_, by_, **kw):
    rp = repoint(up, fe + AE_, fe + OE, BE)
    plant(pid, what + ' (%s+%#x -> %#x)' % (FE, OE, BE), UP, UP, FE, OE, xp=[(BE, bx_)] + rp, yp=[(BE, by_)] + rp, **kw)
eplant('E1', 'ESC string \\x1b[1mBold\\0, bytes differ after the NUL (accepted under rule B, listed)', b'\x1b[1mBold\x00AAAA',
       b'\x1b[1mBold\x00BBBB', expect='equal', listed='cstr')
eplant('E2', 'ESC, NUL, then different data (the hole the ruling accepts, listed)', b'\x1b\x00\x01\x02\x03\x04\x05\x06',
       b'\x1b\x00\x01\x02\x09\x0a\x0b\x0c', expect='equal', listed='cstr')
eplant('E3', 'EMPTY string, data differs after (out of rule B)', b'\x00\x01\x02\x03\x04\x05\x06\x07', b'\x00\x01\x02\x03\x09\x0a\x0b\x0c')
eplant('E4', 'ESC string, the STRING differs (Bold -> BOLD)', b'\x1b[1mBold\x00pad1', b'\x1b[1mBOLD\x00pad1')
# Q*/V*: <agent>'s fuzz_preset B pair (old B : #102 B) and <agent>'s put_utf8 plants on #102 B
PO = 'src4/fuzz_preset/fuzz_preset.asan-ubsan'
PN = 'src3/fuzz_preset/fuzz_preset.asan-ubsan'
pn = kimg(PN)
plant('Q0', 'NEGATIVE natural pair pj_write old B : #102 B (.str.3{preset_file.c} vs .str.3, same bytes): NAME-ONLY',
      PO, PN, 'pj_write', 0x48, bx=PO, by=PO, expect='equal', listed='NAME-ONLY')
plant('Q1', 'pj_write: #102 B .str.3 byte 0 0x0a -> 0x0b (same label, different bytes)', PO, PN, 'pj_write', 0x48,
      yp=[(0x21440, b'\x0b')], bx=PO, by=PN)
pu = pn.fsym('put_utf8')[0]; x1 = word(pn, pu + 0x1c0); x2 = word(pn, pu + 0xc)
plant('V1', "<agent> P1: put_utf8+0x1c0 jal __asan_report_store1 -> __asan_report_store2 (#102 B)", PO, PN, 'put_utf8', 0x1c0,
      yp=[(pu + 0x1c0, w4(enc_jal(pu + 0x1c0, pn.fsym('__asan_report_store2')[0], (x1 >> 7) & 31)))], bx=PO, by=PN)
plant('V2', "<agent> P2: put_utf8+0xc .got load offset + 8 (#102 B)", PO, PN, 'put_utf8', 0xc,
      yp=[(pu + 0xc, w4((x2 & 0x000fffff) | ((((x2 >> 20) + 8) & 0xfff) << 20)))], bx=PO, by=PN)

with open(os.path.join(OUT, 'planted.sha256'), 'w') as f:
    for p in sorted({UP, UA, LP} | {q[k] for q in P for k in ('x', 'y', 'bx', 'by')}):
        f.write('%s  %s\n' % (sha(p), p))
    for q in P: f.write('# %s: %s | X %s | Y %s | baseline X %s Y %s | fn %s off %s root %s\n'
                        % (q['id'], q['what'], q['x'], q['y'], q['bx'], q['by'], q['fn'],
                           ' '.join(hex(o) for o in q['off']) if isinstance(q['off'], tuple) else q['off'] if q['off'] is None else hex(q['off']), q['root']))

# ---- target passes (in-process)
RES = {}; CACHE = {}
def cimg(ImgC, p):
    if (id(ImgC), p) not in CACHE: CACHE[(id(ImgC), p)] = ImgC(p)
    return CACHE[(id(ImgC), p)]
def tcmp_run(tool, q, base):
    ImgC, tc, _ = TC[tool]; xp, yp = (q['bx'], q['by']) if base else (q['x'], q['y'])
    X, Y = cimg(ImgC, xp), cimg(ImgC, yp); I = {'X': X, 'Y': Y}
    if q['xaddr'] is None: sx_, sy_ = X.fsym(q['fn']), Y.fsym(q['fn'])
    else: sx_, sy_ = [(v, z) for v, z, n, t in X.syms if v == q['xaddr'] and t == 'STT_FUNC'][0], (q['yaddr'], 0)
    fb = []
    try: r = tc(I, 'X', sx_[0], 'Y', sy_[0], sx_[1], fb)
    except TypeError: r = tc(I, 'X', sx_[0], 'Y', sy_[0], sx_[1])
    v, c, t3, diff = r
    eq = v in ('EQUAL', 'EQUAL-mod-pcrel') and not diff
    offs = q['off'] if isinstance(q['off'], tuple) else (q['off'],)
    at = any(int(str(d[0]), 16) in offs for d in diff) or v == 'DIFFERENT'
    verdict = ('equal-listed' if q['listed'] and any(e[0] == q['listed'] for e in fb) else 'EQUAL') if eq else \
        'caught' if at else 'noteq-elsewhere'
    line = '%s %#x vs %#x size %d: %s %s fallbacks %s differ %d %s accepted %s' % (
        q['fn'], sx_[0], sy_[0], sx_[1], v, c, t3, len(diff), [tuple(d[:4]) for d in diff][:6], [tuple(e[:2]) for e in fb][:6])
    return verdict, line

# ---- subprocess tools
def cmd(tool, q, base):
    xp, yp = (q['bx'], q['by']) if base else (q['x'], q['y']); f = SUB[tool]; os.makedirs(os.path.join(OUT, 'raw', q['id']), exist_ok=True)
    if tool.startswith('paircl'):
        # --targets-out: the next paircl writes every differing target there (the old one reads argv[1:6] and ignores it)
        return ['python3', '-B', f, xp, yp, q['root'], hex(q['yaddr'] or kimg(yp).fsym(q['root'])[0]), yp, '--targets-out',
                os.path.join(OUT, 'raw', q['id'], '%s-%s.targets.tsv' % (tool, 'baseline' if base else 'planted'))]
    if tool.startswith('closure'):
        return ['python3', '-B', f, xp, yp, q['root']]
    if tool.startswith('cmp-'):
        return ['python3', '-B', f, 'cmp', q['fn'], 'X=' + xp, 'Y=' + yp, 'X:Y']
    return ['python3', '-B', f, xp, yp, q['fn']]
def runsub(tool, q, base):
    c = cmd(tool, q, base)
    raw = os.path.join(OUT, 'raw', q['id'], '%s-%s.out' % (tool, 'baseline' if base else 'planted'))
    if os.environ.get('SUITE_REJUDGE') and os.path.exists(raw):   # re-judge the saved outputs of an earlier run, run nothing
        t = open(raw).read(); m = re.match(r'\$ (.*)\n# rc (-?\d+)\n', t); body = t[m.end():]
        o, _, e = body.partition('# stderr\n') if '\n# stderr\n' in '\n' + body else (body, '', '')
        assert m.group(1) == ' '.join(c), (raw, m.group(1))
        return m.group(1), int(m.group(2)), o, e
    p = subprocess.run(c, cwd=os.path.dirname(c[2]), capture_output=True, text=True, env=ENV, timeout=7200)
    return ' '.join(c), p.returncode, p.stdout, p.stderr
def rows(tool, out):
    if tool.startswith('jtcheck'):
        r = set(); cnt = [0, 0, 0]
        for l in out.split('\n'):
            if l.startswith(('   DIFF', '   UNPAIRED', '   UNMEASURED')) or 'REAL difference' in l or '\tSKIP' in l or '\tUNREADABLE' in l:
                r.add(l)
            m = re.search(r'target differs (\d+)\t', l)
            if m:
                u = re.search(r'target unmeasured (\d+)', l); p = re.search(r'unpaired(?: differing words)? (\d+)', l)
                cnt = [cnt[0] + int(m.group(1)), cnt[1] + (int(u.group(1)) if u else 0), cnt[2] + (int(p.group(1)) if p else 0)]
        return r, cnt
    r = {l for l in out.split('\n') if (l.startswith('   ') and 'ACCEPT' not in l) or l.startswith('  CONFLICT')}
    m = re.search(r'pairing conflicts (\d+)', out)
    return r, [int(m.group(1)) if m else 0]
REFUSAL = ('REFUSED root', 'AMBIGUOUS root name', 'SKIP AMBIGUOUS', '\tSKIP ambiguous', 'AMBIGUOUS\t')
LISTED = {'cstr': ('CSTR\t',), 'NAME-ONLY': ('NAME-ONLY',), 'lui-const': ('lui-const',)}
EQV = ('EQUAL', 'EQUAL-mod-pcrel')
def cmpverdict(out, fn):
    """the printed VERDICT column (7th) of a `strictcmp[23].py cmp` row for fn X:Y; None if no such row"""
    for l in out.split('\n'):
        c = l.split('\t')
        if len(c) > 6 and c[0] == fn and c[1] == 'X:Y': return c[6]
    return None
def subverdict(tool, q, outp, outb, rcp, errp=''):
    """refused = the tool refuses the planted run's name (rc != 0 with REFUSED, or an AMBIGUOUS / SKIP ambiguous line):
    it claims nothing, fail closed; caught = a reported row the baseline lacks, and, for a plant with print_off, the
    planted target printed, or (caught-tsv) listed in the tool's full targets file while its row says TRUNCATED; else
    count-only: the row changed but the planted target is shown nowhere; noteq-both = no new row, but the planted run
    reports the watched function (not called equal before or after the plant); EQUAL = neither (equal-listed: EQUAL and
    the plant's acceptance kind printed). cmp-* tools are judged by their printed VERDICT column only."""
    if any(m in outp + errp for m in REFUSAL): return 'refused', [l for l in (outp + errp).split('\n') if any(m in l for m in REFUSAL)][:1]
    if rcp != 0: return 'ERROR rc %d' % rcp, []
    lst = q['listed'] and any(mk in l and q['watch'] in l for l in outp.split('\n') for mk in LISTED[q['listed']])
    if tool.startswith('cmp-'):
        vp, vb = cmpverdict(outp, q['fn']), cmpverdict(outb, q['fn'])
        if vp in EQV: return ('equal-listed' if lst else 'EQUAL'), ['verdict column %s' % vp]
        return ('noteq-both' if vb not in EQV else 'caught'), ['verdict column %s (baseline %s)' % (vp, vb)]
    rp, cp = rows(tool, outp); rb, cb = rows(tool, outb)
    new = sorted(rp - rb)
    if q['expect'] == 'equal' and not tool.startswith('jtcheck'):
        # a NEGATIVE in a closure: judge the plant's own function; other members of the closure may differ on their own
        own = [l for l in new if q['watch'] in l]
        if own: return 'caught', own
        if new: return ('equal-listed' if lst else 'EQUAL') + ' (own row; %d other members reported)' % len(new), new
    if new or any(a > b for a, b in zip(cp, cb)):
        po = q['print_off']
        if po is not None and not any(s in outp for s in ("'%#x'" % po, 'TARGET %#x ' % po, '+%#x ' % po)):
            tsv = os.path.join(OUT, 'raw', q['id'], '%s-planted.targets.tsv' % tool)
            if 'TRUNCATED' in outp and os.path.exists(tsv) and any(l.split('\t')[3:4] == ['%#x' % po] for l in open(tsv)):
                return 'caught-tsv', new
            return 'count-only', new
        return 'caught', new
    seen = sorted(rp) if tool.startswith('jtcheck') and any(cp) else sorted(l for l in rp if q['watch'] in l)
    return ('noteq-both', seen) if seen else (('equal-listed' if lst else 'EQUAL'), [])

jobs = {}
with cf.ThreadPoolExecutor(JOBS) as ex:
    for q in P:
        for fam, olds, news in FAMILY:
            if fam == 'target pass' or FAMKEY[fam] not in q['tools']: continue
            for tool in olds + news:
                for base in (False, True):
                    jobs[(q['id'], tool, base)] = ex.submit(runsub, tool, q, base)
    for q in P:
        if 't' in q['tools']:
            for tool in TC:
                for base in (False, True):
                    RES[(q['id'], tool, base)] = tcmp_run(tool, q, base)
    for k, fu in jobs.items():
        RES[k] = fu.result()

def toolsha(tool): return sha(TC[tool][2] if tool in TC else SUB[tool])[:12]
summ = open(os.path.join(OUT, 'SUMMARY.tsv'), 'w')
summ.write('plant\tfamily\ttool\tsha12\tversion\tbaseline verdict\tplanted verdict\tevidence\n')
for q in P:
    d = os.path.join(OUT, 'raw', q['id']); os.makedirs(d, exist_ok=True)
    for fam, olds, news in FAMILY:
        for tool in olds + news:
            if (q['id'], tool, False) not in RES: continue
            ver = 'NEW (kit)' if tool.endswith('NEW') else 'cross-check' if tool.endswith('XCHK') else 'old'
            if tool in TC:
                vp, lp_ = RES[(q['id'], tool, False)]; vb, lb = RES[(q['id'], tool, True)]
                open(os.path.join(d, tool + '.out'), 'w').write('PLANTED  %s\nBASELINE %s\n' % (lp_, lb))
                summ.write('%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' % (q['id'], fam, tool, toolsha(tool), ver, vb, vp, lp_))
            else:
                cp, rcp, op, ep = RES[(q['id'], tool, False)]; cb, rcb, ob, eb = RES[(q['id'], tool, True)]
                open(os.path.join(d, tool + '-planted.out'), 'w').write('$ %s\n# rc %d\n%s%s' % (cp, rcp, op, ('# stderr\n' + ep) if ep else ''))
                open(os.path.join(d, tool + '-baseline.out'), 'w').write('$ %s\n# rc %d\n%s%s' % (cb, rcb, ob, ('# stderr\n' + eb) if eb else ''))
                v, new = subverdict(tool, q, op, ob, rcp, ep)
                vb = 'refused' if any(m in ob + eb for m in REFUSAL) else 'ERROR rc %d' % rcb if rcb else \
                    ('reports %s' % q['watch'][:40]) if any(q['watch'] in l for l in rows(tool, ob)[0]) else 'does not report it'
                summ.write('%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' % (q['id'], fam, tool, toolsha(tool), ver, vb, v, ' | '.join(new)[:600]))
summ.close()
print('plants %d; results in %s' % (len(P), os.path.join(OUT, 'SUMMARY.tsv')))
