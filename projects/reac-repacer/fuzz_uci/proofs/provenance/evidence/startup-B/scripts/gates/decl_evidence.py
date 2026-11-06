#!/usr/bin/env python3
"""decl_evidence.py -- the evidence for every codeptr --same / --not-address declaration of codeptr-decl.sh
(the image-B start-up gate set). Each pass-1 value is checked by its ROLE in BOTH images, by command:
  * its first occurrence in the fuzz_uci B file and in cgif's donor file of the same name (file:line + term context);
  * the image fact its reason states: a symbol + offset (uci: twin .symtab; cgif: the recovered nm, stripped image),
    a layout identity (PT_LOAD hull / rw window), an instruction word (the 4 bytes at the fetch address in each image),
    or a mapping-length identity (shadow length = am_len / 8 of the same anonymous mapping).
  usage: decl_evidence.py UCI_IMG UCI_TWIN_NMS CGIF_IMG CGIF_NM GEN_DIR CGIF_DIR      exit 0 = every fact holds
"""
import re
import sys

from elftools.elf.elffile import ELFFile

UI, UN, CI, CN, GD, CD = sys.argv[1:7]
FAIL = []


def check(ok, msg):
    print('   %s %s' % ('ok  ' if ok else 'FAIL', msg))
    if not ok:
        FAIL.append(msg)


def nm(p):
    rows = []
    for l in open(p):
        s = l.split()
        if l.startswith('#') or len(s) < 3:
            continue
        if len(s) == 4:
            rows.append((int(s[0], 16), int(s[1], 16), s[2], s[3]))
        else:
            rows.append((int(s[0], 16), 0, s[1], s[2]))
    return rows


def symoff(rows, v):
    c = [(a, n) for a, z, t, n in rows if a <= v < a + z and t not in 'nN' and not n.startswith('$')]
    return '%s+%#x' % (c[0][1], v - c[0][0]) if c else None


class Img:
    def __init__(self, p):
        e = ELFFile(open(p, 'rb'))
        self.loads = [(s['p_vaddr'], s['p_filesz'], s['p_memsz'], s.data()) for s in e.iter_segments()
                      if s['p_type'] == 'PT_LOAD']
        self.secs = [(s.name, s['sh_addr'], s['sh_addr'] + s['sh_size']) for s in e.iter_sections() if s['sh_addr']]
        self.top = max(v + m for v, f, m, d in self.loads)

    def word(self, a):
        for v, f, m, d in self.loads:
            if v <= a and a + 4 <= v + f:
                return int.from_bytes(d[a - v:a - v + 4], 'little')

    def sec(self, a):
        c = [(n, lo) for n, lo, hi in self.secs if lo <= a < hi]
        return '%s+%#x' % (c[0][0], a - c[0][1]) if c else 'no section'


def first(path, v):
    pat = re.compile(r'(?<![0-9A-Za-z_])(0x0*%x|%d)(?![0-9A-Za-z_])' % (v, v), re.I)
    for i, l in enumerate(open(path).read().split('\n')):
        m = pat.search(l)
        if m:
            return '%s:%d `..%s..`' % (path.split('/')[-1], i + 1, l[max(0, m.start() - 90):m.end() + 12].strip())
    return None


def occ(v, files):
    for f in files:
        print('   uci  %s' % first('%s/%s.v' % (GD, f), v))
        print('   cgif %s' % first('%s/%s.v' % (CD, f), v))


U, C = Img(UI), Img(CI)
UNM, CNM = nm(UN), nm(CN)
ceil = lambda x: -(-x // 4096) * 4096

print('== 0x10800 (--same): gp, __global_pointer$')
occ(0x10800, ['YB01', 'YB03', 'YD2i', 'YF0m'])
check([n for a, z, t, n in UNM if a == 0x10800 and n == '__global_pointer$'] != [], 'uci twin: 0x10800 = __global_pointer$')
check(C.sec(0x10800) == '.rodata+0x520', 'cgif (stripped): 0x10800 = %s (no symbol; its own YF0m says TFIB_GP := 0x10800)' % C.sec(0x10800))
for f in ('YB01', 'YB03'):
    nu = len(re.findall(r'\(ELit \(-\d+\)\); ELit 67584;', open('%s/%s.v' % (GD, f)).read()))
    nc = len(re.findall(r'\(ELit \(-\d+\)\); ELit 67584;', open('%s/%s.v' % (CD, f)).read()))
    check(nu == nc and nu > 0, '%s: register x3 (gp) = ELit 67584 in %d uci / %d cgif states' % (f, nu, nc))
for side, d in (('uci', GD), ('cgif', CD)):
    check('Definition TFIB_GP : Z := 0x10800.' in open('%s/YF0m.v' % d).read(), '%s YF0m: Definition TFIB_GP : Z := 0x10800.' % side)

print('== 0x10101 (--not-address): the VALUE of asan_flags_dont_use_directly+0x70 (flag bytes 01 01 01 00)')
occ(0x10101, ['YB01', 'YB03', 'YF0m'])
su, sc = symoff(UNM, 0x9c968), symoff(CNM, 0xa3ae8)
check(su == '_ZN6__asan28asan_flags_dont_use_directlyE+0x70' and sc == su, 'cell uci 0x9c968 = %s, cgif 0xa3ae8 = %s' % (su, sc))
for side, d, a in (('uci', GD, 0x9c968), ('cgif', CD, 0xa3ae8)):
    t = open('%s/YF0m.v' % d).read()
    check('z8 (ANum %#x) 0x10101' % a in t, '%s YF0m Tfib_const_abs `z8 (ANum %#x) 0x10101`' % (side, a))
    t = open('%s/YB01.v' % d).read()
    check('a_off := %d |} 4 (ELit 65793)' % a in t, '%s YB01 KWord at %d (%#x) width 4 = ELit 65793' % (side, a, a))

print('== 0x100000 (--not-address): 1 MiB, a SIZE (instance+0x328 value; mapping length / shadow length)')
occ(0x100000, ['YB01', 'YB03', 'YF0m'])
su, sc = symoff(UNM, 0x9bdc0), symoff(CNM, 0xa2f40)
check(su == '_ZN6__asanL8instanceE+0x328' and sc == su, 'cell uci 0x9bdc0 = %s, cgif 0xa2f40 = %s' % (su, sc))
for side, d, a in (('uci', GD, 0x9bdc0), ('cgif', CD, 0xa2f40)):
    check('z8 (ANum %#x) 0x100000' % a in open('%s/YF0m.v' % d).read(), '%s YF0m `z8 (ANum %#x) 0x100000`' % (side, a))


def maps(path):
    t = open(path).read()
    s = t[t.find('Definition HS_tfib_0 :'):]
    s = s[:s.find('\nDefinition ', 5)]
    return {int(k): int(n) for k, n in re.findall(r'am_base := EMd Instr\.M_MUL \(ELit 4096\) \(EVar (\d+)\); am_len := ELit (\d+)', s)}


def shadow_windows(path):
    t = open(path).read()
    s = t[t.find('Definition HS_tfib_0_kn'):]
    s = s[:s.find('\nDefinition ', 10)]
    return {(int(k), int(n)) for k, n in re.findall(r'a_base := EMd Instr\.M_MUL \(ELit 512\) \(EVar (\d+)\); a_off := 2147450880 \|\} \(ELit (\d+)\)', s)}


mu, mc = maps(GD + '/YB01.v'), maps(CD + '/YB01.v')
wu, wc = shadow_windows(GD + '/YB01.v'), shadow_windows(CD + '/YB01.v')
print('== shadow-band LENGTHS of HS_tfib_0 (KDisj (0x7fff8000 + 512*EVar n, L), L = am_len(4096*EVar n) / 8): --not-address')
for v, k in ((0x20000, 500), (0x71c00, 254), (0x100000, 501), (0x161200, 424)):
    occ(v, ['YB01'])
    check((k, v) in wu and (k, v) in wc and mu.get(k) == 8 * v and mc.get(k) == 8 * v,
          '%#x = %d: uci and cgif HS_tfib_0_kn both carry KDisj (0x7fff8000 + 512*EVar %d, %d); am_len(EVar %d) uci %s / cgif %s = 8 * %d'
          % (v, v, k, v, k, mu.get(k), mc.get(k), v))
print('== 0x38e000 (--not-address): am_len of mapping 4096*EVar 254 (a LENGTH)')
occ(0x38e000, ['YB01', 'YB03'])
check(mu.get(254) == 0x38e000 and mc.get(254) == 0x38e000, 'am_len(EVar 254) uci %s / cgif %s = 3727360' % (mu.get(254), mc.get(254)))

print('== bounds / values of the hand-off and join states (--not-address), the same term in both files')
for v, what in ((0x1ffff, 'KRange (EVar 3) 0 131071'), (0x445c0, 'KRange (EVar 4) 0 280000'),
                (0x3fffff, 'KRange (EVar 43) 1 4194303'), (0x100018, '|} (ELit 1048600); KZero')):
    occ(v, ['YB01', 'YB03'])
    for f in ('YB01', 'YB03'):
        nu, nc = open('%s/%s.v' % (GD, f)).read().count(what), open('%s/%s.v' % (CD, f)).read().count(what)
        check(nu == nc and nu > 0, '%s `%s`: %d uci / %d cgif' % (f, what, nu, nc))
occ(0x3fffff, ['YD1y', 'YD2i'])
for f, what in (('YD1y', 'mkAF 1 4194303 0'), ('YD2i', 'KRange (EVar TIDV) 1 4194303')):
    nu, nc = open('%s/%s.v' % (GD, f)).read().count(what), open('%s/%s.v' % (CD, f)).read().count(what)
    check(nu == nc and nu > 0, '%s `%s` (tid bound 2^22 - 1): %d uci / %d cgif' % (f, what, nu, nc))

print('== 0x55c000 (--not-address): rw_len = page_ceil(image top) - rw_lo, a LENGTH; the bases differ')
occ(0x55c000, ['YB12', 'YB13', 'YB1h'])
for side, img, d, lo in (('uci', U, GD, 0x98000), ('cgif', C, CD, 0x9f000)):
    t = open('%s/YB12.v' % d).read()
    check('rw_lo := %#x; rw_len := 0x55c000;' % lo in t and ceil(img.top) - lo == 0x55c000,
          '%s: YB12 rw_lo %#x, PT_LOAD top %#x -> page ceil %#x, minus rw_lo = %#x' % (side, lo, img.top, ceil(img.top), ceil(img.top) - lo))

print('== instruction words (--not-address): the bv 32 word at each image\'s own fetch address')
x_pn = {}
for side, d in (('uci', GD), ('cgif', CD)):
    m = re.search(r'x_pnscan := (0x[0-9a-f]+)', open('%s/YB12.v' % d).read())
    x_pn[side] = int(m.group(1), 16)
occ(0x158593, ['YB1h'])
check(U.word(x_pn['uci'] - 4) == 0x158593 and C.word(x_pn['cgif'] - 4) == 0x158593,
      '0x00158593 (YB1h tfib_Fp1, x_pnscan - 4): uci x_pnscan %#x word %#x; cgif x_pnscan %#x word %#x'
      % (x_pn['uci'], U.word(x_pn['uci'] - 4), x_pn['cgif'], C.word(x_pn['cgif'] - 4)))
FW = re.compile(r'Lemma (F_\d+) : fetch_word tfibsegs \(Z_to_bv 64 (0x[0-9a-f]+)\) = Some \((0x[0-9a-f]+)%bv')
fu = {n: (int(a, 16), int(w, 16)) for n, a, w in FW.findall(open(GD + '/YB1k.v').read())}
fc = {n: (int(a, 16), int(w, 16)) for n, a, w in FW.findall(open(CD + '/YB1k.v').read())}
for v in (0x155593, 0x155793, 0x255513, 0x255793, 0x455593, 0x455793):
    ns = sorted(n for n, (a, w) in fu.items() if w == v)
    for n in ns:
        (ua, uw), (ca, cw) = fu[n], fc.get(n, (None, None))
        check(uw == v == cw and U.word(ua) == v and ca is not None and C.word(ca) == v,
              '%#010x YB1k %s: uci fetch %#x reads %#x; cgif %s fetch %#x reads %#x' % (v, n, ua, U.word(ua), n, ca, C.word(ca)))
print('decl_evidence: %s (%d failed)' % ('ALL FACTS HOLD' if not FAIL else 'FAILED', len(FAIL)))
sys.exit(1 if FAIL else 0)
