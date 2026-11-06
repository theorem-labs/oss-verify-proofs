#!/usr/bin/env python3
"""settle-rcf-sm1.py KIT DONOR TARGET: the one target the comparison kit does not settle in
__sanitizer::RegisterCommonFlags (the word at +0x1218), measured by name, beside the kit's own verdict. KIT is the
directory of the comparison kit of record (cmpkit 86da41d3ef68, strictcmp3.py); DONOR and TARGET are the unstripped
twins of fuzz_grant.asan-ubsan and fuzz_uci.asan-ubsan. Read-only; the one control plants in memory.

The kit's class: an UNNAMED target in read-only data that holds an EMPTY string (its first byte is NUL). The kit
compares it on the full region to the next symbol, which differs between two layouts (fail-closed, not a real
difference). The settlement is the named measurement for that class:
 1. kit: strictcmp3's tsame on the target pair of +0x1218 (the auipc + addi address that word takes).
 2. settled: both targets lie in read-only data, and the bytes from each target up to and including its first NUL, all
    file bytes, are equal (an empty C string is the one byte 0x00).
 3. control: one printable byte planted at the target in the target image makes the settled compare DIFFERENT.
 4. +0x1218 against the code table: the proof's table (lib/B/Rt/YF0r.v fs_ranges) holds only the two words of this
    body at [+0x358, +0x360), so the proof never steps through the word at +0x1218.
 5. consumer: the addi at +0x1218 writes register rd; its next use, before rd is written again, is an `sd rd, off(base)`
    storing the address into a field of the flag-registration record, the same word in both images. So the address is
    consumed as a const char* (a C string), which is what 2 compares. The words around it that hold pc-relative
    immediates (+0x1218 itself, the next string's auipc pair) differ by layout and are not compared raw."""
import importlib.util
import os
import sys

sys.dont_write_bytecode = True
FN = '_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE'
OFF = 0x1218
TABLE_WORDS = {0x358, 0x35c}       # lib/B/Rt/YF0r.v fs_ranges: (RegisterCommonFlags + 0x358, 2 words)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


kit, ga, ua = sys.argv[1:4]
sys.path.insert(0, kit)
st = load('strictcmp3', os.path.join(kit, 'strictcmp3.py'))


def target(I):
    a, n = I.fsym(FN)
    b = st.frd(I, a, n)
    t = st.targets(a, b)
    w = st.bc_words(b)
    i = [k for k, (o, x, nb) in enumerate(w) if o == OFF][0]
    return a, n, t[i][1], w[i][1], b


def cstr0(I, x):
    r = st.region(I, x)
    if r is None or b'\0' not in r:
        return None
    return r[:r.index(b'\0') + 1]


def settled(G, xg, U, xu):
    sg, su = cstr0(G, xg), cstr0(U, xu)
    return st.readonly(G, xg) and st.readonly(U, xu) and sg is not None and sg == su, sg, su


G, U = st.Img(ga), st.Img(ua)
print('# G = %s sha256 %s\n# U = %s sha256 %s' % (ga, st.sha(ga), ua, st.sha(ua)))
ag, ng, xg, wg, bg = target(G)
au, nu, xu, wu, bu = target(U)
print('word %s+%#x: G %#x (%08x) -> %#x %s | U %#x (%08x) -> %#x %s'
      % (FN, OFF, ag + OFF, wg, xg, G.sec(xg), au + OFF, wu, xu, U.sec(xu)))
res = st.tsame(G, xg, U, xu, wg)
ok, kind, ra, rb = res[0], res[1], res[2], res[3]
print('1. kit (strictcmp3 tsame): %s %s %s / %s; region lengths %d / %d'
      % ('EQUAL' if ok else 'NOT SETTLED', kind, ra, rb, len(st.region(G, xg)), len(st.region(U, xu))))
ok2, sg, su = settled(G, xg, U, xu)
print('2. settled (read-only %s / %s; bytes up to and including the NUL %r / %r): %s'
      % (st.readonly(G, xg), st.readonly(U, xu), sg, su, 'EQUAL' if ok2 else 'DIFFERENT'))
bad = not ok2

Up = st.Img(ua)
for k, seg in enumerate(Up.segs):
    v, fz, d = seg[0], seg[1], seg[2]
    if v <= xu < v + fz:
        x = bytearray(d)
        x[xu - v] = 0x58
        Up.segs[k] = (v, fz, bytes(x)) + tuple(seg[3:])
okc, sgc, suc = settled(G, xg, Up, xu)
print('3. control, U %#x planted 0x00 -> 0x58: %r / %r: %s -> %s'
      % (xu, sgc, suc, 'EQUAL' if okc else 'DIFFERENT', 'NOT CAUGHT' if okc else 'caught'))
bad += okc

print('4. table words of %s in the proof (lib/B/Rt/YF0r.v fs_ranges): %s; +%#x among them: %s'
      % (FN, ', '.join('+%#x' % o for o in sorted(TABLE_WORDS)), OFF, OFF in TABLE_WORDS))
bad += OFF in TABLE_WORDS

def first_use(b, rd):
    """(offset, word, reason) of the first word after +OFF that reads rd; reason when there is none"""
    for o in range(OFF + 4, OFF + 0x40, 4):
        w = int.from_bytes(b[o:o + 4], 'little')
        if w & 3 != 3:
            return None, None, 'a 2-byte word before any use'
        op, rs1, rs2, wrd = w & 0x7f, (w >> 15) & 31, (w >> 20) & 31, (w >> 7) & 31
        if rs1 == rd or (op in (0x23, 0x33, 0x3b, 0x63) and rs2 == rd):
            return o, w, None
        if op not in (0x23, 0x63) and wrd == rd:
            return None, None, 'rd written again at +%#x before any use' % o
    return None, None, 'no use within 16 words'


uses = {}
for nm, b in (('G', bg), ('U', bu)):
    w0 = int.from_bytes(b[OFF:OFF + 4], 'little')
    rd = (w0 >> 7) & 31
    o, w, why = first_use(b, rd)
    is_sd = w is not None and w & 0x707f == 0x3023 and ((w >> 20) & 31) == rd
    off = (((w >> 25) << 5) | ((w >> 7) & 31)) if w is not None else None
    print('5. %s: +%#x addi writes x%d; first use: %s: %s' % (
        nm, OFF, rd, ('+%#x %08x' % (o, w)) if o else why,
        ('sd x%d, %d(x%d), stores the address into a record field' % (rd, off, (w >> 15) & 31)) if is_sd else 'NOT an sd of rd'))
    uses[nm] = (rd, o, w, is_sd)
same = uses['G'] == uses['U'] and uses['G'][3]
print('5. the consumer is the same sd word at the same offset in both images: %s' % same)
bad += not same
print('not settled, control not caught, in the table, or consumer words differ: %d' % bad)
sys.exit(1 if bad else 0)
