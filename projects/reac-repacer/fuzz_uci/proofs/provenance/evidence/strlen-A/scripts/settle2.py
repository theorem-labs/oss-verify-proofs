#!/usr/bin/env python3
"""settle2.py U_ELF R_ELF OUT_TSV: settles, by a named measurement on both images, the two not-certified closure rows of the
memchr / strlen evidence slices that a fresh reviewer found settleable (2026-10-30):

  (1) __nl_langinfo_l+0xf8: `auipc a0,..; addi a0,a0,..` @+0xf4/+0xf8 forms the address of an unnamed empty string.
      Measured: the byte there is NUL in both images; the next instructions are `bnez a3` -> `ret` (@+0xfc, +0x118) and
      `lbu a3,0(a0)` @+0x100, `beqz a3` -> `ret` (@+0x104): the code reads one byte, the NUL, and then returns the address
      (the `j __lctrans` @+0x114 is reached only when that byte is not NUL). The returned value's consumers are those of
      the accepted row `__nl_langinfo_l+0x5c` (same `ret`).
  (2) RegisterCommonFlags+0x1218: `auipc a1; addi s2,a1,..` forms the address of the same kind of empty string, which is
      stored as `sd s2,0x18(a2)` @+0x1228 and @+0x1274 into two new objects whose word 0 is `s1` (@+0x121c, @+0x1268).
      Measured: s1 = the vtable of __sanitizer::FlagHandlerInclude + 16; that vtable's two methods are Parse and Format;
      Parse only writes the field (a `sd a1,0x18(a0)`, no load of 0x18(a0)); Format loads it (`ld a3,0x18(a0)`) and passes it
      as a3 to its one call, whose a2 is the string "%s". So the field's one reader prints it with %s, which reads to the NUL.
      [Method limit: that no code outside these two methods reads the field is a property of the class (the field is the
      handler's own), not measured here.]
Each check prints PASS / FAIL with the instruction it read; exit 1 if any check fails in either image.
"""
import sys
import capstone
from elftools.elf.elffile import ELFFile

NL = '__nl_langinfo_l'
RC = '_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE'
VT = '_ZTVN11__sanitizer18FlagHandlerIncludeE'
PARSE = '_ZN11__sanitizer18FlagHandlerInclude5ParseEPKc'
FORMAT = '_ZN11__sanitizer18FlagHandlerInclude6FormatEPcm'
MD = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)


class Img:
    def __init__(s, p):
        s.e = ELFFile(open(p, 'rb'))
        s.sym = {}
        for x in s.e.get_section_by_name('.symtab').iter_symbols():
            s.sym.setdefault(x.name, []).append(x['st_value'])
        s.segs = [(g['p_vaddr'], g['p_filesz'], g.data()) for g in s.e.iter_segments() if g['p_type'] == 'PT_LOAD']

    def one(s, n):
        v = s.sym.get(n, [])
        if len(v) != 1:
            raise SystemExit('settle2: %s has %d symbol entries' % (n, len(v)))
        return v[0]

    def rd(s, a, n):
        for v, z, d in s.segs:
            if v <= a and a + n <= v + z:
                return d[a - v:a - v + n]
        raise SystemExit('settle2: %#x not loaded' % a)

    def ins(s, fn, lo, hi):
        a = s.one(fn)
        return {i.address - a: i for i in MD.disasm(s.rd(a, hi), a) if lo <= i.address - a < hi}

    def cstr(s, a):
        b = s.rd(a, 64)
        return b.split(b'\0')[0]


def auipc_pair(ins, p1, p2, rd2):
    a, b = ins[p1], ins[p2]
    assert a.mnemonic == 'auipc' and b.mnemonic == 'addi', (a.mnemonic, b.mnemonic)
    hi = int(a.op_str.split(',')[1], 0)
    lo = int(b.op_str.split(',')[2], 0)
    assert b.op_str.split(',')[0].strip() == rd2
    return (a.address + ((hi << 12) if hi < (1 << 19) else ((hi - (1 << 20)) << 12)) + lo) & ((1 << 64) - 1)


rows, bad = [], 0


def check(img, name, ok, what):
    global bad
    rows.append((img, name, 'PASS' if ok else 'FAIL', what))
    if not ok:
        bad += 1


for tag, path in (('U', sys.argv[1]), ('R', sys.argv[2])):
    I = Img(path)
    n = I.ins(NL, 0xf4, 0x11c)
    s = auipc_pair(n, 0xf4, 0xf8, 'a0')
    check(tag, NL + '+0xf8', I.rd(s, 1) == b'\0', 'string @%#x first byte %s' % (s, I.rd(s, 1).hex()))
    for off, mn, op in ((0xfc, 'bnez', 'a3'), (0x100, 'lbu', 'a3, 0(a0)'), (0x104, 'beqz', 'a3'), (0x118, 'ret', '')):
        i = n[off]
        check(tag, NL + '+%#x' % off, i.mnemonic == mn and i.op_str.startswith(op), '%s %s' % (i.mnemonic, i.op_str))
    for off in (0xfc, 0x104):
        i = n[off]; tgt = i.address + int(i.op_str.split(',')[1], 0)
        check(tag, NL + '+%#x target' % off, tgt - I.one(NL) == 0x118, 'branch to +%#x' % (tgt - I.one(NL)))
    r = I.ins(RC, 0x120c, 0x1278)
    s2 = (r[0x1210].address + (((int(r[0x1210].op_str.split(',')[1], 0) ^ (1 << 19)) - (1 << 19)) << 12)
          + int(r[0x1218].op_str.split(',')[2], 0)) & ((1 << 64) - 1)
    s1 = (r[0x120c].address + (((int(r[0x120c].op_str.split(',')[1], 0) ^ (1 << 19)) - (1 << 19)) << 12)
          + int(r[0x1214].op_str.split(',')[2], 0)) & ((1 << 64) - 1)
    check(tag, RC.split('E')[0] + '+0x1218', r[0x1218].op_str.startswith('s2, a1') and I.rd(s2, 1) == b'\0',
          'addi %s; string @%#x first byte %s' % (r[0x1218].op_str, s2, I.rd(s2, 1).hex()))
    check(tag, 'vtable', s1 == I.one(VT) + 16, 's1 = %#x, FlagHandlerInclude vtable + 16 = %#x' % (s1, I.one(VT) + 16))
    for off in (0x1228, 0x1274):
        check(tag, 'store +%#x' % off, r[off].mnemonic == 'sd' and r[off].op_str == 's2, 0x18(a2)', '%s %s' % (r[off].mnemonic, r[off].op_str))
    for off in (0x121c, 0x1268):
        check(tag, 'vptr +%#x' % off, r[off].mnemonic == 'sd' and r[off].op_str == 's1, 0(a2)', '%s %s' % (r[off].mnemonic, r[off].op_str))
    m = [int.from_bytes(I.rd(s1 + 8 * k, 8), 'little') for k in range(2)]
    check(tag, 'vtable methods', m == [I.one(PARSE), I.one(FORMAT)], 'slots %s' % [hex(x) for x in m])
    pa = I.ins(PARSE, 0, 0x40)
    check(tag, 'Parse', not any(i.mnemonic.startswith('l') and '0x18(a0)' in i.op_str for i in pa.values())
          and any(i.mnemonic == 'sd' and i.op_str.endswith('0x18(a0)') for i in pa.values()),
          'loads of 0x18(a0): %d; stores: %d' % (sum(1 for i in pa.values() if i.mnemonic.startswith('l') and '0x18(a0)' in i.op_str),
                                                 sum(1 for i in pa.values() if i.mnemonic == 'sd' and i.op_str.endswith('0x18(a0)'))))
    fo = I.ins(FORMAT, 0, 0x40)
    ld = [o for o, i in fo.items() if i.mnemonic == 'ld' and i.op_str == 'a3, 0x18(a0)']
    calls = [o for o, i in fo.items() if i.mnemonic in ('jal', 'j', 'tail')]
    fmt, callee = None, None
    for o in sorted(fo):
        i = fo[o]
        if i.mnemonic == 'addi' and i.op_str.startswith('a2, '):
            src = i.op_str.split(',')[1].strip()
            au = [p for p in sorted(fo) if p < o and fo[p].mnemonic == 'auipc' and fo[p].op_str.startswith(src + ',')]
            if au:
                p = au[-1]
                v = (fo[p].address + (((int(fo[p].op_str.split(',')[1], 0) ^ (1 << 19)) - (1 << 19)) << 12)
                     + int(i.op_str.split(',')[2], 0)) & ((1 << 64) - 1)
                fmt = I.cstr(v)
    if len(calls) == 1:
        c = fo[calls[0]]; t = c.address + int(c.op_str.split(',')[-1], 0)
        callee = [n for n, v in I.sym.items() if t in v and n]
    check(tag, 'Format', len(ld) == 1 and len(calls) == 1 and fmt == b'%s' and any('internal_snprintf' in n for n in (callee or [])),
          'ld a3,0x18(a0) at %s; one call at %s to %s; a2 = %r' % ([hex(x) for x in ld], [hex(x) for x in calls], callee, fmt))

open(sys.argv[3], 'w').write('image\tcheck\tresult\tmeasured\n' + ''.join('%s\t%s\t%s\t%s\n' % r for r in rows))
print('settle2: %d checks, %d failed' % (len(rows), bad))
sys.exit(1 if bad else 0)
