#!/usr/bin/env python3
"""vreader.py -- the reader behind the one virtual call escape.py could not resolve statically: the field
common_flags_dont_use + 0x18 (CommonFlags::SetDefaults +0x48 stores the empty string there) is loaded by
StackTraceTextPrinter::ProcessAddressFrames and by ReportErrorSummary(const char*, const AddressInfo&, const char*), and
passed in a7 (the 8th argument) to `jalr t1` with t1 = slot 0 of the printer object's vtable (`ld t0, 0(obj) ; ld t1, 0(t0)`).
For each image: every vtable symbol (_ZTV...) whose name holds `StackTracePrinter`, the function in its slot 0 (the
address point is vtable + 16: offset-to-top, typeinfo, then the slots), and escape.track() of a7 in that function.
Also prints the reader loads (function, word, register) so the a7 claim can be checked. usage: vreader.py"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common, escape

FIELD = 0x18


def main():
    for tag, path in (('cgif B', common.CGIF_B_TWIN), ('decode B', common.DECODE_B_TWIN)):
        img = escape.Image(path)
        img._index()
        owner = [v for v, z, n, t in img.I.syms if n == '_ZN11__sanitizer21common_flags_dont_useE'][0]
        cells = [g for g in range(*img.gotrange()) if escape.sc.frd(img.I, g, 8) == owner.to_bytes(8, 'little')]
        print('== %s: common_flags_dont_use %#x, .got cells %s' % (tag, owner, [hex(c) for c in cells]))
        for g in cells:
            for v, z, o, opc in img.refs.get(g, []):
                if opc != 0x03:
                    continue
                ins = img.dis(v, z); k = [i for i, x in enumerate(ins) if x[0] == o][0]
                r = ins[k][2].split(',')[0].strip()
                for j in range(k + 1, min(len(ins), k + 64)):
                    oj, mj, pj, nj = ins[j]
                    m = re.match(r'(\w+), (-?(?:0x[0-9a-f]+|\d+))\(%s\)$' % r, pj)
                    if mj == 'ld' and m and int(m.group(2), 0) == FIELD:
                        nxt = [x for x in ins[j + 1:j + 40] if x[1] in ('jalr', 'jal')][:1]
                        print('  reader %s +%#x: ld %s, %#x(%s)   next call: %s' % (
                            img.name_at(v)[:80], oj, m.group(1), FIELD, r, nxt))
                    if pj and pj.split(',')[0].strip() == r and mj not in escape.ST and mj not in escape.BR:
                        break                                  # the base register is overwritten: stop
        vt = [(v, z, n) for v, z, n, t in img.I.syms if n.startswith('_ZTV') and 'StackTracePrinter' in n]
        for v, z, n in vt:
            slot0 = int.from_bytes(escape.sc.frd(img.I, v + 16, 8), 'little')
            fn = img.name_at(slot0)
            fz = [x for x in img.funcs if x[0] == slot0]
            us = escape.track(img, slot0, fz[0][1], 0, {'a7'}) if fz else set()
            print('  vtable %s (%#x, %d B): slot 0 = %s (%#x); a7 there: %s' % (
                n, v, z, fn, slot0, ' ; '.join(sorted(' '.join(u) for u in us)) or 'no use found'))
        heap_handler(img)


def heap_handler(img):
    """RegisterCommonFlags +0x1218 stores the empty string at a2 + 0x18 of a heap object whose word 0 it sets from another
    register at the same site: that register's value (escape.reg_value) is the object's vtable address point. Every
    function in the vtable's slots that loads 0x18(a0) (a0 = this, not yet overwritten) is a reader; its loaded register
    is followed with escape.track()."""
    fn = '_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE'
    a, z = img.I.fsym(fn)
    ins = img.dis(a, z)
    k0 = [i for i, x in enumerate(ins) if x[0] == 0x1218][0]
    st0 = [i for i in range(k0, min(len(ins), k0 + 16)) if ins[i][1] == 'sd' and ins[i][2].endswith('0x18(a2)')][0]
    w0 = [i for i in range(k0 - 16, st0 + 1) if ins[i][1] == 'sd' and re.match(r'\w+, (0x0|0)?\(a2\)$', ins[i][2])]
    vreg = ins[w0[-1]][2].split(',')[0].strip()
    vtp = img.reg_value(a, z, w0[-1], vreg)
    sym = [(v, zz, n) for v, zz, n, t in img.I.syms if t == 'STT_OBJECT' and vtp is not None and v <= vtp < v + zz]
    print('  RegisterCommonFlags +0x1218: the empty string is stored at a2+0x18 (+%#x); word 0 of that object := %s = %s (%s)' % (
        ins[st0][0], vreg, hex(vtp) if vtp else None, '%s+%#x' % (sym[0][2], vtp - sym[0][0]) if sym else 'no symbol'))
    if not sym:
        return
    v0, z0, n0 = sym[0]
    for slot in range(vtp, v0 + z0, 8):
        f = int.from_bytes(escape.sc.frd(img.I, slot, 8), 'little')
        fz = [x for x in img.funcs if x[0] == f]
        if not fz:
            continue
        fins = img.dis(f, fz[0][1])
        reads = []
        for j, (oj, mj, pj, nj) in enumerate(fins):
            if mj == 'ld' and re.match(r'\w+, 0x18\(a0\)$', pj):
                us = escape.track(img, f, fz[0][1], j + 1, {pj.split(',')[0].strip()})
                reads.append('+%#x: %s' % (oj, ' ; '.join(sorted(' '.join(u) for u in us)) or 'no use found'))
            if pj and pj.split(',')[0].strip() == 'a0' and mj not in escape.ST and mj not in escape.BR:
                break                                          # this (a0) overwritten: later loads are not of the object
        print('    slot +%#x: %s -- loads 0x18(this): %s' % (slot - vtp, img.name_at(f)[:90], ' | '.join(reads) or 'none'))


if __name__ == '__main__':
    main()
