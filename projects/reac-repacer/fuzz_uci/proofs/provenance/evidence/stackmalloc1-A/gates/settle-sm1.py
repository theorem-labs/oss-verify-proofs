#!/usr/bin/env python3
"""settle-sm1.py DONOR_TWIN TARGET_TWIN: the named measurement of the one target the comparison kit 4bbd3a74be89 does not
certify in this slice: __sanitizer::RegisterCommonFlags +0x1218, an address taken (auipc +0x1210, addi +0x1218) of an
unnamed .rodata place whose first byte is NUL. The kit compares such a place by its whole region to the next symbol
(fail-closed); this script settles it as a C string, or refuses. DONOR_TWIN / TARGET_TWIN: the unstripped twins
(fuzz_grant.asan 57c26f993615, fuzz_uci.asan 56822e263d76). Read-only; pyelftools + capstone (RISCV64 | RVC).

For each image it prints and checks:
  1. the place: the auipc / addi pair at +0x1210 / +0x1218 and its target address; the C string there up to and
     including its NUL;
  2. the consumer in RegisterCommonFlags: every instruction from +0x121c to the function's end (straight-line: the
     script refuses on a branch); every read of the addi's destination register until it is written again; each read
     must be a store of it to field +0x18 of an object whose field +0 receives the FlagHandlerInclude vtable address
     point (_ZTVN11__sanitizer18FlagHandlerIncludeE + 0x10) in the same scan;
  3. that class's methods (the vtable's two entries after the address point): every access to field +0x18 of the object
     (the object pointer tracked through register copies); a store is a write; a load must be the C-string argument of a
     call whose format string, read from the image, is exactly "%s"; no call may receive the object pointer.
Verdict: SETTLED EQUAL AS A C STRING when both places are the same C string and every consumer reads the place only as
a "%s" argument (which reads up to the NUL), else NOT SETTLED (exit 1)."""
import hashlib, sys

import capstone
from elftools.elf.elffile import ELFFile

FN = '_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE'
VT = '_ZTVN11__sanitizer18FlagHandlerIncludeE'
OFF_HI, OFF_LO, FIELD = 0x1210, 0x1218, 0x18
STORES = ('sd', 'sw', 'sh', 'sb')
MD = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)


class Img:
    def __init__(self, path):
        self.path, self.sha = path, hashlib.sha256(open(path, 'rb').read()).hexdigest()
        self.e = ELFFile(open(path, 'rb'))
        self.segs = [(g['p_vaddr'], g['p_filesz'], g.data()) for g in self.e.iter_segments() if g['p_type'] == 'PT_LOAD']
        self.syms = [(s['st_value'], s['st_size'], s.name) for s in self.e.get_section_by_name('.symtab').iter_symbols()
                     if s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT') and s['st_size'] > 0]

    def rd(self, a, n):
        """file bytes only"""
        return next((d[a - v:a - v + n] for v, fz, d in self.segs if v <= a and a + n <= v + fz), None)

    def sym(self, name):
        c = [(v, z) for v, z, n in self.syms if n == name]
        if len(c) != 1:
            sys.exit('%s: %d symbols named %s' % (self.path, len(c), name))
        return c[0]

    def where(self, a):
        c = [(z, v, n) for v, z, n in self.syms if v <= a < v + z]
        if not c:
            return '(%s)' % next((s.name for s in self.e.iter_sections() if s['sh_addr'] <= a < s['sh_addr'] + s['sh_size']), '?')
        z, v, n = min(c)
        return '%s+%#x' % (n, a - v)

    def cstr(self, a):
        b = self.rd(a, 4096) or b''
        z = b.find(b'\0')
        return b[:z + 1] if z >= 0 else None


def ops(i):
    return [o.strip() for o in i.op_str.split(',')] if i.op_str else []


def imm(s):
    return int(s, 0)


def auipc_addi(img, hi_pc, lo_pc):
    (h,), (l,) = list(MD.disasm(img.rd(hi_pc, 4), hi_pc)), list(MD.disasm(img.rd(lo_pc, 4), lo_pc))
    ho, lo = ops(h), ops(l)
    assert h.mnemonic == 'auipc' and l.mnemonic == 'addi' and lo[1] == ho[0], (h.mnemonic, h.op_str, l.mnemonic, l.op_str)
    u = imm(ho[1]) & 0xfffff
    u = u - 0x100000 if u & 0x80000 else u
    return lo[0], (hi_pc + (u << 12) + imm(lo[2])) % (1 << 64)


def call_target(i):
    return i.address + imm(ops(i)[-1]) if i.mnemonic in ('jal', 'j') else None


def measure(img, out):
    bad = []
    fa, fz = img.sym(FN)
    reg, place = auipc_addi(img, fa + OFF_HI, fa + OFF_LO)
    s = img.cstr(place)
    out.append('  place: auipc +%#x / addi +%#x -> %s = %#x %s; C string at it (with its NUL): %r (%d byte(s))'
               % (OFF_HI, OFF_LO, reg, place, img.where(place), s, len(s) if s else 0))
    va, vz = img.sym(VT)
    # the vtable address point register: the auipc / addi pair just before (+0x120c / +0x1214)
    vreg, vaddr = auipc_addi(img, fa + 0x120c, fa + 0x1214)
    out.append('  vtable register %s = %#x %s (FlagHandlerInclude vtable + 0x10: %s)'
               % (vreg, vaddr, img.where(vaddr), vaddr == va + 0x10))
    if vaddr != va + 0x10:
        bad.append('the register stored at field +0 is not the FlagHandlerInclude address point')
    out.append('  RegisterCommonFlags from +0x121c to its end:')
    vt_at, vreg_ok = set(), True
    for i in MD.disasm(img.rd(fa + 0x121c, fz - 0x121c), fa + 0x121c):
        o = ops(i)
        t = call_target(i)
        out.append('    +%#x %s %s%s' % (i.address - fa, i.mnemonic, i.op_str, ' -> ' + img.where(t) if t else ''))
        if i.mnemonic.startswith('b') or i.mnemonic in ('jr', 'jalr'):
            bad.append('branch at +%#x: not straight-line' % (i.address - fa))
        if i.mnemonic in STORES:
            src, mem = o[0], o[1]
            moff, base = mem[:-1].split('(')
            if src == vreg and vreg_ok and imm(moff or '0') == 0:
                vt_at.add(base)
            if src == reg:
                ok = imm(moff or '0') == FIELD and base in vt_at
                out.append('      READ of %s: stored to field %s of the object in %s (its field +0 holds the vtable: %s)'
                           % (reg, moff, base, base in vt_at))
                if not ok:
                    bad.append('use of %s at +%#x is not a store to field +0x18 of a FlagHandlerInclude' % (reg, i.address - fa))
            continue
        if i.mnemonic in ('j', 'jal', 'ret'):
            if i.mnemonic == 'j':
                break       # the tail call ends the function
            continue
        if o and o[0] == vreg and vreg != reg:
            vreg_ok = False     # later stores of this register no longer carry the vtable address
        if any(x == reg or x.endswith('(%s)' % reg) for x in o[1:]):
            bad.append('other read of %s at +%#x: %s %s' % (reg, i.address - fa, i.mnemonic, i.op_str))
        if o and o[0] == reg:
            out.append('      %s written again here: its value ends' % reg)
            break
        if o and o[0] in vt_at:
            vt_at.discard(o[0])
    ents = [int.from_bytes(img.rd(va + k, 8), 'little') for k in (0x10, 0x18)]
    out.append('  vtable entries after the address point: %s' % ', '.join('%#x %s' % (x, img.where(x)) for x in ents))
    if [img.where(x) for x in ents] != ['_ZN11__sanitizer18FlagHandlerInclude5ParseEPKc+0x0',
                                        '_ZN11__sanitizer18FlagHandlerInclude6FormatEPcm+0x0']:
        bad.append('the vtable entries are not Parse / Format')
    for m in ents:
        ma, mz = next((v, z) for v, z, n in img.syms if v == m)
        out.append('  %s:' % img.where(m))
        obj, regs, fmt = {'a0'}, {}, None
        # every register that ever receives a copy of the object pointer (flow-insensitive, so a field access on any
        # path is seen); `obj` below is the in-order copy set used for the call arguments
        mins = list(MD.disasm(img.rd(ma, mz), ma))
        objfi, grew = {'a0'}, True
        while grew:
            grew = False
            for i in mins:
                o = ops(i)
                if i.mnemonic == 'mv' and o[1] in objfi and o[0] not in objfi:
                    objfi.add(o[0]); grew = True
        out.append('    (registers holding the object pointer somewhere in the method: %s)' % sorted(objfi))
        for i in MD.disasm(img.rd(ma, mz), ma):
            o = ops(i)
            t = call_target(i)
            out.append('    +%#x %s %s%s' % (i.address - ma, i.mnemonic, i.op_str, ' -> ' + img.where(t) if t else ''))
            if i.mnemonic in STORES:
                moff, base = o[1][:-1].split('(')
                if base in objfi and imm(moff or '0') == FIELD:
                    out.append('      WRITE of field +0x18 (%s): the place is not read here' % o[0])
                continue
            if i.mnemonic == 'auipc':
                regs[o[0]] = ('hi', i.address, imm(o[1]))
            elif i.mnemonic == 'addi' and len(o) == 3 and regs.get(o[1], (None,))[0] == 'hi':
                _, pc, u = regs[o[1]]
                u = (u & 0xfffff) - 0x100000 if u & 0x80000 else u & 0xfffff
                regs[o[0]] = ('addr', (pc + (u << 12) + imm(o[2])) % (1 << 64))
            if i.mnemonic in ('ld', 'lw', 'lwu', 'lh', 'lhu', 'lb', 'lbu'):
                moff, base = o[1][:-1].split('(')
                if base in objfi and imm(moff or '0') == FIELD:
                    regs[o[0]] = ('field',)
                    out.append('      READ of field +0x18 into %s' % o[0])
            if i.mnemonic in ('jal', 'j'):
                args = ['a%d' % k for k in range(8)]
                if any(a in obj for a in args):
                    bad.append('a call at %s +%#x receives the object pointer' % (img.where(m), i.address - ma))
                fr = [a for a in args if regs.get(a, (None,))[0] == 'field']
                if fr:
                    fa_ = regs.get('a2', (None, None))
                    fmt = img.cstr(fa_[1]) if fa_[0] == 'addr' else None
                    out.append('      the field is argument %s of %s; format string a2 = %r'
                               % (fr, img.where(t), fmt))
                    if fmt != b'%s\x00' or fr != ['a3'] or not img.where(t).startswith('_ZN11__sanitizer17internal_snprintf'):
                        bad.append('the field is not the "%%s" argument of internal_snprintf at %s +%#x' % (img.where(m), i.address - ma))
                for a in args:
                    regs.pop(a, None)
            if i.mnemonic == 'mv' and o[1] in obj:
                obj.add(o[0])
            elif o and i.mnemonic not in ('jal', 'j', 'ret') and o[0] in obj and not (i.mnemonic == 'mv' and o[1] in obj):
                obj.discard(o[0])
            if o and i.mnemonic not in ('auipc', 'addi', 'ld', 'lw', 'lwu', 'lh', 'lhu', 'lb', 'lbu', 'jal', 'j', 'ret') \
                    and o[0] in regs:
                regs.pop(o[0])
            if i.mnemonic == 'mv' and o[1] in regs:
                regs[o[0]] = regs[o[1]]
    return place, s, bad


def main():
    out, res = [], []
    for role, p in (('donor', sys.argv[1]), ('target', sys.argv[2])):
        img = Img(p)
        out.append('%s %s sha256 %s' % (role, p.rsplit('/', 1)[-1], img.sha[:12]))
        res.append(measure(img, out))
    (pd, sd, bd), (pt, st, bt) = res
    same = sd is not None and sd == st
    out.append('C strings: donor %r, target %r: %s' % (sd, st, 'the same C string' if same else 'DIFFERENT'))
    for who, b in (('donor', bd), ('target', bt)):
        for x in b:
            out.append('REFUSED (%s): %s' % (who, x))
    ok = same and not bd and not bt
    out.append('VERDICT: %s' % ('SETTLED EQUAL AS A C STRING (RegisterCommonFlags +0x1218: both places the C string %r; '
                                'the one consumer reads it only as the "%%s" argument of internal_snprintf)' % sd
                                if ok else 'NOT SETTLED'))
    print('\n'.join(out))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
