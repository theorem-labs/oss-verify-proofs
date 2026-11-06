#!/usr/bin/env python3
"""luitrace-B.py TWIN: the hand dataflow check (registry 18:50Z KNOWN LIMIT: the kit's lui dataflow does not follow
add / sub / shNadd) for the lui-built values strictcmp3 reports in __strftime_fmt_1 and MaybeReleaseToOS of
libdiginet fuzz_transport.asan-ubsan (the same instruction words on the donor, settle5-B.out). From the instruction
after each value is formed, the register is followed through every instruction (unconditional jumps followed, register
copies / add / sub / shNadd followed into their destination) until it is overwritten, passed to a call, read by a
branch, or used as a MEMORY BASE (a load / store `off(reg)`), which would make the value an address. Expected: no
MEMORY BASE. The switch dispatch at +0x64 (`jr t2`) is followed into every one of its case targets."""
import capstone, struct, re, sys
from elftools.elf.elffile import ELFFile

e = ELFFile(open(sys.argv[1], 'rb'))
syms = {y['st_value']: y.name for y in e.get_section_by_name('.symtab').iter_symbols() if y['st_info']['type'] == 'STT_FUNC'}
fsz = {y.name: (y['st_value'], y['st_size']) for y in e.get_section_by_name('.symtab').iter_symbols()
       if y['st_info']['type'] == 'STT_FUNC' and y['st_size']}
seg = [(g['p_vaddr'], g.data()) for g in e.iter_segments() if g['p_type'] == 'PT_LOAD']
rd = lambda a, n: next(d[a - v:a - v + n] for v, d in seg if v <= a < v + len(d))
MD = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
REG = re.compile(r'\b(zero|ra|sp|gp|tp|t[0-6]|s1[01]|s[0-9]|a[0-7])\b')
STORE = ('sd', 'sw', 'sh', 'sb', 'fsd', 'fsw')
BR = ('beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'beqz', 'bnez', 'bltz', 'bgez', 'blez', 'bgtz', 'jr', 'ret')
COPY = ('mv', 'add', 'addw', 'addi', 'addiw', 'sub', 'subw', 'sh1add', 'sh2add', 'sh3add', 'slli', 'slliw')


def fn(name):
    A, N = fsz[name]
    ins = {x.address: x for x in MD.disasm(rd(A, N), A)}
    return A, N, ins, sorted(ins)


def trace(F, a, reg, seen=None):
    A, N, ins, order = F
    seen = set() if seen is None else seen
    out = []
    while a is not None and A <= a < A + N and a not in seen:
        seen.add(a)
        x = ins[a]
        regs = REG.findall(x.op_str)
        o = '%+#x %s %s' % (a - A, x.mnemonic, x.op_str)
        if x.mnemonic == 'jal' and (len(x.op_str.split(',')) == 1 or regs[:1] == ['ra']):
            t = x.address + int(x.op_str.split(',')[-1], 0)
            out.append(f'CALL {o} <{syms.get(t, hex(t))}> ({reg} live: an argument register at the call)')
            return out
        m = re.search(r'\((\w+)\)', x.op_str)
        if m and m.group(1) == reg:
            out.append('MEMORY BASE ' + o)
            return out
        reads = set(regs) if x.mnemonic in STORE + BR else set(regs[1:])
        if reg in reads:
            out.append('read ' + o)
            if x.mnemonic in BR:
                return out
            dst = regs[0]
            if x.mnemonic in COPY and dst != reg:
                i = order.index(a)
                out.append('{' + dst + ': ' + ' | '.join(trace(F, order[i + 1], dst, set(seen))) + '}')
            elif x.mnemonic not in COPY:
                out.append(f'  ({x.mnemonic}: arithmetic use, the result is no address of this value)')
        if regs[:1] == [reg] and x.mnemonic not in STORE + BR and not (reg in reads and x.mnemonic in COPY):
            out.append('overwritten ' + o)
            return out
        if x.mnemonic in ('j',):
            a = x.address + int(x.op_str.split(',')[-1], 0)
            continue
        if x.mnemonic in ('ret', 'jr'):
            out.append('end ' + o)
            return out
        i = order.index(a)
        a = order[i + 1] if i + 1 < len(order) else None
    return out


S = fn('__strftime_fmt_1')
A = S[0]
tb = A + 0x44
# the table base the dispatch adds: read it from settle5-B.out's rel4 row (T 0x22994); recomputed here from the bytes
base = 0x22994
cases = sorted({base + struct.unpack('<i', rd(base + 4 * i, 4))[0] for i in range(86)})
print(f'# __strftime_fmt_1 at {A:#x}: a1 = 0x20028 (+0x58 lui t1, 0x20; +0x60 addiw a1, t1, 0x28) before +0x64 jr t2; '
      f'{len(cases)} distinct case targets of the 86-entry rel4 table at {base:#x}')
for c in cases:
    print('case %+#x: %s' % (c - A, ' | '.join(trace(S, c, 'a1'))))
for st, r, v in ((0xf4, 'a0', '0x20007 + a0 (+ 7)'), (0x14c, 'a1', '0x2002a'), (0x258, 'a1', '0x2002b'),
                 (0x470, 'a1', '0x20029'), (0x4f0, 'a0', '0x20007 + a0 (+ 0x13)'), (0x500, 'a0', '0x20007 + a0')):
    print(f'# from {st:+#x} follow {r} = {v}: ' + ' | '.join(trace(S, A + st, r)))
M = fn('_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16MaybeReleaseToOSEPNS_12MemoryMapperIS5_EEmb')
print(f'# MaybeReleaseToOS at {M[0]:#x}: a3 = 0xf4240 (1000000) from +0xe0: ' + ' | '.join(trace(M, M[0] + 0xe0, 'a3')))
