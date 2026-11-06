#!/usr/bin/env python3
"""sites.py TWIN: every call into an __asan_stack_malloc_<k> of one unstripped image. It lists the image's
__asan_stack_malloc_* symbols, then scans every 4-byte jal in the executable PT_LOAD (linearly, capstone RISCV64 | RVC)
for a target that is one of them, and prints each call site with its function, the class and the last write of a0
before the call in the same function (the frame size argument)."""
import sys

import capstone
from elftools.elf.elffile import ELFFile

e = ELFFile(open(sys.argv[1], 'rb'))
syms = [(s['st_value'], s['st_size'], s.name) for s in e.get_section_by_name('.symtab').iter_symbols()
        if s['st_info']['type'] == 'STT_FUNC' and s['st_size'] > 0]
sm = {a: n for a, sz, n in syms if n.startswith('__asan_stack_malloc_')}
print('stack_malloc symbols:', ', '.join(f'{n} {a:#x}' for a, n in sorted(sm.items())) or 'none')


def owner(a):
    best = None
    for st, sz, n in syms:
        if st <= a < st + sz and (best is None or sz < best[1]):
            best = (st, sz, n)
    return best


md = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
n_jal = 0
for p in e.iter_segments():
    if p['p_type'] != 'PT_LOAD' or not p['p_flags'] & 1:
        continue
    code, base = p.data(), p['p_vaddr']
    off = 0
    while off < len(code):
        got = list(md.disasm(code[off:off + 4], base + off, 1))
        if not got:
            off += 2
            continue
        ins = got[0]
        if ins.mnemonic == 'jal':
            n_jal += 1
            t = ins.address + int(ins.op_str.split(',')[-1], 0)
            if t in sm:
                st, sz, fn = owner(ins.address)
                a0 = None
                for j in md.disasm(code[st - base:ins.address - base], st):
                    if j.op_str.split(',')[0].strip() == 'a0':
                        a0 = f'{j.address:#x} {j.mnemonic} {j.op_str}'
                print(f'call {ins.address:#x} in {fn} ({st:#x}, {sz} bytes) -> {sm[t]}; last a0 write: {a0}')
        off += ins.size
print(f'jal scanned: {n_jal}')
