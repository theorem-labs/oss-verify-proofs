#!/usr/bin/env python3
"""Per-function excerpt of the three __asan_set_shadow_{00,f5,f8} stubs, and the 8-byte words of the cells they read,
in a symbol-bearing twin (pyelftools + capstone). usage: sshdis.py ELF SHA12 [FUNC ...]"""
import hashlib, sys, struct
from elftools.elf.elffile import ELFFile
from capstone import Cs, CS_ARCH_RISCV, CS_MODE_RISCV64, CS_MODE_RISCVC
path, want = sys.argv[1], sys.argv[2]
raw = open(path, 'rb').read(); h = hashlib.sha256(raw).hexdigest()
assert h.startswith(want), h
f = open(path, 'rb'); e = ELFFile(f)
loads = [(s['p_vaddr'], s['p_filesz'], s.data()) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
def rd(a, n):
    for v, fz, d in loads:
        if v <= a and a + n <= v + fz: return d[a - v:a - v + n]
    return None
syms = {}
byaddr = {}
for s in e.get_section_by_name('.symtab').iter_symbols():
    if s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT') and s['st_value']:
        syms.setdefault(s.name, []).append((s['st_value'], s['st_size'], s['st_info']['type']))
        byaddr.setdefault(s['st_value'], []).append(s.name)
def secname(a):
    for s in e.iter_sections():
        if s['sh_addr'] and s['sh_addr'] <= a < s['sh_addr'] + s['sh_size']: return s.name
    return None
md = Cs(CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC)
print('# %s sha256 %s' % (path, h))
for fn in sys.argv[3:]:
    (a, sz, t), = [x for x in syms[fn] if x[2] == 'STT_FUNC']
    code = rd(a, sz)
    print('== %s at %#x size %d (%d words) section %s' % (fn, a, sz, sz // 4, secname(a)))
    au = {}
    for ins in md.disasm(code, a):
        w = int.from_bytes(ins.bytes, 'little')
        extra = ''
        dst = ins.op_str.replace(' ', '').split(',')[0]
        if ins.mnemonic == 'auipc':
            au[dst] = ins.address + (int(ins.op_str.split(',')[1], 0) << 12)
        elif ins.mnemonic in ('ld', 'addi', 'jalr', 'jr'):
            ops = ins.op_str.replace(' ', '')
            if '(' in ops:
                off, base = ops.split(',')[-1].rstrip(')').split('(')
                if base in au:
                    tgt = (au[base] + int(off, 0)) & 0xffffffffffffffff
                    cell = rd(tgt, 8)
                    extra = '  ; -> %#x [%s %s]' % (tgt, secname(tgt), ','.join(byaddr.get(tgt, [])))
                    if ins.mnemonic == 'ld' and cell:
                        v = struct.unpack('<Q', cell)[0]
                        v2 = rd(v, 8)
                        extra += ' holds %#x [%s %s]' % (v, secname(v), ','.join(byaddr.get(v, [])))
                        if v2: extra += ' which holds %#x [%s %s]' % (struct.unpack('<Q', v2)[0], secname(struct.unpack('<Q', v2)[0]), ','.join(byaddr.get(struct.unpack('<Q', v2)[0], [])))
        if ins.mnemonic not in ('auipc', 'jr', 'jalr', 'sd', 'sw', 'sh', 'sb'): au.pop(dst, None)
        print('  %x: %0*x  %s\t%s%s' % (ins.address, 2 * ins.size, w, ins.mnemonic, ins.op_str, extra))
