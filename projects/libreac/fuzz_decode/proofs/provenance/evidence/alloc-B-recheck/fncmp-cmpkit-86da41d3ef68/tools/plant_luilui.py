#!/usr/bin/env python3
"""plant_luilui.py -- the two controls the lui+lui -> base check (luilui.py, FAIL-OPEN #3) must REFUSE, each a FILE copy
of the cgif-B unstripped twin with one word or one byte changed (written to PLANTDIR, never into the record):
  (c) LUILUI-OBJECT: in LargeMmapAllocator<NoOpMapUnmapCallback, ..Static..>::Allocate (cgif-B 0x5e6bc), the site
      +0x258 `ld a3, 0x40(a2)` reads base (the allocator object) + 0x40040 + index; its displacement is built by
      `lui a3, 0x40` (+0x24c). The plant makes it `lui a3, 0x41` (0x000416b7): the same base, another field.
  (d) LUILUI-TABLE: in SizeClassAllocator64<..>::PackedCounterArray::PackedCounterArray (cgif-B 0x34b18), the site
      +0x19c `lbu a2, 0(a2)` reads the 64-byte table at 0x104e8 through a lui-built index. The plant flips one byte of
      that table (0x104e8 + 5, XOR 0xff).
Each original word / byte is checked before it is changed. Then luilui.py runs with CGIF_B_TWIN = the planted copy
(and the real decode-B twin), in a scratch record (its own scans/, the record's out/ read only), and the plant's
function must come out DIFFERS. usage: PLANTDIR=... plant_luilui.py"""
import hashlib, os, shutil, struct, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common
from elftools.elf.elffile import ELFFile

FN_C, FN_D = 0x5e6bc, 0x34b18


def main():
    out = os.environ.get('PLANTDIR')
    if not out:
        raise SystemExit('PLANTDIR is not set')
    os.makedirs(out, exist_ok=True)
    src = common.CGIF_B_TWIN
    e = ELFFile(open(src, 'rb'))
    loads = [(s['p_vaddr'], s['p_offset'], s['p_filesz']) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
    foff = lambda va: [o + va - v for v, o, n in loads if v <= va < v + n][0]
    from capstone import Cs, CS_ARCH_RISCV, CS_MODE_RISCV64, CS_MODE_RISCVC
    md = Cs(CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC)
    orig = open(src, 'rb').read()
    # (c): one instruction word
    data = bytearray(orig)
    fo = foff(FN_C + 0x24c)
    ins = next(md.disasm(bytes(data[fo:fo + 4]), FN_C + 0x24c))
    if '%s %s' % (ins.mnemonic, ins.op_str) != 'lui a3, 0x40':
        raise SystemExit('plant c: found %s %s' % (ins.mnemonic, ins.op_str))
    data[fo:fo + 4] = struct.pack('<I', 0x000416b7)
    ins2 = next(md.disasm(bytes(data[fo:fo + 4]), FN_C + 0x24c))
    print('plant c: %#x +0x24c  lui a3, 0x40  ->  %s %s' % (FN_C, ins2.mnemonic, ins2.op_str))
    pc = os.path.join(out, 'planted-c.elf')
    open(pc, 'wb').write(data)
    # (d): one table byte
    data = bytearray(orig)
    fo = foff(0x104e8 + 5)
    old = data[fo]
    data[fo] = old ^ 0xff
    print('plant d: table byte 0x104ed  %#04x  ->  %#04x' % (old, data[fo]))
    pd = os.path.join(out, 'planted-d.elf')
    open(pd, 'wb').write(data)
    print('original sha256 %s' % hashlib.sha256(orig).hexdigest()[:16])
    res = {}
    for tag, path, fn in (('c', pc, FN_C), ('d', pd, FN_D)):
        print('  planted-%s sha256 %s' % (tag, hashlib.sha256(open(path, 'rb').read()).hexdigest()[:16]))
        rec = tempfile.mkdtemp(prefix='luilui-plant-%s-' % tag, dir=out)
        os.makedirs(os.path.join(rec, 'scans'))
        os.symlink(common.OUT, os.path.join(rec, 'out'))
        shutil.copy(os.path.join(common.SCANS, 'exposure.tsv'), os.path.join(rec, 'scans'))
        env = dict(os.environ, CMPREC=rec, CGIF_B_TWIN=path)
        subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'luilui.py')],
                       env=env, check=True, stdout=subprocess.DEVNULL)
        rows = [l.rstrip('\n').split('\t') for l in list(open(os.path.join(rec, 'scans', 'luilui.tsv')))[1:]]
        row = [r for r in rows if int(r[1], 16) == fn][0]
        others = sorted(set(r[7] for r in rows if int(r[1], 16) != fn and r[7] not in ('none', 'EQUAL')))
        res[tag] = row[7]
        print('plant %s: luilui verdict on the planted function: %s (other functions not none / EQUAL: %s)' % (
            tag, row[7], others or 'none'))
        for s in row[5].split(' ;; '):
            if 'DIFFERS' in s:
                print('    %s' % s[-260:])
    ok = all(v == 'DIFFERS' for v in res.values())
    print('plant_luilui: %s' % ('both controls REFUSED (DIFFERS)' if ok else 'A CONTROL WAS NOT REFUSED: %s' % res))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
