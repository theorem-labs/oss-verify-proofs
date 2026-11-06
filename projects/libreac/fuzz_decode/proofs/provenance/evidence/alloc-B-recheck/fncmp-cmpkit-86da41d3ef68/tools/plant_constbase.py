#!/usr/bin/env python3
"""plant_constbase.py -- planted controls the constant-base scan (constbase.py, fail-opens (a)-(h)) must REFUSE, each a
FILE copy of the cgif-B unstripped twin with ONE instruction word changed (written to PLANTDIR, never into the record):
  (e) a lui-built displacement: LargeMmapAllocator<NoOpMapUnmapCallback, ..Static..>::Allocate (0x5e6bc) +0x24c
      `lui a3, 0x40` -> `lui a3, 0x41`: the site +0x258 `ld a3, 0x40(a2)` reads another field of the same object;
  (f) a li-built (no lui) constant: SizeClassAllocator64LocalCache::Refill (0x36134) +0x60 `addi a3, zero, 0x20` ->
      `addi a3, zero, 0x21` (shape (h)), the loop-entry value of what +0x98 `sd t3, 0(a1)` stores.
Each original instruction is checked before it is changed. constbase.py then runs on the planted function alone
(CONSTBASE_ONLY) with CGIF_B_TWIN = the planted copy, in a scratch record (its own scans/, the record's out/ read only);
the function must come out DIFFERS. usage: PLANTDIR=... plant_constbase.py"""
import hashlib, os, shutil, struct, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common
from elftools.elf.elffile import ELFFile

T = os.path.dirname(os.path.abspath(__file__))
PLANTS = [('e', 0x5e6bc, 0x24c, 'lui a3, 0x40', 0x000416b7),
          ('f', 0x36134, 0x60, 'addi a3, zero, 0x20', None)]


def encode_addi(rd, rs, imm):
    regs = {'zero': 0, 'ra': 1, 'sp': 2, 'gp': 3, 'tp': 4, 't0': 5, 't1': 6, 't2': 7, 's0': 8, 's1': 9}
    regs.update({'a%d' % i: 10 + i for i in range(8)})
    return ((imm & 0xfff) << 20) | (regs[rs] << 15) | (0 << 12) | (regs[rd] << 7) | 0x13


def main():
    pd = os.environ.get('PLANTDIR')
    if not pd:
        raise SystemExit('PLANTDIR is not set')
    os.makedirs(pd, exist_ok=True)
    src = common.CGIF_B_TWIN
    e = ELFFile(open(src, 'rb'))
    loads = [(s['p_vaddr'], s['p_offset'], s['p_filesz']) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
    foff = lambda va: [o + va - v for v, o, n in loads if v <= va < v + n][0]
    from capstone import Cs, CS_ARCH_RISCV, CS_MODE_RISCV64, CS_MODE_RISCVC
    md = Cs(CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC)
    orig = open(src, 'rb').read()
    print('original sha256 %s' % hashlib.sha256(orig).hexdigest()[:16])
    res = {}
    for tag, fn, off, want, new in PLANTS:
        data = bytearray(orig)
        fo = foff(fn + off)
        ins = next(md.disasm(bytes(data[fo:fo + 4]), fn + off))
        have = '%s %s' % (ins.mnemonic, ins.op_str)
        if have != want:
            raise SystemExit('plant %s: found %r, expected %r' % (tag, have, want))
        if new is None:
            ops = [x.strip() for x in ins.op_str.split(',')]
            new = encode_addi(ops[0], ops[1], int(ops[2], 0) + 1)
        data[fo:fo + 4] = struct.pack('<I', new)
        ins2 = next(md.disasm(bytes(data[fo:fo + 4]), fn + off))
        path = os.path.join(pd, 'planted-%s.elf' % tag)
        open(path, 'wb').write(data)
        print('plant %s: %#x +%#x  %s  ->  %s %s  (sha256 %s)' % (tag, fn, off, have, ins2.mnemonic, ins2.op_str,
                                                               hashlib.sha256(data).hexdigest()[:16]))
        rec = tempfile.mkdtemp(prefix='constbase-plant-%s-' % tag, dir=pd)
        os.makedirs(os.path.join(rec, 'scans'))
        os.symlink(common.OUT, os.path.join(rec, 'out'))
        shutil.copy(os.path.join(common.SCANS, 'exposure.tsv'), os.path.join(rec, 'scans'))
        env = dict(os.environ, CMPREC=rec, CGIF_B_TWIN=path, CONSTBASE_ONLY='%#x' % fn)
        subprocess.run([sys.executable, os.path.join(T, 'constbase.py')], env=env, check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        rows = [l.rstrip('\n').split('\t') for l in list(open(os.path.join(rec, 'scans', 'constbase.tsv')))[1:]]
        row = [r for r in rows if int(r[1], 16) == fn]
        res[tag] = row[0][7] if row else 'no site'
        print('plant %s: constbase verdict on the planted function: %s' % (tag, res[tag]))
        for s in (row[0][5].split(' ;; ') if row else []):
            if 'DIFFERS' in s:
                print('    %s' % s[-300:])
    ok = all(v == 'DIFFERS' for v in res.values())
    print('plant_constbase: %s' % ('both controls REFUSED (DIFFERS)' if ok else 'A CONTROL WAS NOT REFUSED: %s' % res))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
