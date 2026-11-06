#!/usr/bin/env python3
"""plant_ctz.py -- PLANTED CONTROL for the by-hand settlement of Allocate +0xdc (the 64-byte De Bruijn ctz table).
Makes two FILE copies of the cgif-B unstripped twin under plant/: `untouched` (byte-identical) and `planted` (ONE byte
changed inside the 64-byte table Allocate +0xdc reads: table + 17, XOR 0xff). For each copy it then reports
  (1) the settlement measurement (settle.py's DEBRUIJN rule: index from `srli 58`, one `lbu`, 64 bytes compared) on
      Allocate +0xdc against decode B's twin: must be EQUAL for `untouched`, DIFFERS for `planted`;
  (2) what the kit's one compare (strictcmp3) says for Allocate on that copy against decode B's twin.
usage: plant_ctz.py"""
import hashlib, os, shutil, struct, subprocess, sys, tempfile, importlib.util
from elftools.elf.elffile import ELFFile
TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)
import common
HERE = common.HERE
TWIN, DE = common.CGIF_B_TWIN, common.DECODE_B_TWIN
FN = '_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb'
TABLE, K = 0x10428, 17


def foff(path, va):
    for s in ELFFile(open(path, 'rb')).iter_segments():
        if s['p_type'] == 'PT_LOAD' and s['p_vaddr'] <= va < s['p_vaddr'] + s['p_filesz']:
            return s['p_offset'] + va - s['p_vaddr']
    raise SystemExit('not file-backed')


def main():
    pd = os.environ.get('PLANTDIR') or tempfile.mkdtemp(prefix='plant-ctz-'); os.makedirs(pd, exist_ok=True)   # never the record
    un, pl = os.path.join(pd, 'untouched.asan-ubsan'), os.path.join(pd, 'planted.asan-ubsan')
    shutil.copyfile(TWIN, un); shutil.copyfile(TWIN, pl)
    o = foff(pl, TABLE + K)
    b = bytearray(open(pl, 'rb').read()); old = b[o]; b[o] ^= 0xff; open(pl, 'wb').write(b)
    print('plant: %s byte at %#x (file offset %#x): %#04x -> %#04x' % (pl, TABLE + K, o, old, b[o]))
    for p in (TWIN, un, pl):
        print('  %s sha256 %s' % (p, hashlib.sha256(open(p, 'rb').read()).hexdigest()[:16]))
    sp = importlib.util.spec_from_file_location('settle', os.path.join(TOOLS, 'settle.py'))
    for tag, p in (('untouched', un), ('planted', pl)):
        os.environ['SETTLE_C'] = p
        st = importlib.util.module_from_spec(sp); sp.loader.exec_module(st)
        C, D = st.sc.Img(p), st.sc.Img(DE)
        v, why, tc, td = st.measure(C, D, FN, 0xdc)
        print('[%s] settlement Allocate +0xdc: %s (%s; targets %#x | %#x)' % (tag, 'EQUAL' if v == 'DEBRUIJN' else v, why, tc, td))
        r = subprocess.run(['python3', os.path.join(common.KIT, common.CMP_PY), 'cmp', FN, 'C=' + p, 'D=' + DE, 'C:D'],
                           capture_output=True, text=True)
        row = [l for l in r.stdout.split('\n') if l.startswith(FN + '\t')][0].split('\t')
        print('[%s] %s Allocate: verdict %s pcrel/real/unmeasured %s/%s/%s target-differ %s' % (tag, common.CMP_PY,
            row[6], row[7], row[8], row[9], row[11][:160]))


if __name__ == '__main__':
    main()
