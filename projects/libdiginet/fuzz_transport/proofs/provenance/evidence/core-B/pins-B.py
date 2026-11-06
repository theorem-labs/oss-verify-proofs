#!/usr/bin/env python3
"""pins-B.py: the pins and the donor inputs of libdiginet/fuzz_transport's image-B core run, each with its control.
Output: pins-B.out.
  P   libreac's pinned image tree (bin/<unit>, unstripped/<unit>: fuzz_decode, the donor, and fuzz_grant, the control)
  T   libdiginet's pinned image tree (result/bin/fuzz_transport, result/unstripped/fuzz_transport)
  HUB a clone of the proofs repository (the harness.yaml files; the control syms file of reac-repacer/fuzz_uci's image B)
1. Pins: fuzz_transport.asan-ubsan (libdiginet) equals the asan-ubsan pin of the unit's harness.yaml at TREV; the donor
   image libreac fuzz_decode.asan-ubsan equals the asan-ubsan pin of libreac/fuzz_decode's harness.yaml at the donor's
   release commit (DONREV), the tree its released lib/B was proved against.
2. Twin: each unstripped twin's PT_LOAD headers equal the pin's, and its PT_LOAD bytes equal the pin's except the ELF
   header's section-table fields (e_shoff, e_shnum, e_shstrndx) and the .note.gnu.build-id descriptor, which the strip
   rewrites. Control: fuzz_grant's pair (fuzz_uci's image-B donor) differs in the same places.
3. --old-prog: LLVMFuzzerTestOneInput .. end of the last program function before __wrap_getenv. Control: the rule gives
   fuzz_grant.asan-ubsan's 80a3c:86640 and fuzz_grant.asan's 806b0:857dc (the values the reac-repacer runs pass).
4. --old-syms: mksyms.py over the donor twin equals libreac-fuzz_decode.asan-ubsan.syms.txt beside this file; control:
   over fuzz_grant's asan-ubsan twin it reproduces reac-repacer/fuzz_uci's image-B fuzz_grant.asan-ubsan.syms.txt byte
   for byte.
5. The core file list (files-B-core.txt): call sites of the runtime entries whose walks the core list holds, in each
   image's .text (jal, and auipc + jalr pairs). Control: fuzz_grant.asan-ubsan, whose counts reac-repacer/fuzz_lock's
   pins-B.out records (__asan_memset 10, bcmp trampoline 6)."""
import bisect, hashlib, os, re, subprocess, sys
import capstone
from elftools.elf.elffile import ELFFile

P, T, HUB = os.environ['P'], os.environ['T'] + '/result', os.environ['HUB']
DONREV = os.environ.get('DONREV', '88154566652a')
UCISYMS = os.environ.get('UCISYMS', '09fe004d91a8:proofs/reac-repacer/fuzz_uci/provenance/evidence/core-B/fuzz_grant.asan-ubsan.syms.txt')
HERE = os.path.dirname(os.path.abspath(__file__))
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
git = lambda *a: subprocess.run(['git', '-C', HUB, *a], capture_output=True, text=True, check=True).stdout
TREV = os.environ.get('TREV', 'HEAD')
img = {'libdiginet fuzz_transport': (f'{T}/bin/fuzz_transport/fuzz_transport.asan-ubsan', f'{T}/unstripped/fuzz_transport/fuzz_transport.asan-ubsan'),
       'libreac fuzz_decode': (f'{P}/bin/fuzz_decode/fuzz_decode.asan-ubsan', f'{P}/unstripped/fuzz_decode/fuzz_decode.asan-ubsan'),
       'fuzz_grant': (f'{P}/bin/fuzz_grant/fuzz_grant.asan-ubsan', f'{P}/unstripped/fuzz_grant/fuzz_grant.asan-ubsan')}


def yaml_pin(rev, path, build):
    hy = git('show', f'{rev}:{path}')
    m = re.search(r'\n  %s:\n(?:    .*\n)*?    sha256: ([0-9a-f]{64})' % re.escape(build), hy)
    return m.group(1)


print('== 1. pins')
for unit, rev, path in (('libdiginet fuzz_transport', TREV, 'projects/libdiginet/fuzz_transport/harness.yaml'),
                        ('libreac fuzz_decode', DONREV, 'projects/libreac/fuzz_decode/harness.yaml')):
    want, got = yaml_pin(rev, path, 'asan-ubsan'), sha(img[unit][0])
    print(f'  {unit}.asan-ubsan sha256 {got[:12]}; harness.yaml asan-ubsan pin at {rev}: {want[:12]}: '
          f'{"EQUAL" if got == want else "DIFFERS"}')
for unit, rev, path, p in (('libdiginet fuzz_transport', TREV, 'projects/libdiginet/fuzz_transport/harness.yaml',
                            f'{T}/bin/fuzz_transport/fuzz_transport.asan'),
                           ('libreac fuzz_decode', DONREV, 'projects/libreac/fuzz_decode/harness.yaml',
                            f'{P}/bin/fuzz_decode/fuzz_decode.asan')):
    want, got = yaml_pin(rev, path, 'asan'), sha(p)
    print(f'  {unit}.asan (--known-elf / --kernel-image) sha256 {got[:12]}; harness.yaml asan pin at {rev}: {want[:12]}: '
          f'{"EQUAL" if got == want else "DIFFERS"}')

print('== 2. unstripped twin against the pin (PT_LOAD)')
for unit, (p, t) in img.items():
    ep, et = ELFFile(open(p, 'rb')), ELFFile(open(t, 'rb'))
    lp = [g for g in ep.iter_segments() if g['p_type'] == 'PT_LOAD']
    lt = [g for g in et.iter_segments() if g['p_type'] == 'PT_LOAD']
    hd = lambda g: tuple(g[k] for k in ('p_offset', 'p_vaddr', 'p_filesz', 'p_memsz', 'p_flags'))
    heads = [hd(a) for a in lp] == [hd(b) for b in lt]
    bid = ep.get_section_by_name('.note.gnu.build-id')
    allowed = set(range(40, 48)) | {60, 61, 62, 63} | set(range(bid['sh_offset'] + 16, bid['sh_offset'] + bid['sh_size']))
    diff = []
    for a, b in zip(lp, lt):
        da, db = a.data(), b.data()
        diff += [a['p_offset'] + i for i in range(len(da)) if da[i] != db[i]]
    rest = [x for x in diff if x not in allowed]
    print(f'  {unit}: pin {sha(p)[:12]} twin {sha(t)[:12]}: {len(lp)} PT_LOAD, headers equal {heads}; '
          f'{len(diff)} bytes differ, all in e_shoff / e_shnum / e_shstrndx / build-id: {not rest}')

print('== 3. --old-prog rule')


def prog(twin):
    s = [x for x in ELFFile(open(twin, 'rb')).get_section_by_name('.symtab').iter_symbols()
         if x['st_info']['type'] == 'STT_FUNC']
    a = {x.name: x['st_value'] for x in s}
    lo, wg = a['LLVMFuzzerTestOneInput'], a['__wrap_getenv']
    last = max((x['st_value'], x['st_size']) for x in s if lo <= x['st_value'] < wg)
    return f'{lo:x}:{last[0] + last[1]:x}'


print(f'  libreac fuzz_decode.asan-ubsan (the donor): {prog(img["libreac fuzz_decode"][1])}')
print(f'  CONTROL fuzz_grant.asan-ubsan (reac-repacer image-B runs pass 80a3c:86640): {prog(img["fuzz_grant"][1])}')
print(f'  CONTROL fuzz_grant.asan (the image-A runs pass 806b0:857dc): {prog(P + "/unstripped/fuzz_grant/fuzz_grant.asan")}')

print('== 4. --old-syms')
ms = lambda t, p: subprocess.run([sys.executable, f'{HERE}/mksyms.py', t, p], capture_output=True, text=True,
                                 check=True).stdout
b = ms(img['libreac fuzz_decode'][1], img['libreac fuzz_decode'][0])
print(f'  mksyms.py over the donor twin == libreac-fuzz_decode.asan-ubsan.syms.txt: '
      f'{b == open(HERE + "/libreac-fuzz_decode.asan-ubsan.syms.txt").read()} ({len(b.splitlines()) - 1} symbols)')
g = ms(img['fuzz_grant'][1], img['fuzz_grant'][0])
print(f'  CONTROL: over fuzz_grant\'s asan-ubsan twin == fuzz_uci image B\'s fuzz_grant.asan-ubsan.syms.txt, byte for byte: '
      f'{g == git("show", UCISYMS)} ({len(g.splitlines()) - 1} symbols)')

print('== 5. call sites of the walked runtime entries (.text)')
md = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
NAMES = ['__asan_memset', '__asan_memcpy', '__interceptor_trampoline_bcmp', '__interceptor_trampoline_memchr',
         '__interceptor_trampoline_strlen', '__interceptor_trampoline_strcmp', '__asan_set_shadow_f8',
         '__asan_stack_malloc_0', '__asan_stack_malloc_1', '__asan_stack_malloc_2', '__asan_stack_malloc_3',
         '__asan_stack_malloc_4', '__asan_stack_malloc_5', '__asan_stack_free_5']


def calls(pin, twin, names):
    tx = ELFFile(open(pin, 'rb')).get_section_by_name('.text')
    code, base = tx.data(), tx['sh_addr']
    fs = sorted((s['st_value'], s.name) for s in ELFFile(open(twin, 'rb')).get_section_by_name('.symtab').iter_symbols()
                if s['st_info']['type'] == 'STT_FUNC' and s['st_value'])
    starts, by = [x[0] for x in fs], {}
    for v, n in fs:
        by.setdefault(n, v)
    tg = {by[n]: n for n in names if n in by}
    out, auipc, off = {n: [] for n in names}, {}, 0
    while off < len(code):
        got = False
        for i in md.disasm(code[off:], base + off):
            got, off = True, i.address - base + i.size
            ops, t = [x.strip() for x in i.op_str.split(',')], None
            if i.mnemonic in ('jal', 'j', 'c.jal', 'c.j'):
                try:
                    t = i.address + int(ops[-1], 0)
                except ValueError:
                    pass
            elif i.mnemonic == 'auipc':
                v = int(ops[1], 0)
                auipc[ops[0]] = i.address + ((v - (1 << 20) if v >= 1 << 19 else v) << 12)
            elif i.mnemonic == 'jalr':
                mm = re.match(r'(?:(\w+), )?(-?\w+)\((\w+)\)', i.op_str)
                if mm and mm.group(3) in auipc:
                    t = auipc[mm.group(3)] + int(mm.group(2), 0)
            if t in tg:
                out[tg[t]].append((i.address, fs[bisect.bisect_right(starts, i.address) - 1][1]))
        if not got:
            off += 2
    return out, {n: by.get(n) for n in names}


for unit, (p, t) in img.items():
    o, at = calls(p, t, NAMES)
    for n, v in o.items():
        a = at[n]
        print(f'  {unit}: {n} {"absent" if a is None else hex(a)}: {len(v)} call sites in '
              f'{sorted(set(f for _, f in v))}')
