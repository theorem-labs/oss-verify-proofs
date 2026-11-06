#!/usr/bin/env python3
"""measureB.py PIN TWIN -- step-1 image facts of an asan-ubsan pin, read from the pin and its unstripped twin
(pyelftools only; RISC-V instruction fields decoded by hand). Prints one fact per line, each with where it was read:
  pin / twin sha256; PT_LOAD equality pin vs twin (file bytes of every PT_LOAD; the only allowed differences are the
  ELF / program header bytes and the .note.gnu.build-id descriptor); sections; .text -> TFIB_TEXT_LO / TFIB_TEXT_N;
  PT_LOADs and the image hull; asan_globals descriptors (8 words each), lowest beg mod 64 -> hull floor;
  __asan_register_globals callers; main / _start; memset / memcpy (x_memset / x_memcpy); the canary .got cell
  (8-byte .got word = &__stack_chk_guard); the interceptor ipc values (return address of each GetCurrentPc call in
  ___interceptor_malloc / ___interceptor_free; the mcs > 2 path is the second); the frame-pointer setters
  (`addi s0, sp, k`) of the program functions (DWARF CUs outside the runtime) and whether they call malloc / free.
Computes nothing it does not print."""
import hashlib, struct, sys
from elftools.elf.elffile import ELFFile

pin, twin = sys.argv[1], sys.argv[2]


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def sx(v, b):
    return v - (1 << b) if v >> (b - 1) & 1 else v


ep, et = ELFFile(open(pin, 'rb')), ELFFile(open(twin, 'rb'))
bp, bt = open(pin, 'rb').read(), open(twin, 'rb').read()
print('pin  sha256 %s (%s)' % (sha(pin), pin.rsplit('/', 3)[-3:]))
print('twin sha256 %s' % sha(twin))

# PT_LOAD equality
lp = [s for s in ep.iter_segments() if s['p_type'] == 'PT_LOAD']
lt = [s for s in et.iter_segments() if s['p_type'] == 'PT_LOAD']
bid = et.get_section_by_name('.note.gnu.build-id')
bid_rng = (bid['sh_addr'] + 16, bid['sh_addr'] + bid['sh_size']) if bid else (0, 0)
hdr_hi = max(ep['e_phoff'] + ep['e_phnum'] * ep['e_phentsize'], ep['e_ehsize'])
print('PT_LOAD count pin %d twin %d' % (len(lp), len(lt)))
allok = len(lp) == len(lt)
for a, b in zip(lp, lt):
    same_hdr = all(a[k] == b[k] for k in ('p_vaddr', 'p_filesz', 'p_memsz', 'p_flags'))
    da = bp[a['p_offset']:a['p_offset'] + a['p_filesz']]
    db = bt[b['p_offset']:b['p_offset'] + b['p_filesz']]
    diffs = [i for i in range(min(len(da), len(db))) if da[i] != db[i]]
    bad = [i for i in diffs if not (a['p_offset'] + i < hdr_hi and a['p_offset'] == 0)
           and not (bid_rng[0] <= a['p_vaddr'] + i < bid_rng[1])]
    allok &= same_hdr and len(da) == len(db) and not bad
    print('  PT_LOAD vaddr %#x filesz %#x memsz %#x flags %#x: header fields %s; bytes differing %d (ELF/phdr header %d, '
          'build-id %d, OTHER %d)' % (a['p_vaddr'], a['p_filesz'], a['p_memsz'], a['p_flags'], 'EQUAL' if same_hdr else 'DIFFERENT',
                                      len(diffs), sum(1 for i in diffs if a['p_offset'] == 0 and i < hdr_hi),
                                      sum(1 for i in diffs if bid_rng[0] <= a['p_vaddr'] + i < bid_rng[1]), len(bad)))
print('PT_LOAD bytes pin == twin outside the ELF header fields and the build id: %s' % ('YES' if allok else 'NO'))
pl = [(s['p_vaddr'], s['p_vaddr'] + s['p_memsz']) for s in lp]
print('image hull [%#x, %#x) (page-up of the last PT_LOAD end)' % (pl[0][0] & ~0xfff, (max(h for _, h in pl) + 0xfff) & ~0xfff))
print('e_entry %#x' % ep['e_entry'])

secs = {s.name: s for s in et.iter_sections()}
print('sections (twin): ' + ' '.join('%s@%#x+%#x' % (s.name, s['sh_addr'], s['sh_size']) for s in et.iter_sections() if s['sh_addr']))
tx = secs['.text']
print('.text addr %#x size %#x -> TFIB_TEXT_LO %#x TFIB_TEXT_N = ceil(size/4) = %d' % (
    tx['sh_addr'], tx['sh_size'], tx['sh_addr'], -(-tx['sh_size'] // 4)))

syms = [(s['st_value'], s['st_size'], s['st_info']['type'], s.name) for s in secs['.symtab'].iter_symbols() if s.name]
by = {}
for v, z, t, n in syms:
    by.setdefault(n, []).append((v, z, t))


def fn(n):
    r = [x for x in by.get(n, []) if x[2] == 'STT_FUNC' and x[0]]
    return r[0] if r else None


def read(a, n):
    for s in lp:
        if s['p_vaddr'] <= a and a + n <= s['p_vaddr'] + s['p_filesz']:
            o = s['p_offset'] + a - s['p_vaddr']
            return bp[o:o + n]
    return None


def insns(lo, hi):
    pc, out = lo, []
    while pc < hi:
        h = int.from_bytes(read(pc, 2), 'little')
        if h & 3 == 3:
            out.append((pc, 4, int.from_bytes(read(pc, 4), 'little')))
            pc += 4
        else:
            out.append((pc, 2, h))
            pc += 2
    return out


def jal_target(raw, s, pc):
    if s == 4 and raw & 0x7f == 0x6f:
        imm = ((raw >> 31) << 20) | (((raw >> 12) & 0xff) << 12) | (((raw >> 20) & 1) << 11) | (((raw >> 21) & 0x3ff) << 1)
        return pc + sx(imm, 21), (raw >> 7) & 31
    if s == 2 and raw & 0xe003 == 0xa001:  # c.j
        i = raw >> 2
        imm = (((i >> 10) & 1) << 11) | (((i >> 9) & 1) << 4) | (((i >> 7) & 3) << 8) | (((i >> 6) & 1) << 10) | \
              (((i >> 5) & 1) << 6) | (((i >> 4) & 1) << 7) | (((i >> 1) & 7) << 1) | ((i & 1) << 5)
        return pc + sx(imm, 12), 0
    return None


def calls_in(lo, hi):
    """(pc, target, rd) of every jal / auipc+jalr call in [lo, hi)"""
    out, prev = [], None
    for pc, s, raw in insns(lo, hi):
        j = jal_target(raw, s, pc)
        if j:
            out.append((pc, j[0], j[1]))
        elif s == 4 and raw & 0x7f == 0x67 and prev and prev[1] == 4 and prev[2] & 0x7f == 0x17 \
                and (prev[2] >> 7) & 31 == (raw >> 15) & 31:
            out.append((pc, prev[0] + sx(prev[2] & 0xfffff000, 32) + sx(raw >> 20, 12), (raw >> 7) & 31))
        prev = (pc, s, raw)
    return out


# asan_globals
ag = secs.get('asan_globals')
if ag is None:
    print('asan_globals: NO such section in the twin -> 0 descriptors')
else:
    d = ag.data()
    print('asan_globals %#x size %#x: %d descriptors' % (ag['sh_addr'], ag['sh_size'], len(d) // 64))
    begs = []
    for i in range(0, len(d), 64):
        w = struct.unpack_from('<8Q', d, i)
        begs.append(w[0])
        print('  @%#x words (+0 beg, +8 size, +16 size_with_redzone, +24 name, +32 module_name, +40 has_dynamic_init, '
              '+48 source_location, +56 odr_indicator) = %s' % (ag['sh_addr'] + i, ', '.join('%#x' % x for x in w)))
    if begs:
        lo = min(begs)
        print('  lowest beg %#x mod 64 = %d -> hull floor %#x' % (lo, lo % 64, lo & ~63))
print('__odr_asan* symbols: %d; ___asan_gen_* symbols: %d' % (
    sum(1 for n in by if n.startswith('__odr_asan')), sum(1 for n in by if n.startswith('___asan_gen_'))))
rg = fn('__asan_register_globals')
if rg:
    cs = []
    for v, z, t, n in syms:
        if t == 'STT_FUNC' and v and z:
            cs += ['%s+%#x' % (n, pc - v) for pc, tg, rd in calls_in(v, v + z) if tg == rg[0]]
    print('__asan_register_globals %#x: direct callers %s' % (rg[0], sorted(set(cs)) or 'NONE'))
for n in ('asan.module_ctor', 'asan.module_dtor'):
    print('%s: %s' % (n, ['%#x+%d' % (x[0], x[1]) for x in by.get(n, [])] or 'absent'))

for n in ('main', '_start', '_start_c', 'LLVMFuzzerTestOneInput', 'memset', 'memcpy', 'memmove', 'bcmp', 'memcmp',
          'strlen', 'memchr', 'strchr', '__stack_chk_guard', '__asan_memset', '__asan_memcpy', '__asan_memmove',
          '_ZN6__asan9asan_initE', '__asan_init'):
    print('symbol %-24s %s' % (n, ['%#x size %d %s' % x for x in by.get(n, [])] or 'absent'))

g = by['__stack_chk_guard'][0][0]
got = secs['.got']
gd = got.data()
print('canary .got cell(s) (8-byte .got word = &__stack_chk_guard %#x): %s' % (
    g, [hex(got['sh_addr'] + i) for i in range(0, len(gd), 8) if int.from_bytes(gd[i:i + 8], 'little') == g]))

gcp = fn('_ZN11__sanitizer10StackTrace12GetCurrentPcEv')
for n in ('___interceptor_malloc', '___interceptor_free'):
    v, z, _ = fn(n)
    r = [pc + 4 for pc, tg, rd in calls_in(v, v + z) if tg == gcp[0] and rd == 1]
    print('ipc %s %#x: GetCurrentPc %#x return addresses %s (gen_traces --ipc takes the second)' % (
        n, v, gcp[0], [hex(x) for x in r]))

# program functions: DWARF CUs outside the runtime
dw = et.get_dwarf_info()
prog = []
for cu in dw.iter_CUs():
    top = cu.get_top_DIE()
    name = top.attributes.get('DW_AT_name')
    name = name.value.decode() if name else '?'
    comp = top.attributes.get('DW_AT_comp_dir')
    comp = comp.value.decode() if comp else ''
    if 'llvm-project' in name or 'llvm-project' in comp or '/musl' in name or '/musl' in comp or 'musl' in comp.split('/'):
        continue
    for die in cu.iter_DIEs():
        if die.tag == 'DW_TAG_subprogram' and 'DW_AT_low_pc' in die.attributes and 'DW_AT_high_pc' in die.attributes:
            lo = die.attributes['DW_AT_low_pc'].value
            hv = die.attributes['DW_AT_high_pc']
            hi = hv.value if hv.form == 'DW_FORM_addr' else lo + hv.value
            nm = die.attributes.get('DW_AT_name')
            if tx['sh_addr'] <= lo < hi <= tx['sh_addr'] + tx['sh_size']:   # discarded subprograms keep low_pc 0
                prog.append((lo, hi, nm.value.decode() if nm else '?', name))
prog.sort()
print('program functions (DWARF, non-runtime CUs %s): %d' % (sorted({p[3] for p in prog}), len(prog)))
alloc = {x[0] for n in ('__interceptor_trampoline_malloc', '__interceptor_trampoline_free', '___interceptor_malloc',
                        '___interceptor_free', 'malloc', 'free', '__wrap_malloc', '__wrap_free') for x in by.get(n, []) if x[0]}
for lo, hi, nm, cu in prog:
    fps = [(pc, sx(raw >> 20, 12)) for pc, s, raw in insns(lo, hi)
           if s == 4 and raw & 0x707f == 0x13 and (raw >> 7) & 31 == 8 and (raw >> 15) & 31 == 2]
    if fps:
        ca = [pc for pc, tg, rd in calls_in(lo, hi) if tg in alloc]
        print('FP-SETTER %s [%#x,%#x) %s; calls malloc/free: %s' % (
            nm, lo, hi, ', '.join('addi s0, sp, %d at %#x' % (k, pc) for pc, k in fps), [hex(x) for x in ca] or 'none'))
