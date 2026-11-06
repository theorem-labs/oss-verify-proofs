import json
import os
import struct
import sys

sys.path.insert(0, os.environ.get('REVCHECK_DIR') or sys.exit('set REVCHECK_DIR to the directory holding revcheck.py (NOTES.md, Commands)'))
import revcheck as rc  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
W = HERE + '/'
ROOT = os.environ.get('PIPELINE_ROOT') or sys.exit('set PIPELINE_ROOT to the pipeline libreac root (it holds bin/ and unstripped/)')
PA = ROOT + '/unstripped/fuzz_boxreg/fuzz_boxreg.asan'
PB = ROOT + '/unstripped/fuzz_boxreg/fuzz_boxreg.asan-ubsan'
EA, EB = rc.Elf(PA), rc.Elf(PB)
S = json.load(open(W + 'syms.json'))

print('entry asan %#x  ubsan %#x' % (struct.unpack('<Q', EA.data[24:32])[0], struct.unpack('<Q', EB.data[24:32])[0]))
for k in ('asan', 'ubsan'):
    for n, t, v, z in S[k]['syms']:
        if n in ('__global_pointer$',):
            print(k, n, hex(v), t)
print('absent-in-asan names, checked in asan-ubsan:')
nb = {n for n, t, v, z in S['ubsan']['syms']}
na = {n for n, t, v, z in S['asan']['syms']}
for n in ('fopen', 'fclose', '__interceptor_fopen', '__interceptor_fclose', '__fdopen', '__fmodeflags',
          '__ofl_add', '__asan_stack_malloc_1', '__asan_stack_malloc_2', '__asan_stack_malloc_3'):
    print('   %-26s asan %s  ubsan %s' % (n, n in na, n in nb))

# the sealed string
s = EA.read(0x117e0, 0x60)
print('asan rodata @0x117fe:', EA.read(0x117fe, 32))
tgt = EA.read(0x117fe, 24)
dataB = EB.data
secB = EB.secs['.rodata'][0]
off = EB.bounds_of(secB[0]) if hasattr(EB, 'bounds_of') else None
print('ubsan .rodata', hex(secB[0]), hex(secB[1]))
raw = EB.read(secB[0], secB[1])
i = raw.find(tgt)
print('found at', hex(secB[0] + i) if i >= 0 else 'NOT FOUND', 'count', raw.count(tgt))
rawA = EA.read(EA.secs['.rodata'][0][0], EA.secs['.rodata'][0][1])
print('asan count of same bytes', rawA.count(tgt), 'identical rodata:', rawA == raw)

# GOT slots
GA, GB = (0x98e58, 0x99bb0), (0x99278, 0x99fd0)


def place(k, addr):
    c = sorted((z, v, n) for n, t, v, z in S[k]['syms'] if t in (1, 2) and n and v <= addr < v + max(z, 1))
    return (c[0][2], addr - c[0][1]) if c else None


def slots(E, lo, hi):
    out = {}
    for a in range(lo, hi, 8):
        out[a] = struct.unpack('<Q', E.read(a, 8))[0]
    return out


SA, SB = slots(EA, *GA), slots(EB, *GB)
for nm, a in [('GOT_common_flags', 0x98ea8), ('GOT_flags', 0x98eb0),
              ('GOT_asan_shadow_memory_dynamic_address', 0x98eb8), ('GOT_kMidMemBeg', 0x98ec0),
              ('GOT_kMidMemEnd', 0x98ec8), ('GOT_kHighMemEnd', 0x98ed0),
              ('GOT_replace_intrin_cached', 0x99a20), ('environ_musl', 0x99b48)]:
    w = SA[a]
    p = place('asan', w)
    tb = sorted({v for n, t, v, z in S['ubsan']['syms'] if n == p[0] and t in (1, 2)})
    want = tb[0] + p[1]
    hits = [x for x, v in SB.items() if v == want]
    print('%-40s asan slot %#x -> %s+%#x ; ubsan target %#x, slots %s (asan slots with same word: %s)'
          % (nm, a, p[0], p[1], want, [hex(x) for x in hits], [hex(x) for x, v in SA.items() if v == w]))
