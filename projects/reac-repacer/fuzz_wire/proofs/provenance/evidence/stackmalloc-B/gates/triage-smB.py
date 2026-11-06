#!/usr/bin/env python3
"""triage-smB.py FLAG.tsv OUT.tsv: one measured reason per port_addr_check row that is not a pass (every FLAG class row
and every UNMEASURED row) of the five files of this record; exit 1 on any row no rule explains.

Rules (each measured on the images or read from this record's own inputs; anything else is UNEXPLAINED):
  PATCH      UNPAIRED-PORTED, the value 0 on a line B-smB.patch writes (its `ly_NB ly =? 0` / `ly_SB ly =? 0` tests of
             lib/Reusable/YG0f.v owned_extents): not an image value.
  DROPPED    UNPAIRED-SOURCE on YF0r.v's fs_ranges: the donor rows of __asan_stack_malloc_2 / _4 (start and word count),
             which B-smB.patch removes; fuzz_wire's twin has no symbol of either name (read from its symtab).
  MODEL      GEOMETRY-CHANGED on an unchanged value equal to fs_frames 1 = Z.shiftl 1 (kStackSizeLog - 6 - 1) (FS_N of
             class 1, lib/Reusable/YG00.v): a count of the model, not a quantity of either image.
  IMG        UNRESOLVED with donor value kLowShadowBeg + IMG_TOP(grant) / 8 and ported value kLowShadowBeg +
             IMG_TOP(wire) / 8 (IMG_TOP = the page-rounded end of the last PT_LOAD): numerals-smB.tsv's IMG rule.
  env: P, R, LIB (the ported files' tree), KLIB (the unit lib for lib/Reusable/YG00.v; default LIB), PATCH (B-smB.patch)"""
import os, re, sys
from elftools.elf.elffile import ELFFile

FLAG, OUT = sys.argv[1:3]
P, R, LIB = os.environ['P'], os.environ['R'], os.environ['LIB']
PATCHED = {l[1:] for l in open(os.environ['PATCH']).read().split('\n') if l.startswith('+') and not l.startswith('+++')}
K_LOW_SHADOW_BEG = 0x7fff7000


def top(p):
    e = ELFFile(open(p, 'rb'))
    end = max(s['p_vaddr'] + s['p_memsz'] for s in e.iter_segments() if s['p_type'] == 'PT_LOAD')
    return (end + 0xfff) & ~0xfff


def names(p):
    return {s.name for s in ELFFile(open(p, 'rb')).get_section_by_name('.symtab').iter_symbols()}


GTOP, WTOP = top(P + '/bin/fuzz_grant/fuzz_grant.asan-ubsan'), top(R + '/result/bin/fuzz_wire/fuzz_wire.asan-ubsan')
WN = names(R + '/result/unstripped/fuzz_wire/fuzz_wire.asan-ubsan')
GN = names(P + '/unstripped/fuzz_grant/fuzz_grant.asan-ubsan')
ksl = int(re.search(r'Definition kStackSizeLog : Z := (\d+)\.', open(os.path.join(os.environ.get('KLIB', LIB), 'Reusable/YG00.v')).read()).group(1))
FS_FRAMES_1 = 1 << (ksl - 6 - 1)
PASS = {'INSN-SAME', 'NON-ADDRESS-SAME', 'SAME-GEOMETRY', 'SAME-SYMBOL', 'ROUND-CONSTANT-SAME', 'INTERCEPTOR-TRAMPOLINE'}

L = [l for l in open(FLAG).read().splitlines() if not l.startswith('#')]
h = L[0].split('\t')
out, bad = [], 0
for l in L[1:]:
    f = dict(zip(h, l.split('\t')))
    v = f.get('verdict', '')
    if v in PASS or not v:
        continue
    sv = int(f['src_value'], 16) if f.get('src_value') else None
    dv = int(f['dst_value'], 16) if f.get('dst_value') else None
    line = open(os.path.join(LIB, f['dst_file'])).read().split('\n')[int(f['dst_line']) - 1] if f.get('dst_line') else ''
    why = None
    if v == 'UNPAIRED-PORTED' and dv == 0 and line in PATCHED:
        why = 'PATCH: the 0 of `ly_NB ly =? 0` / `ly_SB ly =? 0`, a line B-smB.patch writes (lib/Reusable/YG0f.v owned_extents); no image value'
    elif v == 'UNPAIRED-SOURCE' and f['dst_file'] == 'B/Rt/YF0r.v' and f.get('sentence') == 'Definition fs_ranges':
        m = re.match(r'(__asan_stack_malloc_[24])\+0x0', f.get('src_res', ''))
        cls = {0x67: '__asan_stack_malloc_2', 0x73: '__asan_stack_malloc_4'}.get(sv) if not m else m.group(1)
        if cls and cls in GN and cls not in WN:
            why = 'DROPPED: the donor fs_ranges row of %s (%s), removed by B-smB.patch; fuzz_wire twin has no symbol %s, fuzz_grant twin has it' % (
                cls, 'its start' if m else 'its word count %d' % sv, cls)
    elif v == 'GEOMETRY-CHANGED' and sv == dv == FS_FRAMES_1:
        why = 'MODEL: fs_frames 1 = Z.shiftl 1 (kStackSizeLog - 6 - 1) = %d with kStackSizeLog = %d (lib/Reusable/YG00.v), FS_N of class 1; a count, not an image quantity' % (FS_FRAMES_1, ksl)
    elif v == 'UNRESOLVED' and sv == K_LOW_SHADOW_BEG + GTOP // 8 and dv == K_LOW_SHADOW_BEG + WTOP // 8:
        why = 'IMG: kLowShadowBeg + IMG_TOP / 8; grant IMG_TOP %#x -> %d (the donor value), wire IMG_TOP %#x -> %d (overrides-smB.tsv; numerals-smB.tsv IMG rows)' % (GTOP, sv, WTOP, dv)
    if why is None:
        bad += 1
        why = 'UNEXPLAINED'
    out.append('\t'.join([v, f['dst_file'], f.get('dst_line', ''), f.get('src_line', ''), f.get('src_value', ''), f.get('dst_value', ''), why]))
with open(OUT, 'w') as o:
    o.write('verdict\tfile\tdst_line\tsrc_line\tsrc_value\tdst_value\treason\n' + ''.join(r + '\n' for r in out))
print('triage-smB: %d rows not passing, %d explained, %d UNEXPLAINED' % (len(out), len(out) - bad, bad))
sys.exit(1 if bad else 0)
