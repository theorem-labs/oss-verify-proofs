"""Write lib/B/AB1w.v: the A-core table, every value moved to fuzz_boxreg.asan-ubsan."""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
W = HERE + '/'
SRC = os.path.join(HERE, '../../../../lib/A/AB1w.v')
OUT = os.path.join(HERE, '../AB1w.v')
R = {r['row']: r for r in json.load(open(W + 'resolved.json'))['res']}

HEAD = [
    '(* Copyright 2026 Anthropic PBC *)',
    '(* SPDX-License-Identifier: Apache-2.0 *)',
    '(* Modified by Theorem Labs, 2026-10: ported to rc.2\'s binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)',
    '(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its addresses moved to libreac/fuzz_boxreg\'s ASan build. *)',
    '(* Modified by Theorem Labs, 2026-10: the function-range table (the tfib_A_ and tfib_E_ rows) regenerated from fuzz_boxreg.asan\'s symtab (st_value, st_value+st_size); merged cgif rows split, rows without a boxreg counterpart dropped; see NOTES.md. *)',
    '(* Modified by Theorem Labs, 2026-10: this is lib/B\'s copy, for the ASan+UBSan build fuzz_boxreg.asan-ubsan (sha256 7620eb05..., symbols 1d548458...). Every row keeps lib/A\'s name and is paired to that build BY SYMBOL and, where a name occurs more than once, BY CODE (instruction compare of the two builds); its two values are the asan-ubsan symbol\'s st_value and st_value + st_size. The section, image, entry and gp constants, the tfib_D_* cells and the tfib_at_* anchors are fuzz_boxreg.asan-ubsan\'s; see NOTES.md. *)',
    'From Stdlib Require Import ZArith.',
    'From OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YImgTop.',
    'Unset Lia Cache. Unset Nia Cache.',
    'Open Scope Z_scope.',
]

CONST = [
    ('rodata', 0x102e0, 0x2268c), ('text', 0x2ffb8, 0x97d40),
    ('init_array', 0x98d40, 0x98d60), ('fini_array', 0x98d60, 0x98d70),
    ('preinit_array', 0x98d70, 0x98d78), ('data_rel_ro', 0x98d78, 0x99278),
    ('got', 0x99278, 0x99fd0), ('data', 0x9afd0, 0x9db90),
    ('asan_globals', 0x9db90, 0x9dcd0), ('bss', 0x9dd00, 0x5f5c30),
    ('tbss', 0x97d40, 0x97d54),
]

TAIL = {
    'tfib_D_str_sealed': '0x117fe',
    'tfib_D_init_array_0_3': '0x98d40',
    'tfib_D_fini_array_0_1': '0x98d60',
    'tfib_D_GOT_common_flags': '0x992c8',
    'tfib_D_GOT_flags': '0x992d0',
    'tfib_D_GOT_asan_shadow_memory_dynamic_address': '0x992d8',
    'tfib_D_GOT_kMidMemBeg': '0x992e0',
    'tfib_D_GOT_kMidMemEnd': '0x992e8',
    'tfib_D_GOT_kHighMemEnd': '0x992f0',
    'tfib_D_GOT_replace_intrin_cached': '0x99e40',
    'tfib_D_environ_musl': '0x99f68',
    'tfib_D_REAL_read': '0x9b018',
    'tfib_D_REAL_memcpy': '0x9b140',
    'tfib_D_REAL_memset': '0x9b148',
    'tfib_D_asan_allocator_instance_asan_allocator_cpp_insta': '0x9dd58',
    'tfib_D_asan_flags_Flags_struct_flags': '0x9ebb8',
    'tfib_D_asan_shadow_memory_dynamic_address': '0xa13b8',
    'tfib_D_asan_inited': '0xa2098',
    'tfib_D_replace_intrin_cached': '0xa2099',
    'tfib_D_kHighMemEnd': '0xa20a0',
    'tfib_D_kMidMemBeg': '0xa20a8',
    'tfib_D_kMidMemEnd': '0xa20b0',
    'tfib_D_malloc_context_size': '0xa20bc',
    'tfib_D_common_flags_dont_use_CommonFlags_struct_common': '0x132ee8',
    'tfib_D_libc_progname_area_musl_bss': '0x5f45e0',
    'tfib_at_img_lo': '0x10000',
    'tfib_at_img_hi': 'YImgTop.IMG_TOP',
    'tfib_at_n_res': '4%nat',
    'tfib_at_shadow_off': '0x7fff8000',
    'tfib_at_a_entry': '0x2ffb8',
    'tfib_at_rw_lo': '0x9a000',
    'tfib_at_rw_len': '0x55c000',
    'tfib_at_ph_addr_z': '0x10040',
    'tfib_at_ph_ent_z': '56',
    'tfib_at_ph_num_z': '11',
    'tfib_at_x_imemset': '0x63484',
    'tfib_at_x_imemcpy': '0x63408',
    'tfib_at_x_memset': '0x929ac',
    'tfib_at_x_memcpy': '0x925a8',
    'tfib_at_x_memiszero': '0x639b4',
    'tfib_at_x_istrncpy': '0x638b0',
    'tfib_at_x_sealed': '0x117fe',
    'tfib_at_x_popfree': '0x363a4',
    'tfib_at_x_sniff': '0',
    'tfib_at_sniff_tab': '0',
    'tfib_at_sniff_cell': '0',
    'tfib_at_x_envscan': '0x883ac',
    'tfib_at_x_envscan_k': '0x883b8',
    'tfib_at_x_pnscan': '0x88470',
    'tfib_at_x_pnscan_k': '0x8847c',
    'tfib_at_stops_more': '(0x34018 :: 0x3563c :: 0x53790 :: 0x59b48 :: 0x59b5c :: 0x59b70 :: 0x5f500 :: 0x5f5d0 :: 0x6cafc :: 0x6da08 :: 0x6db98 :: 0x778f0 :: nil)%list',
}

out = list(HEAD)
seen_rows, seen_tail = set(), set()
for ln, line in enumerate(open(SRC), 1):
    s = line.rstrip('\n')
    if ln <= 9:                                        # header, replaced above
        continue
    m = re.match(r'Definition tfib_A_(\w+) : Z := 0x[0-9a-f]+\.\s+Definition tfib_E_\1 : Z := 0x[0-9a-f]+\.$', s.strip())
    if m:
        r = R[m.group(1)]
        out.append('Definition tfib_A_%s : Z := %#x.  Definition tfib_E_%s : Z := %#x.' % (r['row'], r['b'], r['row'], r['be']))
        seen_rows.add(r['row'])
        continue
    m = re.match(r'Definition (tfib_(?:D|at)_\w+) : (Z|nat|list Z) := .*\.$', s.strip())
    if m:
        out.append('Definition %s : %s := %s.' % (m.group(1), m.group(2), TAIL[m.group(1)]))
        seen_tail.add(m.group(1))
        continue
    if s.startswith('Definition tfib_') and '_lo : Z' in s:       # section / img / entry constants
        continue
    if s.startswith('Definition tfib_img_lo') or s.startswith('Definition tfib_entry'):
        continue
    assert s.startswith('(*'), (ln, s)
    out.append(s.replace('fuzz_boxreg.asan is', 'fuzz_boxreg.asan-ubsan is')
                .replace('fuzz_boxreg.asan has', 'fuzz_boxreg.asan-ubsan has')
                .replace('into fuzz_boxreg.asan;', 'into fuzz_boxreg.asan-ubsan;')
                .replace('__asan_stack_malloc_3 0x3c520+0x1ac', '__asan_stack_malloc_3 0x3c580+0x1ac'))

# the constant block goes back in at its place (after Open Scope)
cb = ['Definition tfib_%s_lo : Z := %#x.  Definition tfib_%s_hi : Z := %#x.' % (n, lo, n, hi) for n, lo, hi in CONST]
cb.append('Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := YImgTop.IMG_TOP.')
cb.append('Definition tfib_entry : Z := 0x2ffb8.  Definition tfib_gp : Z := 0x10800.')
out = out[:len(HEAD)] + cb + out[len(HEAD):]
open(OUT, 'w').write('\n'.join(out) + '\n')
print('wrote', OUT, len(out), 'lines; rows', len(seen_rows), 'tail', len(seen_tail), 'of', len(TAIL))
assert seen_tail == set(TAIL), set(TAIL) - seen_tail
