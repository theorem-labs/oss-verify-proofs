# lib/B/AB1w.v for libreac/fuzz_boxreg.asan-ubsan (TFIB function-range table)

Output: `AB1w.v` in this directory (630 lines; the same file as `proofs/libreac/fuzz_boxreg/lib/B/AB1w.v`, git blob `426222576f90821d236a6f486e44aa22f0a0a2f3`), the B core's copy of the A core's table. It is
`proofs/libreac/fuzz_boxreg/lib/A/AB1w.v` (git blob `68d907a2306868af462cff22e74fb9e3b9c467c2`; 629 lines, the regenerated A table of `../ab1w/NOTES.md`) with every value moved to the
ASan+UBSan build; one provenance comment is added (line 6), nothing else changes shape: same 524 rows, same row
names, same order, same comments, same 51 tail definitions.

## Sources

- Row names and order: `proofs/libreac/fuzz_boxreg/lib/A/AB1w.v` (git blob `68d907a2306868af462cff22e74fb9e3b9c467c2`; the A core's file, already carrying the renames of
  `../ab1w/NOTES.md`; it differs from `../ab1w/AB1w.v` only in the `YImgTop` Require and the two image-top
  values).
- Pinned images, under `$PIPELINE_ROOT` (the pipeline's `libreac` directory; see Commands): asan
  `$PIPELINE_ROOT/bin/fuzz_boxreg/fuzz_boxreg.asan` (sha256 `eacfa20547ad7dc0d24164010513fcc8af4ba5e557ff3f391a07559e3e34a6df`),
  symbols `$PIPELINE_ROOT/unstripped/fuzz_boxreg/fuzz_boxreg.asan` (sha256 `4532568b621d62be2c79a1e2cf52cd1393008542eeb32e465d50b90d68e8f7a3`);
  asan-ubsan `$PIPELINE_ROOT/bin/fuzz_boxreg/fuzz_boxreg.asan-ubsan` (sha256 `7620eb05e0adf5cb5ea350a6fe814d02d6ddb2685ec03477d0d4a85d249b0d85`),
  symbols `$PIPELINE_ROOT/unstripped/fuzz_boxreg/fuzz_boxreg.asan-ubsan` (sha256 `1d548458eac37ae17f9e8dfb06a5dfef3c606ec9e03eca8ef291d5fec9dce495`).
- Every emitted function value: the asan-ubsan symtab read with revcheck's `Elf` (`rc.Elf(p).syms`, tuples
  `(name, type, st_value, st_size)`; only `type == 2`, FUNC). `tfib_A_x = st_value`, `tfib_E_x = st_value + st_size`.
- Code comparison: capstone through elfdis (`217c0af79e0d8be29b6aa5f568b03cfe250712ab:audit-tools/elfdis.py`, sha256 `ed45f6bea2e54eff8a6fa9bed0bd4fec353f7c6887c0ce3472a53725f41ccab2`; `elfdis.load`, `elfdis.disasm`), mnemonic + register
  sequence over the whole function, immediates allowed to differ (the A lane's `port_verdict` rule).
  The elfdis named here is `217c0af79e0d:audit-tools/elfdis.py` (sha256 ed45f6bea2e5); its `--diff` mode is fail-open on the comparison-tool registry's false-equal plant set (23 plants, manifest sha256 31c4dfb2053aacc591d627bcc3a94a97415cb0b58778172df0bef374ce10b2b2: EQUAL on 23 of 23). The old verdict table below (resolve.py's SAME / IMM / SHAPE) used `elfdis.disasm`'s full output, mnemonics and operands; it is superseded by `RERUN-cmpkit-4bbd3a74be89.md` (independent decode and kit), and no standing verdict rests on elfdis in either mode. The Commands section uses elfdis only in decode mode to regenerate `AB1w.v`, whose values are checked independently in `../ab1w/RERUN-cmpkit-4bbd3a74be89.md`, section "The ab1wB generator scripts and the values of lib/A/AB1w.v and lib/B/AB1w.v"; the kit's verdicts on the 524 rows are audited against cmpkit 86da41d3ef68's fail-open shapes in the same file, section "Address-shape audit against cmpkit 86da41d3ef68's fail-open list (a)-(h)" (0 DIFFERENT; per-row results in `SHAPE-AUDIT-rows.tsv` here).

## Method: how each row was paired

1. The A row's `(A, E)` is resolved in **fuzz_boxreg.asan**: the FUNC symbols at `st_value == A` with
   `st_value + st_size == E`. Every one of the 524 rows resolves (the two size-0 asm rows below are the exception
   to the size test only).
2. Those symbol **names** are looked up in the asan-ubsan symtab. Rows are never paired by the row's label.
3. Where the name set lands on one address, that is the row (516 rows: `unique-symbol`; alias names such as
   `__interceptor_trampoline_strlen` / `__wrap_strlen`, or `___interceptor_strlen` / `__interceptor_strlen`, sit on
   the same address and do not make the row ambiguous).
4. Where a name occurs more than once in asan-ubsan, the row is decided by code; see "Pairings decided by code".
5. Each pairing is then verdicted by instruction compare of the asan function against the chosen asan-ubsan
   function.

## Counts

| | rows |
|---|---|
| rows in the A file | 524 |
| rows in `AB1w.v` (this directory) | 524 |
| paired `unique-symbol` | 520 |
| paired by code (duplicate symbol `__asan::MemToShadow`) | 4 |
| **A rows with no asan-ubsan twin** | **0** |

Instruction compare of the 524 pairs (whole function, asan vs asan-ubsan):

| verdict | rows |
|---|---|
| `SAME` (identical mnemonics and operands) | 186 |
| `IMM` (same mnemonic + register sequence, immediates differ) | 335 |
| `SHAPE` (equal past pc-relative fields; the three rows below) | 3 |

The three `SHAPE` rows are not code differences. Each word counted unequal is `addi rd,rs,lo12` (the low part of a
pc-relative address) in one image and the same `addi` with lo12 = 0 in the other, which the disassembler prints as its
alias `mv rd,rs`. The registers are equal. The comparison kit finds `ioctl_table_fill` and
`AsanThread_AsyncSignalSafeLazyInitFakeStack` equal past pc-relative fields, and `asan_InitializeFlags` equal except one
target (an empty string) that `RERUN-cmpkit-4bbd3a74be89.md` settles by measurement. The `equal` column is the
disassembler's count. All three have the same
instruction count on both sides:

| row | asan | asan-ubsan | insns | equal |
|---|---|---|---|---|
| `asan_InitializeFlags` | 0x3c808..0x3d834 | 0x3c868..0x3d894 | 1035/1035 | 1034 |
| `ioctl_table_fill` | 0x4825c..0x50f34 | 0x482bc..0x50f94 | 9014/9014 | 9005 |
| `AsanThread_AsyncSignalSafeLazyInitFakeStack` | 0x5bb1c..0x5bd4c | 0x5bb7c..0x5bdac | 140/140 | 139 |

Every one of the 524 B rows has **exactly the same byte length as its A row** (checked pairwise), so the port adds
and drops no code inside any row.

## No-twin list

**Empty.** Every row of the A file has a counterpart in fuzz_boxreg.asan-ubsan. The ten cgif rows the A lane
dropped (fopen / fclose and their interceptors, musl `__fdopen`, `fclose`, `fopen`, `__fmodeflags`, `__ofl_add`,
`__asan_stack_malloc` classes 1 and 2) are absent from asan-ubsan as well, which is why their comments carry over
unchanged (only the image name in them is updated):

```
fopen False  fclose False  __interceptor_fopen False  __interceptor_fclose False
__fdopen False  __fmodeflags False  __ofl_add False  __asan_stack_malloc_1 False  __asan_stack_malloc_2 False
__asan_stack_malloc_3 True (0x3c580+0x1ac, 107 insns)
```
(`in` the asan-ubsan symtab; the same query on the asan symtab gives the same answers.)

## Pairings decided by code

`_ZN6__asanL11MemToShadowEm` has five instances in each image, with identical bodies (79 insns, `IMM` against
every one of the five), so a code compare alone cannot choose. They are paired by ordinal and the choice is
confirmed by the neighbouring symbols, which are the same function on both sides:

| row | asan | asan-ubsan | ordinal | previous FUNC (both images) | next FUNC (both images) |
|---|---|---|---|---|---|
| `MemToShadow_3c6cc` | 0x3c6cc | 0x3c72c | 2/5 | `__asan_stack_malloc_3` | `__asan::InitializeFlags` |
| `MemToShadow_CHECK_AddrIsInMem_instance` | 0x52140 | 0x521a0 | 3/5 | `__asan::FlushUnneededASanShadowMemory` | `__asan::AsanCheckDynamicRTPrereqs` |
| `MemToShadow_checked` | 0x53788 | 0x537e8 | 4/5 | `__asan::PoisonShadow` | `__asan_poison_memory_region` |
| `MemToShadow_checked_instance_3` | 0x5c674 | 0x5c6d4 | 5/5 | `__asan::AsanThread::GetStackFrameAccessByAddr` | `__asan::FindThreadByStackAddress` |

(The first instance, asan 0x3ae64 / asan-ubsan 0x3aec4, carries no row in either file.)

Four rows whose asan address also carries the generic local name `dummy` (which sits on five different addresses in
asan-ubsan) are decided by the other, unique name at the same address, and each pairing is `SAME` code with the
same neighbours: `init` -> `_init` 0x88370, `fini` -> `_fini` 0x88d40, `testcancel` -> `__testcancel` 0x94c2c,
`aio_close_stub_j_ret_used_by_close_stdio_close` -> `__aio_close` 0x8e150.

## The two size-0 asm rows

`E` is not `st_value + st_size` for these two; each keeps the A lane's own rule, and the resulting length equals
the A row's:

| row | asan-ubsan | rule | insns |
|---|---|---|---|
| `start` | 0x2ffb8..0x30000 | `_start` (size 0) through the end of the next FUNC `_start_c` 0x2ffd4+0x2c | 18, `IMM` against asan's 18 |
| `set_thread_area` | 0x94c30..0x94c3c | `__set_thread_area` (size 0) to the next FUNC start `__unmapself` 0x94c3c | 3, `SAME` as asan's 3 |

## Header constants (from the asan-ubsan ELF)

Section table of fuzz_boxreg.asan-ubsan, read with `rc.Elf(...).secs`:

| row | asan | asan-ubsan |
|---|---|---|
| `tfib_rodata_lo/hi` | 0x102e0 / 0x2268c | 0x102e0 / 0x2268c |
| `tfib_text_lo/hi` | 0x2ff58 / 0x97920 | 0x2ffb8 / 0x97d40 |
| `tfib_init_array_lo/hi` | 0x98920 / 0x98940 | 0x98d40 / 0x98d60 |
| `tfib_fini_array_lo/hi` | 0x98940 / 0x98950 | 0x98d60 / 0x98d70 |
| `tfib_preinit_array_lo/hi` | 0x98950 / 0x98958 | 0x98d70 / 0x98d78 |
| `tfib_data_rel_ro_lo/hi` | 0x98958 / 0x98e58 | 0x98d78 / 0x99278 |
| `tfib_got_lo/hi` | 0x98e58 / 0x99bb0 | 0x99278 / 0x99fd0 |
| `tfib_data_lo/hi` | 0x9abb0 / 0x9d770 | 0x9afd0 / 0x9db90 |
| `tfib_asan_globals_lo/hi` | 0x9d770 / 0x9d8b0 | 0x9db90 / 0x9dcd0 |
| `tfib_bss_lo/hi` | 0x9d8c0 / 0x5f57f0 | 0x9dd00 / 0x5f5c30 |
| `tfib_tbss_lo/hi` | 0x97920 / 0x97934 | 0x97d40 / 0x97d54 |
| `tfib_entry` | 0x2ff58 | 0x2ffb8 (`e_entry`, = `_start`) |
| `tfib_gp` | 0x10800 | 0x10800 (`__global_pointer$`, same value in both) |

`tfib_text_hi = 0x97d40` keeps cgif's convention (`.tbss`'s start). In asan-ubsan `.text` ends at that same address
(asan has a 4-byte gap: `.text` ends 0x9791c, `.tbss` starts 0x97920).

`tfib_img_lo = 0x10000`; `tfib_img_hi = YImgTop.IMG_TOP` and `tfib_at_img_hi = YImgTop.IMG_TOP`, the named constant
(`lib/Reusable/YImgTop.v`, which states both pinned images: last loaded segment 0x5f57f0 asan / 0x5f5c30
asan-ubsan, both rounding to the page 0x5f6000). No image-end literal occurs in the file (checked: 0 lines match
`0x5f6000|6250496|781312`).

## Module paths

The file sits at `lib/B/AB1w.v`, so its own module is
`OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.B.AB1w`. Its only Require is
`From OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YImgTop.`, unchanged (Reusable is shared by
both cores, and `YImgTop` states both images). The table Requires no A-core file, so no Require had to become
`lib.B`.

## Tail: tfib_D_* cells and tfib_at_* anchors

Each A value was placed in the asan image (the OBJECT/FUNC symbol that covers it, plus the offset; for a `.got`
word, the symbol its content points at) and the same place was read in asan-ubsan. All 25 `tfib_D_*` and 26
`tfib_at_*` definitions keep their names.

| row | asan | asan-ubsan | how |
|---|---|---|---|
| `tfib_D_str_sealed`, `tfib_at_x_sealed` | 0x117fe | 0x117fe | the bytes `"<sealed>\0"`; the 24 bytes at the asan address occur exactly once in each image's `.rodata`, at the same address |
| `tfib_D_init_array_0_3` | 0x98920 | 0x98d40 | `.init_array` start |
| `tfib_D_fini_array_0_1` | 0x98940 | 0x98d60 | `.fini_array` start |
| `tfib_D_GOT_common_flags` | 0x98ea8 | 0x992c8 | GOT slot holding `__sanitizer::common_flags_dont_use` (0x132aa8 -> 0x132ee8); one slot on each side |
| `tfib_D_GOT_flags` | 0x98eb0 | 0x992d0 | GOT slot -> `__asan::asan_flags_dont_use_directly` |
| `tfib_D_GOT_asan_shadow_memory_dynamic_address` | 0x98eb8 | 0x992d8 | GOT slot -> `__asan_shadow_memory_dynamic_address` |
| `tfib_D_GOT_kMidMemBeg` | 0x98ec0 | 0x992e0 | GOT slot -> `__asan::kMidMemBeg` |
| `tfib_D_GOT_kMidMemEnd` | 0x98ec8 | 0x992e8 | GOT slot -> `__asan::kMidMemEnd` |
| `tfib_D_GOT_kHighMemEnd` | 0x98ed0 | 0x992f0 | GOT slot -> `__asan::kHighMemEnd` |
| `tfib_D_GOT_replace_intrin_cached` | 0x99a20 | 0x99e40 | GOT slot -> `__asan::replace_intrin_cached` |
| `tfib_D_environ_musl` | 0x99b48 | 0x99f68 | GOT slot -> `___environ` (0x5d3e40 -> 0x5d4280) |
| `tfib_D_REAL_read` | 0x9abf8 | 0x9b018 | `__interception::real_read` |
| `tfib_D_REAL_memcpy` | 0x9ad20 | 0x9b140 | `__interception::real_memcpy` |
| `tfib_D_REAL_memset` | 0x9ad28 | 0x9b148 | `__interception::real_memset` |
| `tfib_D_asan_allocator_instance_...` | 0x9d918 | 0x9dd58 | `__asan::instance` |
| `tfib_D_asan_flags_Flags_struct_flags` | 0x9e778 | 0x9ebb8 | `__asan::asan_flags_dont_use_directly` |
| `tfib_D_asan_shadow_memory_dynamic_address` | 0xa0f78 | 0xa13b8 | `__asan_shadow_memory_dynamic_address` |
| `tfib_D_asan_inited` | 0xa1c58 | 0xa2098 | `__asan::asan_inited` |
| `tfib_D_replace_intrin_cached` | 0xa1c59 | 0xa2099 | `__asan::replace_intrin_cached` |
| `tfib_D_kHighMemEnd` | 0xa1c60 | 0xa20a0 | `__asan::kHighMemEnd` |
| `tfib_D_kMidMemBeg` | 0xa1c68 | 0xa20a8 | `__asan::kMidMemBeg` |
| `tfib_D_kMidMemEnd` | 0xa1c70 | 0xa20b0 | `__asan::kMidMemEnd` |
| `tfib_D_malloc_context_size` | 0xa1c7c | 0xa20bc | `__asan::malloc_context_size` |
| `tfib_D_common_flags_dont_use_...` | 0x132aa8 | 0x132ee8 | `__sanitizer::common_flags_dont_use` |
| `tfib_D_libc_progname_area_musl_bss` | 0x5f41a0 | 0x5f45e0 | `__libc` |
| `tfib_at_a_entry` | 0x2ff58 | 0x2ffb8 | `e_entry` |
| `tfib_at_rw_lo` | 0x9a000 | 0x9a000 | end of the RW/RELRO PT_LOAD (`load2.memhi`), the page the writable window starts at; the same value in both images |
| `tfib_at_rw_len` | 0x55c000 | 0x55c000 | `IMG_TOP - rw_lo`, = the last PT_LOAD's page-rounded size in both images |
| `tfib_at_ph_addr_z` | 0x10040 | 0x10040 | `img_lo + e_phoff`; `e_phoff = 0x40` in both |
| `tfib_at_ph_ent_z`, `tfib_at_ph_num_z` | 56, 11 | 56, 11 | `e_phentsize`, `e_phnum` of asan-ubsan |
| `tfib_at_n_res` | 4 | 4 | PT_LOADs of asan-ubsan (4) |
| `tfib_at_shadow_off` | 0x7fff8000 | 0x7fff8000 | the runtime's shadow base; the B core states it for this image in `lib/B/Prog/BoxBReacBoxregInit.v:77` (`SBR`) and `lib/B/Prog/BoxBMacIsZero.v:78` (`MZ_SB`), and the checker resolves it to ASan's `kLowShadowBeg`, not an image address |
| `tfib_at_x_imemset` | 0x63424 | 0x63484 | `__sanitizer_internal_memset` |
| `tfib_at_x_imemcpy` | 0x633a8 | 0x63408 | `__sanitizer_internal_memcpy` |
| `tfib_at_x_memset` | 0x92588 | 0x929ac | musl `memset` |
| `tfib_at_x_memcpy` | 0x92184 | 0x925a8 | musl `memcpy` |
| `tfib_at_x_memiszero` | 0x63954 | 0x639b4 | `__sanitizer::mem_is_zero` |
| `tfib_at_x_istrncpy` | 0x63850 | 0x638b0 | `__sanitizer::internal_strncpy` |
| `tfib_at_x_popfree` | 0x36344 | 0x363a4 | `SizeClassAllocator64<AP64>::PopulateFreeArray+0x1bc` |
| `tfib_at_x_sniff`, `tfib_at_sniff_tab`, `tfib_at_sniff_cell` | 0 | 0 | not addresses (0 in the A file too) |
| `tfib_at_x_envscan` | 0x87f88 | 0x883ac | `__init_libc+0x38` |
| `tfib_at_x_envscan_k` | 0x87f94 | 0x883b8 | `__init_libc+0x44` |
| `tfib_at_x_pnscan` | 0x8804c | 0x88470 | `__init_libc+0xfc` |
| `tfib_at_x_pnscan_k` | 0x88058 | 0x8847c | `__init_libc+0x108` |
| `tfib_at_stops_more` | 12 addresses | 0x34018, 0x3563c, 0x53790, 0x59b48, 0x59b5c, 0x59b70, 0x5f500, 0x5f5d0, 0x6cafc, 0x6da08, 0x6db98, 0x778f0 | each is `<function>+<offset>`; see below |

Every interior (non-start) address was verified instruction by instruction: the asan address is instruction *i* of
its function, the emitted asan-ubsan address is instruction *i* of the twin function, and the two mnemonics agree.
All 17 of them pass (`work/interior.py`): `x_popfree` insn 111/220 `srli`; `x_envscan` 14/139 `ld`;
`x_envscan_k` 17/139 `auipc`; `x_pnscan` 63/139 `lbu`; `x_pnscan_k` 66/139 `addi`; the 12 `stops_more` entries
(`SealedHangOnAllocationFailure+0x24`, `QuarantineCache<QuarantineCallback>::Enqueue+0x190`,
`PoisonShadow+0x4a4`, `SealedReserveShadow+0x1b0/+0x1c4/+0x1d8`, `ReportMmapFailureAndDie+0x30`,
`ReportMunmapFailureAndDie+0x28`, `MapDynamicShadow+0x158`, `MmapFixedNoReserve+0xc4`,
`ReservedAddressRange::Init+0xc4`, `InternalSymbolizer::Flush+0x0`), each a `j` instruction at the same index in
both images.

## Checks run on the generated file

`work/check.py`, against the asan-ubsan symtab and the A file:

```
A rows 524 | B rows 524
same names, same order: True
duplicate names: []
duplicate ranges: []
outside .text [0x2ffb8, 0x97d40): []
A not a FUNC st_value: []
E not st_value+st_size of the same symbol: []      (the two size-0 asm rows excepted)
port_core_refused occurrences: 0
literal 0x5f6000 / 6250496 / 781312: 0
rows whose length differs from the A row: []
tail rows A/B: 51 51 names equal: True
tail values outside [0x10000, 0x5f6000) other than shadow_off/rw_len: []
line count: 630
```

### Address checker (`port_addr_check.py.frozen-39e67a7eb166`), A file vs this file

1136 numerals paired, 1130 clean: `SAME-SYMBOL` 1119, `IMAGE-EXTENT-SAME` 3 (`tfib_bss_hi`, `tfib_E_musl_read`,
`tfib_at_rw_lo`), `NON-ADDRESS-SAME` 7, `SAME-GEOMETRY` 1 (`tfib_at_rw_len` = the target's own `seg3.size`).
Six flags, all accounted for:

| flag | row | verdict |
|---|---|---|
| `KIND-CHANGED` | `tfib_text_hi`, `tfib_tbss_lo` (0x97920 -> 0x97d40) | no fix. 0x97d40 is `.tbss`'s start in the target, measured in its section table; in asan-ubsan `.text` ends at the same address, so the checker also reads it as `load1.memhi`. The A value is the same boundary. |
| `IDENT-MISMATCH` | `tfib_A_MemToShadow_3c6cc`, `tfib_E_MemToShadow_3c6cc` | no fix. The hex run inside the ROW NAME is the asan address; the row keeps lib/A's name by instruction. The values 0x3c72c / 0x3c868 are the ones the checker itself names (`the target has it at __asan::MemToShadow@0x3c72c`). |
| `UNRESOLVED` | `tfib_E_set_thread_area` | no fix, same flag as in the A lane: `__set_thread_area` is size-0 asm, 0x94c3c is the next FUNC (`__unmapself`) and the length 0xc equals the A row's. |
| `UNRESOLVED` | `tfib_at_ph_addr_z` | no fix, same flag as in the A lane: 0x10040 = `img_lo + e_phoff` and `e_phoff = 0x40` in both images, so the equal value is right, not stale. |

## Commands

Run from the repository root, with the scripts in `work/` (this directory). They are those of commit
`0ec8bd3fae71ca36acb3467a84b0dd52f3cf3893` except `check.py` (sha256 21c2cd4c570e3ddb52b6047f350ebdcaa4ef4e222a1db1183f26204f9d9d5814),
which differs from that commit's `check.py` (sha256 4c71e079b0c27662467ec9d573bec7160b5162cb333ea1bf725e5cc55c4c0d0f) only
in its docstring (line 1).
They read three variables, none with a default (a script stops with a message when one is not set):

- `PIPELINE_ROOT`: the pipeline's `libreac` directory. The run of record used the one whose files have these sha256:
  `bin/fuzz_boxreg/fuzz_boxreg.asan` eacfa20547ad7dc0d24164010513fcc8af4ba5e557ff3f391a07559e3e34a6df,
  `bin/fuzz_boxreg/fuzz_boxreg.asan-ubsan` 7620eb05e0adf5cb5ea350a6fe814d02d6ddb2685ec03477d0d4a85d249b0d85,
  `unstripped/fuzz_boxreg/fuzz_boxreg.asan` 4532568b621d62be2c79a1e2cf52cd1393008542eeb32e465d50b90d68e8f7a3,
  `unstripped/fuzz_boxreg/fuzz_boxreg.asan-ubsan` 1d548458eac37ae17f9e8dfb06a5dfef3c606ec9e03eca8ef291d5fec9dce495.
- `REVCHECK_DIR`: a directory with `revcheck.py` from `002698d25b7653ae4f5ef9096c4f8a3da4dac534:frame/revcheck.py`
  (sha256 06fc9cefdb2080f7c4c577f572114f544a1c47330d7837661a532a608953653d).
- `ELFDIS_DIR`: a directory with `elfdis.py` from `217c0af79e0d8be29b6aa5f568b03cfe250712ab:audit-tools/elfdis.py`
  (sha256 ed45f6bea2e54eff8a6fa9bed0bd4fec353f7c6887c0ce3472a53725f41ccab2); it needs capstone 5.0.7.

The address checker is `aba86b55203fd33bb7e87c049f3c8de0f37b5ded:audit-tools/port_addr_check.py.frozen-39e67a7eb166`
(sha256 39e67a7eb1664338976f92f8d71c66c9c48ef2bcd7c88acf79735a93de962f97) with `scan_literals.py` from the same commit
beside it (sha256 ae01d69b2ee4af269258982bef0de35a38a44d2b8832b62ef217e58439cd5804); it needs pyelftools (0.33 used).

Re-run with the commands below from a clean checkout of `0ec8bd3fae71ca36acb3467a84b0dd52f3cf3893`, three times (twice
inside `work/`, once with every script started from the repository root): `../AB1w.v` is byte-identical to
`lib/B/AB1w.v` (sha256 27b8781cd69c6a92b7ccee4971304eb28cf713c4f50a447d9302def8d69d5844, all three); `rows.json`,
`resolved.json` and `pac.tsv` are byte-identical to the run of record; the output of `check.py`, `interior.py`,
`facts.py`, `tail.py` and `spot.py` is identical to that of the scripts before that commit; no file is left outside
`work/`. `syms.json` and the output of `sec.py` hold the repr of bound methods (`dump.py` and `sec.py` print `e.loads` /
`e.tls` without calling them), so they differ from run to run in those object addresses only; with the addresses
masked, the three runs and the run of record are identical.
The same re-run with this directory's `check.py`, from a clean checkout of this commit, once inside `work/` and once
from the repository root, gives: `../AB1w.v` is byte-identical to `lib/B/AB1w.v`; `rows.json`, `resolved.json`, `pac.tsv` and
the output of `check.py`, `interior.py`, `facts.py`, `tail.py` and `spot.py` are identical to the run of record, and so
are `syms.json` and the output of `sec.py` with the object addresses masked; no file is left outside `work/`.

History of header line 5 of `AB1w.v`: the generator before `0ec8bd3fae71` wrote `(tfib_A_* / tfib_E_*)` there; its
`*)` closes the Coq comment early, so the shipped `AB1w.v` was edited by hand at that line after generation (`gen.py`
was last changed at 2026-10-28 23:45:53Z, the address checker wrote `pac.tsv` from the file at 23:47:49Z, and the file
was last changed at 2026-10-29 02:57:05Z). `0ec8bd3fae71` makes `gen.py` write the shipped text, `(the tfib_A_ and
tfib_E_ rows)`, so the regenerated file is the shipped file byte for byte.

```bash
export PIPELINE_ROOT=...    # the directory described above
D=proofs/libreac/fuzz_boxreg/provenance/core-reloc/ab1wB
G=$(mktemp -d)              # a throwaway repository: the fetch leaves this clone unchanged
git -C "$G" init -q
git -C "$G" remote add origin "$(git remote get-url origin)"
git -C "$G" fetch --depth=1 --filter=blob:none origin 002698d25b7653ae4f5ef9096c4f8a3da4dac534 \
  217c0af79e0d8be29b6aa5f568b03cfe250712ab aba86b55203fd33bb7e87c049f3c8de0f37b5ded
export REVCHECK_DIR=$(mktemp -d) ELFDIS_DIR=$(mktemp -d)
git -C "$G" show 002698d25b7653ae4f5ef9096c4f8a3da4dac534:frame/revcheck.py > "$REVCHECK_DIR/revcheck.py"
git -C "$G" show 217c0af79e0d8be29b6aa5f568b03cfe250712ab:audit-tools/elfdis.py > "$ELFDIS_DIR/elfdis.py"
cd "$D/work"
python3 dump.py         # both symtabs -> syms.json (revcheck rc.Elf)
python3 sec.py          # section tables, PT_LOADs, e_phoff/e_phentsize/e_phnum of both images
python3 map.py          # map every row by symbol (by code where a name repeats)   -> rows.json
python3 resolve.py      # pair every row (symbol, then code), verdict it   -> resolved.json
python3 interior.py     # instruction-index check of the 17 interior tail addresses
python3 facts.py        # entry, gp, the absent symbols, the sealed string, the GOT slots
python3 tail.py         # place every tfib_D_* / tfib_at_* value and read it in asan-ubsan
python3 spot.py         # spot checks: size-0 asm rows, the `dummy` rows, MemToShadow neighbours
python3 gen.py          # write ../AB1w.v
python3 check.py        # the checks listed above
cd -
X=$(mktemp -d)
git -C "$G" show aba86b55203fd33bb7e87c049f3c8de0f37b5ded:audit-tools/port_addr_check.py.frozen-39e67a7eb166 \
  > "$X/port_addr_check.py.frozen-39e67a7eb166"
git -C "$G" show aba86b55203fd33bb7e87c049f3c8de0f37b5ded:audit-tools/scan_literals.py > "$X/scan_literals.py"
R=$PIPELINE_ROOT
python3 "$X/port_addr_check.py.frozen-39e67a7eb166" \
  --src proofs/libreac/fuzz_boxreg/lib/A/AB1w.v \
  --src-image A=$R/bin/fuzz_boxreg/fuzz_boxreg.asan:$R/unstripped/fuzz_boxreg/fuzz_boxreg.asan \
  --dst $D/AB1w.v \
  --dst-image A=$R/bin/fuzz_boxreg/fuzz_boxreg.asan-ubsan:$R/unstripped/fuzz_boxreg/fuzz_boxreg.asan-ubsan \
  --out $D/work/pac.tsv --summary
```

Nothing was committed, pushed or built.
