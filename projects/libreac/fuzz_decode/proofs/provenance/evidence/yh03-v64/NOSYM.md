# provenance/evidence/yh03-v64: the NOSYM cells of the two YH03 address tables, read against the unit's pins

yh03check fb3bfbc1eea8 checks a D cell by the symbol its name says. Where no symbol of the image carries that name it
reports the cell NOSYM and checks nothing about it: 44 cells per file (`check-fb3bfbc1eea8.<side>.summary.txt`, "NOSYM
44 (no symbol of the name, not checked)"). This file reads every one of those 44 cells against the unit's pinned
binaries and judges it. No .v file is changed by it, and no function is proved here: it is provenance only.

Result: **44 of 44 TRUE in each file, 0 FALSE, 0 UNSETTLED.** No cell is removed, and both tables stay as they are.

## 1. Inputs

| what | sha256 | checked against |
|---|---|---|
| `lib/Reusable/YH03.v` (plain) and `lib/U/Reusable/YH03.v` (ubsan) | read at the series commit 5d8494b09e34 | - |
| plain pin `PINNED_DIR/fuzz_decode.plain` | `556b61e63c44907b003aff8b1e8b926863db277b4f2897fdc58967a7beddc9cc` | `builds.plain` of `projects/libreac/fuzz_decode/harness.yaml` |
| ubsan pin `PINNED_DIR/fuzz_decode.ubsan` | `ff70f30e22dcdcea42fe294ed23995ec278b6c66ace0ecade26d2a917657c1b9` | `builds.ubsan` of the same harness.yaml |
| plain twin `TWIN_DIR/fuzz_decode.plain` | `3761f28504c43cd63b6f9ffeaa804ca776583cb46bfbca9036644d201f947325` | yh03check: the twin's 4 PT_LOADs equal the pin's |
| ubsan twin `TWIN_DIR/fuzz_decode.ubsan` | `01b24c88d35d3c65558dd016f210506a4ac341850d6f55f8a7347d2d348cedcf` | the same, for the ubsan side |

The plain file is read against the plain pin, the U file against the ubsan pin. Bytes come from the PIN; symbols and
their compilation units (STT_FILE) from the TWIN. `run.sh` beside this file runs everything.

## 2. The rule each cell is judged by (nosym_table.py)

| class | cells | the rule |
|---|---|---|
| const | 10 | the 8 bytes at the value are the constant the name encodes |
| got | 18 | the 8 bytes at the value are the address of the symbol the name says (`x`, `_x` or `__x`), or 0 when the twin defines no such symbol: a weak undefined reference |
| table | 5 | the real object the name says: a jump table formed only inside the named function, in the shape `slli / add / lw / add / jr`; the De Bruijn table a permutation of 0..31 that code forms; `size_classes` a sized OBJECT starting there |
| object | 11 | a sized OBJECT symbol starts exactly at the value, and its name or its compilation unit is the one the cell name says |

A rule that does not apply gives UNSETTLED, never a pass. Which code forms an address is the comparison kit's own
target pass (`targets` of repin_check, through strictcmp3.py / drvcmp.py of cmpkit 86da41d3ef68), printed per address by
`refs.py` in `nosym-refs.<side>.out`.

The per-cell tables are `nosym-plain.tsv` and `nosym-ubsan.tsv`: file, line, cell, value, section, class, expected,
found, verdict, readers. The readers are `nosym-readers.tsv` (`git grep -w src0_<cell>` over
`proofs/libreac/fuzz_decode` at 5d8494b09e34, less the two YH03.v themselves).

The scanner of record blocks one driver prefix outside `.v` files, so five cell names are written here and in the
tables with that prefix replaced by `CODENAME` (`D_CODENAME_arg0`, `_argc`, `_argv`, `_in_callback`,
`_aligned_copy_empty`). `run.sh` reads the prefix from `lib/Reusable/YH03.v` itself and passes it to the tool as
`--mask`, so no file of this slice holds it; every row gives the file and the line, where the real name stands.

## 3. What the measurements show

- **const (10 per file).** Every one holds its constant: `0x1p28`, `1.0`, `0.5`, `0x1p1023`, `1.5`, `0x1p120`, the
  HIGHS mask `0x8080808080808080`, the ONES mask `0x0101010101010100`, `0x1p-969`, and the fmt_fp reciprocal.
  - `D_const_u64_fmt_fp_1e9_recip_misc` holds `0x0044b82fa09b5a53` = ceil(2^84 / 1e9), the magic an unsigned division
    by 1e9 multiplies by (mulhu, then shift right 84 - 64 = 20). The only code of either image that forms its address
    is `fmt_fp+0x520`, and the next words there build the divisor itself: `lui a1,0x3b9ad ; addiw a1,a1,-0x600` =
    1000000000.
  - `D_const_double_0x1p_969_0x1p_1022_0x1p` is a slug that lists three source constants. The image holds one object at
    the cell's value, the double `0x1p-969`, which is the first of them: in scalbn the compiler folds
    `0x1p-1022 * 0x1p53` into `0x1p-969`, and neither `0x1p-1022` (`0010000000000000`) nor `0x1p53`
    (`4340000000000000`) is a separate 8-aligned word of either .rodata. The cell is right about the object at its
    value; it is not a claim that the other two exist.
- **got (18 per file).** Fourteen slots hold exactly the address of the symbol the name says (`main`, `_init`, `_fini`,
  `__cxa_finalize`, `stderr`, `stdout`, `__environ`, `__progname_full`, `__progname`, `__init_array_start` / `_end`,
  `__fini_array_start` / `_end`, `__stack_chk_guard`). Four hold 0, and 0 is what the slot of a weak undefined symbol
  holds; the code that reads each one shows which symbol it is:
  - `D_got_DYNAMIC` — read by `static_init_tls+0x58` (`ld t0`), in the loop that also materialises `PT_DYNAMIC` (2),
    `PT_TLS` (7) and `PT_GNU_RELRO` (`lui t3,0x6474e ; addiw t3,t3,0x551`): musl's
    `if (phdr->p_type == PT_DYNAMIC && _DYNAMIC)`. The image has no `_DYNAMIC`.
  - `D_got_register_frame_info` — `__do_init+0x40`, `ld` then `beqz` then the call: the weak-null test.
  - `D_got_deregister_frame_info` — `__do_fini+0x64`, the same shape.
  - `D_got_LLVMFuzzerInitialize` — `target_run+0x134`, `ld` then `beqz` then the call with `&argc` / `&argv`.
- **table (5 per file).** `D_jt_printf_core_1` and `_2` are formed only by `printf_core` (+0x534, +0x6ac) and
  `D_jt_pop_arg` only by `pop_arg` (+0x14), each in the jump-table shape `add / lw / add / jr` under a `bltu` bound.
  `D_debruijn32` is 32 bytes that are a permutation of 0..31, formed by `__libc_malloc_impl+0xec` and `alloc_slot`
  (+0x1d0, +0x370), beside the De Bruijn multiplier `lui a1,0x77cb` (0x077cb531); `src0_debruijn_len` is 32.
  `D_size_classes` starts exactly at `__malloc_size_classes{malloc.c}` (96 bytes), which 10 words of the malloc code
  form.
- **object (11 per file).** Each starts exactly at a sized OBJECT of the twin, and the STT_FILE says it is the one the
  name means: `oft_arg0` / `oft_argc` / `oft_argv` / `oft_in_callback` / `oft_aligned_copy.empty` of `adapter.c` for
  the five driver cells (lines 185-187, 198 and 199), `lock` / `slot` / `head` / `builtin` of
  `atexit.c` for the four `D_atexit_*`, and `buf{stderr.c}` (8 bytes) and `buf{stdout.c}` (1032 bytes) for the two
  stream buffers.

## 4. Readers

38 of the 44 cells have no reader outside the two YH03.v. Six are read (`nosym-readers.tsv` holds the lines):
`D_size_classes` 312, `D_got_stack_chk_guard` 156, `D_debruijn32` 132, `D_const_HIGHS_0x8080808080808080` 34,
`D_const_ONES_0x0101010101010100` 34, `D_CODENAME_aligned_copy_empty` 2. All six are TRUE, so none of those proofs rests on
a wrong value.

No cell is FALSE, so nothing was removed and no hand-set value was written.

## 5. The tables still pass, unchanged

Both files are byte-identical to the series commit, so yh03check fb3bfbc1eea8 was re-run on them as they are, the
plain pin on the plain file and the ubsan pin on the U file. Its summary lines are byte-identical to the
`check-fb3bfbc1eea8.<side>.summary.txt` beside this file, which carry:

- `# self-test: 223 known answers OK (yh03regen 163 + yh03check 60)`
- `# rows checked: 103; rows not OK: 0`
- `# D cells by symbol: 41 (OK 41, BAD 0) ... NOSYM 44`
- exit 0, and no REFUSED line in either run.

One definition per line: `grep -cE "Definition [a-z0-9]+_D_.*Definition [a-z0-9]+_D_"` prints 0 for both files.
