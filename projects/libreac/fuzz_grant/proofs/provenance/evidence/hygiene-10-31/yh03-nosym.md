# YH03 address cells, checked against each copy's own pin

`lib/Reusable/YH03.v` is read against the plain image and `lib/U/Reusable/YH03.v` against the ubsan image. Both pins
equal the ones the build's `harness.yaml` names: plain sha256 e84d949045ee, ubsan sha256 ae8453d49b86 (unstripped
twins sha256 d381bf799a3e and add7ed0b7ac6).

## Tools

- `yh03check.py` (sha256 fb3bfbc1eea8; internal record) and `yh03regen.py` (sha256 1254e5c96a44; internal record),
  self-test `223 known answers OK (yh03regen 163 + yh03check 60)`, run with `--pins projects/libreac/fuzz_grant/harness.yaml`.

## Before and after, per copy

- Before (the current release): `# rows checked: 124; rows not OK: 26`, all 26 ABSENT code cells, and
  `# REFUSED: 1 problem(s)` (per cell: `src0_D_got_DYNAMIC_reserved` was not `.got`'s start), exit 2.
- After: exit 0, `# section bounds: 18 of 18 section cells equal the image's section headers`,
  `# rows checked: 98; rows not OK: 0`. The `start` row reads `OK SIZE0` (its address is the image's own `_start`).

## What changed, per copy

- 26 absent code cells removed by `yh03regen.py --write` (50 definitions on 26 lines, the 14 moved-by-address
  A_ / E_ rows included): the donor functions `read_frameconfig` .. `create_byte_list_block` and `unlist_locked_file`,
  `fclose`, `fopen`, `fmodeflags`, `fdopen`, `stdio_read`, `ofl_add`, `strchr`, `strchrnul`, `strlen`, `unlink`, which
  this image does not hold at those addresses.
- `str_inf` 0x10313 -> 0x10301 and `str_INF` 0x10317 -> 0x10305 (`yh03regen.py --write`).
- `got_DYNAMIC_reserved` set to the image's `.got` start, GOT[0]: plain 0x1e2d8, ubsan 0x1ee48.
- Removed, each with 0 readers outside its own definition (`git grep -nw`):
  - `str_n0X_0X_0X_0x_0x_0x` 0x102a5: donor value left unmoved, 3 bytes inside this image's own string (which starts
    at 0x102a2), 0 readers; evidence is the byte read.
  - `str_2` 0x102d1: donor value left unmoved, 3 bytes inside this image's own string (which starts at 0x102ce), 0
    readers; evidence is the byte read.
  - `str` 0x102cd: TRUE (an empty string at its own start), removed as unread.
  - `errmsgstr` (plain 0x10a50, ubsan 0x10a88): FALSE, inside the error-message block (the byte before it is 'F'),
    so it starts no string.
  - the 12 NOSYM cells below that are FALSE of the image.

## String cells after the change

13 per copy, each read at its own address in its own pin up to the first NUL, and each a string start (the byte before
it is NUL). The same in both copies:

| cell | address | string |
|---|---|---|
| `str_n0X0x` | 0x10298 | `-+   0X0x` |
| `str_cli_out_of_memory_n` | 0x102b5 | `cli: out of memory\n` |
| `str_d_n` | 0x102c9 | `%d\n` |
| `str_usage_s_INPUT_n` | 0x102d0 | `usage: %s INPUT\n` |
| `str_cli_config_len_overruns` | 0x102e1 | `cli: config_len overruns input\n` |
| `str_inf` | 0x10301 | `inf` |
| `str_INF` | 0x10305 | `INF` |
| `str_cli_input_u_bytes_refuse` | 0x10309 | `cli: input >= %u bytes, refused\n` |
| `str_cli_cannot_open_s_n` | 0x1032a | `cli: cannot open %s\n` |
| `str_cli_read_error_on_s_n` | 0x1033f | `cli: read error on %s\n` |
| `str_cli_input_shorter_than_h` | 0x10365 | `cli: input shorter than header\n` |
| `str_dev_null` | 0x10385 | `/dev/null` |
| `str_null` | 0x1038f | `(null)` |

## The NOSYM cells

`yh03check.py` leaves a D cell with no symbol of its name unjudged (NOSYM, 43 per copy). Each was read against its
own copy's pin. A FALSE cell with 0 readers is removed; a TRUE one stays; no value was set by hand.

### Counts

| copy | NOSYM cells checked | TRUE (stays) | FALSE, 0 readers (removed) | FALSE with readers (FINDING) |
|---|---|---|---|---|
| plain, `lib/Reusable/YH03.v` | 43 | 31 | 12 | 0 |
| ubsan, `lib/U/Reusable/YH03.v` | 43 | 31 | 12 | 0 |

TRUE in each copy: `const_HIGHS_0x8080808080808080`, `const_ONES_0x0101010101010100`, `debruijn32`, `size_classes`, the 18
`got_*` cells (GOT[1]..GOT[18]), the 3 adapter cells (the fuzz adapter's objects `oft_argc`, `oft_in_callback`, `oft_aligned_copy.empty`), `atexit_lock`, `atexit_slot`,
`atexit_head`, `atexit_builtin`, `stderr_buf`, `stdout_buf`.

FALSE in each copy (the same 12 lines in both files: 158, 159, 161, 163, 164, 165, 166, 167, 168, 173, 174, 175): the 9
`const_double_*` / `const_u64_*` cells and the 3 `jt_*` cells. Each has 0 readers outside YH03.v and is not read inside YH03.v
either (its only `git grep` hit in each file is its own definition).

### How each NOSYM cell was read

- `const_*`: the 8 bytes at V must be the constant that the name says. Doubles come from the name (`0x1p28`, `1_0`, ...).
  `fmt_fp_1e9_recip_misc` is the u64 ceil(2^84 / 1e9) = `0x0044b82fa09b5a53`, which musl's `fmt_fp` loads with `ld` to divide by
  1e9. `0x1p_969_0x1p_1022_0x1p` is the double 0x1p-969 (= 0x1p-1022 * 0x1p53, the scale that `scalbn` loads); under any reading
  of that name the bytes at grant's V are neither 0x1p-969 nor 0x1p-1022. For a FALSE cell the row also gives where the named
  constant really is and which code loads it (evidence only; the ruling removes the cell, it does not move it).
- `jt_*`: the function's own jump tables are found from its code: `auipc; addi; add; lw; add; jr` (clang's PIC switch), with
  the `li` bound before the `bltu`. TRUE only if V is the base of that table (tables numbered by address).
- `got_*`: V is in `.got`, the slot's word equals the named symbol's value (0 for a weak undefined symbol), and the function that
  uses that symbol loads that slot.
- the adapter cells, `atexit_*`, `stderr_buf`, `stdout_buf`: a symbol of the named object (name plus the twin's STT_FILE) starts
  exactly at V. YH03 names the adapter cells with a short prefix of its own for the adapter's `oft_` objects, and v6.4 itself
  reports each as RENAMED to its `oft_` object, and the donor's fuzz adapter source (`ossfuzz_adapter.h`)
  names them `oft_arg0`, `oft_argv`, `oft_argc`, `oft_aligned_copy.empty`, `oft_in_callback`.
- `debruijn32`: the 32 bytes satisfy byte[(2^k * 0x077CB531 mod 2^32) >> 27] = k for all k < 32, and `alloc_slot` forms V.
- `size_classes`: `__malloc_size_classes` (musl mallocng `#define size_classes __malloc_size_classes`) starts at V, and its 96
  bytes equal musl's 48-entry table.
- Readers per copy: files under `lib/U/` import `...fuzz_grant.lib.U.Reusable.*` and so read the U copy; the others read the
  plain copy. The script asserts that no reader file imports the other side's library.

### The 24 removal records (12 per copy)

- `src0_D_const_double_0x1p28` (`lib/Reusable/YH03.v:158`): NOSYM, FALSE (0x103a8, the 8 bytes there are 0x8080808080808080 (formed by memchr@0x1cd78 ld), not the double 0x1.0000000000000p+28 (u64 0x41b0000000000000); the double 0x1.0000000000000p+28 (u64 0x41b0000000000000) is at 0x10398 (formed by fmt_fp@0x1917c fld)), 0 readers, removed
- `src0_D_const_double_1_0` (`lib/Reusable/YH03.v:159`): NOSYM, FALSE (0x103b0, the 8 bytes there are 0x3fe0000000000000 (formed by fmt_fp@0x19b08 fld), not the double 0x1.0000000000000p+0 (u64 0x3ff0000000000000); the double 0x1.0000000000000p+0 (u64 0x3ff0000000000000) is at 0x103a0 (formed by fmt_fp@0x19d18 fld)), 0 readers, removed
- `src0_D_const_double_0_5` (`lib/Reusable/YH03.v:161`): NOSYM, FALSE (0x103c0, the 8 bytes there are 0x7fe0000000000000 (formed by scalbn@0x1b3b4 fld), not the double 0x1.0000000000000p-1 (u64 0x3fe0000000000000); the double 0x1.0000000000000p-1 (u64 0x3fe0000000000000) is at 0x103b0 (formed by fmt_fp@0x19b08 fld)), 0 readers, removed
- `src0_D_const_double_0x1p1023` (`lib/Reusable/YH03.v:163`): NOSYM, FALSE (0x103d0, the 8 bytes there are 0x0044b82fa09b5a53 (formed by fmt_fp@0x194e8 ld), not the double 0x1.0000000000000p+1023 (u64 0x7fe0000000000000); the double 0x1.0000000000000p+1023 (u64 0x7fe0000000000000) is at 0x103c0 (formed by scalbn@0x1b3b4 fld)), 0 readers, removed
- `src0_D_const_double_1_5` (`lib/Reusable/YH03.v:164`): NOSYM, FALSE (0x103d8, the 8 bytes there are 0x0360000000000000 (formed by scalbn@0x1b3ec fld), not the double 0x1.8000000000000p+0 (u64 0x3ff8000000000000); the double 0x1.8000000000000p+0 (u64 0x3ff8000000000000) is at 0x103c8 (formed by fmt_fp@0x19d24 fld)), 0 readers, removed
- `src0_D_const_u64_fmt_fp_1e9_recip_misc` (`lib/Reusable/YH03.v:165`): NOSYM, FALSE (0x103e0, the 8 bytes there are 0x4770000000000000 (formed by frexpl@0x1aa48 fld), not the u64 0x0044b82fa09b5a53; the u64 0x0044b82fa09b5a53 is at 0x103d0 (formed by fmt_fp@0x194e8 ld)), 0 readers, removed
- `src0_D_const_double_0x1p_969_0x1p_1022_0x1p` (`lib/Reusable/YH03.v:166`): NOSYM, FALSE (0x103e8, the 8 bytes there are 0x000fff000fff0010 (formed by LLVMFuzzerTestOneInput@0x137c0 ld), not the double 0x1.0000000000000p-969 (u64 0x0360000000000000); the double 0x1.0000000000000p-969 (u64 0x0360000000000000) is at 0x103d8 (formed by scalbn@0x1b3ec fld)), 0 readers, removed
- `src0_D_const_u64_0x0101010101010102` (`lib/Reusable/YH03.v:167`): NOSYM, FALSE (0x103f0, the 8 bytes there are 0x0010080006040000 (formed by LLVMFuzzerTestOneInput@0x135d0 addi), not the u64 0x0101010101010102; the u64 0x0101010101010102 is nowhere in the image (no copy in any PT_LOAD's file bytes, at any alignment)), 0 readers, removed
- `src0_D_const_double_0x1p120` (`lib/Reusable/YH03.v:168`): NOSYM, FALSE (0x103f8, the 8 bytes there are 0x1111001109111011 (no auipc pair forms this address), not the double 0x1.0000000000000p+120 (u64 0x4770000000000000); the double 0x1.0000000000000p+120 (u64 0x4770000000000000) is at 0x103e0 (formed by frexpl@0x1aa48 fld)), 0 readers, removed
- `src0_D_jt_printf_core_1` (`lib/Reusable/YH03.v:173`): NOSYM, FALSE (0x11b40, the address is in no section and in no PT_LOAD (unmapped), not a table; printf_core's tables are 0x10728 (56 x 4-byte entries, dispatch jr at 0x184d4); 0x10808 (8 x 4-byte entries, dispatch jr at 0x1864c)), 0 readers, removed
- `src0_D_jt_printf_core_2` (`lib/Reusable/YH03.v:174`): NOSYM, FALSE (0x11c20, the address is in no section and in no PT_LOAD (unmapped), not a table; printf_core's tables are 0x10728 (56 x 4-byte entries, dispatch jr at 0x184d4); 0x10808 (8 x 4-byte entries, dispatch jr at 0x1864c)), 0 readers, removed
- `src0_D_jt_pop_arg` (`lib/Reusable/YH03.v:175`): NOSYM, FALSE (0x11c40, the address is in no section and in no PT_LOAD (unmapped), not a table; pop_arg's tables are 0x10828 (18 x 4-byte entries, dispatch jr at 0x18de4)), 0 readers, removed
- `src0_D_const_double_0x1p28` (`lib/U/Reusable/YH03.v:158`): NOSYM, FALSE (0x103a8, the 8 bytes there are 0x3ff0000000000000 (formed by fmt_fp@0x1a888 fld), not the double 0x1.0000000000000p+28 (u64 0x41b0000000000000); the double 0x1.0000000000000p+28 (u64 0x41b0000000000000) is at 0x10398 (formed by fmt_fp@0x19cec fld)), 0 readers, removed
- `src0_D_const_double_1_0` (`lib/U/Reusable/YH03.v:159`): NOSYM, FALSE (0x103b0, the 8 bytes there are 0x8080808080808080 (formed by memchr@0x1d8e8 ld), not the double 0x1.0000000000000p+0 (u64 0x3ff0000000000000); the double 0x1.0000000000000p+0 (u64 0x3ff0000000000000) is at 0x103a8 (formed by fmt_fp@0x1a888 fld)), 0 readers, removed
- `src0_D_const_double_0_5` (`lib/U/Reusable/YH03.v:161`): NOSYM, FALSE (0x103c0, the 8 bytes there are 0x0101010101010100 (formed by memchr@0x1d8e0 ld), not the double 0x1.0000000000000p-1 (u64 0x3fe0000000000000); the double 0x1.0000000000000p-1 (u64 0x3fe0000000000000) is at 0x103b8 (formed by fmt_fp@0x1a678 fld)), 0 readers, removed
- `src0_D_const_double_0x1p1023` (`lib/U/Reusable/YH03.v:163`): NOSYM, FALSE (0x103d0, the 8 bytes there are 0x3ff8000000000000 (formed by fmt_fp@0x1a894 fld), not the double 0x1.0000000000000p+1023 (u64 0x7fe0000000000000); the double 0x1.0000000000000p+1023 (u64 0x7fe0000000000000) is at 0x103c8 (formed by scalbn@0x1bf24 fld)), 0 readers, removed
- `src0_D_const_double_1_5` (`lib/U/Reusable/YH03.v:164`): NOSYM, FALSE (0x103d8, the 8 bytes there are 0x0044b82fa09b5a53 (formed by fmt_fp@0x1a058 ld), not the double 0x1.8000000000000p+0 (u64 0x3ff8000000000000); the double 0x1.8000000000000p+0 (u64 0x3ff8000000000000) is at 0x103d0 (formed by fmt_fp@0x1a894 fld)), 0 readers, removed
- `src0_D_const_u64_fmt_fp_1e9_recip_misc` (`lib/U/Reusable/YH03.v:165`): NOSYM, FALSE (0x103e0, the 8 bytes there are 0x0360000000000000 (formed by scalbn@0x1bf5c fld), not the u64 0x0044b82fa09b5a53; the u64 0x0044b82fa09b5a53 is at 0x103d8 (formed by fmt_fp@0x1a058 ld)), 0 readers, removed
- `src0_D_const_double_0x1p_969_0x1p_1022_0x1p` (`lib/U/Reusable/YH03.v:166`): NOSYM, FALSE (0x103e8, the 8 bytes there are 0x4770000000000000 (formed by frexpl@0x1b5b8 fld), not the double 0x1.0000000000000p-969 (u64 0x0360000000000000); the double 0x1.0000000000000p-969 (u64 0x0360000000000000) is at 0x103e0 (formed by scalbn@0x1bf5c fld)), 0 readers, removed
- `src0_D_const_u64_0x0101010101010102` (`lib/U/Reusable/YH03.v:167`): NOSYM, FALSE (0x103f0, the 8 bytes there are 0x000fff000fff0010 (formed by LLVMFuzzerTestOneInput@0x13b28 ld), not the u64 0x0101010101010102; the u64 0x0101010101010102 is nowhere in the image (no copy in any PT_LOAD's file bytes, at any alignment)), 0 readers, removed
- `src0_D_const_double_0x1p120` (`lib/U/Reusable/YH03.v:168`): NOSYM, FALSE (0x103f8, the 8 bytes there are 0x0010080006040000 (formed by LLVMFuzzerTestOneInput@0x1385c addi), not the double 0x1.0000000000000p+120 (u64 0x4770000000000000); the double 0x1.0000000000000p+120 (u64 0x4770000000000000) is at 0x103e8 (formed by frexpl@0x1b5b8 fld)), 0 readers, removed
- `src0_D_jt_printf_core_1` (`lib/U/Reusable/YH03.v:173`): NOSYM, FALSE (0x11b40, the address is inside .eh_frame (mapped), not a table; printf_core's tables are 0x10760 (56 x 4-byte entries, dispatch jr at 0x19044); 0x10840 (8 x 4-byte entries, dispatch jr at 0x191bc)), 0 readers, removed
- `src0_D_jt_printf_core_2` (`lib/U/Reusable/YH03.v:174`): NOSYM, FALSE (0x11c20, the address is in no section and in no PT_LOAD (unmapped), not a table; printf_core's tables are 0x10760 (56 x 4-byte entries, dispatch jr at 0x19044); 0x10840 (8 x 4-byte entries, dispatch jr at 0x191bc)), 0 readers, removed
- `src0_D_jt_pop_arg` (`lib/U/Reusable/YH03.v:175`): NOSYM, FALSE (0x11c40, the address is in no section and in no PT_LOAD (unmapped), not a table; pop_arg's tables are 0x10860 (18 x 4-byte entries, dispatch jr at 0x19954)), 0 readers, removed
