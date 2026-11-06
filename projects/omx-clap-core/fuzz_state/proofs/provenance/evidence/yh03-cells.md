# fuzz_state YH03 cell records (lib/Reusable/YH03.v = plain build, lib/U/Reusable/YH03.v = ubsan build)

Images: plain pin sha256 c9703541c41a, ubsan pin 6e4aa2cd877d (FACTS c8557374ad2e). Symbols come from unstripped twins of the same link, sha256 115c6ed24187 (plain) and a626088ba293 (ubsan); `drvcmp.py twins` (cmpkit 4bbd3a74be89 copy, drvcmp 4d70e90bc1fa) shows their PT_LOAD bytes equal the pins except the ELF header and .note.gnu.build-id.

Tools: yh03check e5d7cbda4e27 / yh03regen f357a8df6e49 (v6.3), yh03check fb3bfbc1eea8 / yh03regen 1254e5c96a44 (v6.4). Base of every count: the shipped fuzz_state tree 9a979984f23e.

## 1. Cell fix (v6.3 scope) and the .got cell

- `yh03regen --pinned <pin> --elf <twin> --syms-elf <twin> --pins projects/omx-clap-core/fuzz_state/harness.yaml --side <build> --unchecked-ok --write` per file (no `--proofs`, no `--accept`); self-test `151 known answers OK`. Per file 37 FIX: 32 A/E cells of functions the image links (by symbol), 5 string cells by the `--elf` string pass (str_n0X_0X_0X_0x_0x_0x, str_inf, str_INF, str_NAN, str_nan).
- src0_D_got_DYNAMIC_reserved: 0x1ed90 (the donor image's .got start) set to the .got start of this image, plain 0x22120, ubsan 0x22808 (the value the v6.3 refusal line names; GOT[0] of the pin holds 0). v6.4 reports it OK-GOT0 / KEEP-GOT0.
- One changed value has a reader: src0_A_stdio_seek (lib/Reusable/YI5c.v and lib/U/Reusable/YI5c.v, sk_seek): plain 0x1899c -> 0x189c8, ubsan 0x19084 -> 0x190b0 (the old value was inside __stdio_write).

## 2. Unread ABSENT cells removed (v6.4)

One `yh03regen v6.4 ... --proofs proofs/omx-clap-core/fuzz_state --unchecked-ok --write` run per file (self-test `163 known answers OK`) removed 24 ABSENT A/E pairs per file, each "ABSENT, 0 readers, removed": LZW_GenerateStream, cgif_addframe, cgif_close, cgif_newgif, cgif_raw_addframe, cgif_raw_close, cgif_raw_newgif, cgif_writecb, cmpPixel, create_byte_list, create_byte_list_block, fclose, fdopen, flushFrame, fmodeflags, fopen, freeCGIF, freeFrame, ofl_add, read_frameconfig, strchr, strchrnul, unlink, unlist_locked_file. The tool does not remove the string cells str / str_2; section 6 does.

## 3. NOSYM cells (no symbol of the name; v6.4 does not judge them), read against the pins

Each of the 45 NOSYM cells per file was judged TRUE or FALSE by what its name claims (constant bytes in a read-only section; table bytes and the function that reads them; a jump table at the dispatch base with entries inside the function; a .got cell's stored word; a static object at the start the reading code uses). A planted wrong value per class was called FALSE (62 controls). Per file 31 TRUE, 14 FALSE; no FALSE cell has a reader outside the two YH03.v files. The 14 FALSE cells were removed by deletion only (no value set); each: "NOSYM, FALSE, 0 readers, removed".

| build | line at 7fe64089be9c | cell | value | verdict | what the image holds there | readers |
|---|---|---|---|---|---|---|
| plain | 143 | const_double_0x1p28 | 0x103a8 | FALSE | bytes[8]=693a207265616420 sec=.rodata near=$d+0x2e[fuzz_state.c] in C string @0x103a6 'cli: read error on %s\n' | 0 |
| plain | 144 | const_double_1_0 | 0x103b0 | FALSE | bytes[8]=6572726f72206f6e sec=.rodata near=$d+0x36[fuzz_state.c] in C string @0x103a6 'cli: read error on %s\n' | 0 |
| plain | 145 | const_HIGHS_0x8080808080808080 | 0x10438 | TRUE | bytes[8]=8080808080808080 sec=.rodata near=$d+0x8[floatscan.c] | 17 lines in 3 files |
| plain | 146 | const_double_0_5 | 0x103c0 | FALSE | bytes[8]=006e616e00626173 sec=.rodata near=$d+0x46[fuzz_state.c] in C string @0x103bd 'NAN' | 0 |
| plain | 147 | const_ONES_0x0101010101010100 | 0x10448 | TRUE | bytes[8]=0001010101010101 sec=.rodata near=$d+0x0[memchr.c] | 17 lines in 3 files |
| plain | 148 | const_double_0x1p1023 | 0x103d0 | FALSE | bytes[8]=6c693a20696e7075 sec=.rodata near=$d+0x56[fuzz_state.c] in C string @0x103cf 'cli: input shorter than header\n' | 0 |
| plain | 149 | const_double_1_5 | 0x103d8 | FALSE | bytes[8]=742073686f727465 sec=.rodata near=$d+0x5e[fuzz_state.c] in C string @0x103cf 'cli: input shorter than header\n' | 0 |
| plain | 150 | const_u64_fmt_fp_1e9_recip_misc | 0x103e0 | FALSE | bytes[8]=72207468616e2068 sec=.rodata near=$d+0x66[fuzz_state.c] in C string @0x103cf 'cli: input shorter than header\n' | 0 |
| plain | 151 | const_double_0x1p_969_0x1p_1022_0x1p | 0x103e8 | FALSE | bytes[8]=65616465720a005c sec=.rodata near=$d+0x6e[fuzz_state.c] in C string @0x103cf 'cli: input shorter than header\n' | 0 |
| plain | 152 | const_u64_0x0101010101010102 | 0x103f0 | FALSE | bytes[8]=7525303478007b00 sec=.rodata near=$d+0x76[fuzz_state.c] in C string @0x103ef '\\u%04x' | 0 |
| plain | 153 | const_double_0x1p120 | 0x103f8 | FALSE | bytes[8]=5c25630062797465 sec=.rodata near=$d+0x7e[fuzz_state.c] in C string @0x103f8 '\\%c' | 0 |
| plain | 154 | debruijn32 | 0x10564 | TRUE | bytes[32]=00011c021d0e18031e16140f191104081f1b0d17151310071a0c12060b050a09 sec=.rodata near=$d+0x0[malloc.c] | 82 lines in 56 files |
| plain | 155 | size_classes | 0x10584 | TRUE | bytes[96]=0100020003000400050006000700080009000a000c000f001200140019001f0024002a0032003f004800540066007f009200aa00cc00ff00240154019901ff014802aa023203 | 180 lines in 77 files |
| plain | 158 | jt_printf_core_1 | 0x11b40 | FALSE | bytes[16]=c8c9d2d3d4d5d6d7d8d9dadb440e0000 sec=.eh_frame near=.eh_frame+0x758 of [0x113e8,0x11d30) (__EH_FRAME_LIST__[crtbegin.c] and __EH_FRAME_LIST_ | 0 |
| plain | 159 | jt_printf_core_2 | 0x11c20 | FALSE | bytes[16]=3808000024ab0000cc07000000440e30 sec=.eh_frame near=.eh_frame+0x838 of [0x113e8,0x11d30) (__EH_FRAME_LIST__[crtbegin.c] and __EH_FRAME_LIST_ | 0 |
| plain | 160 | jt_pop_arg | 0x11c40 | FALSE | bytes[16]=07c1c8c9d2d3d4440e00440b00000000 sec=.eh_frame near=.eh_frame+0x858 of [0x113e8,0x11d30) (__EH_FRAME_LIST__[crtbegin.c] and __EH_FRAME_LIST_ | 0 |
| plain | 173 | got_DYNAMIC | 0x22128 | TRUE | bytes[8]=0000000000000000 sec=.got near=stdout+0x10 | 0 |
| plain | 174 | got_main | 0x22130 | TRUE | bytes[8]=7c2e010000000000 sec=.got near=stdout+0x18 | 0 |
| plain | 175 | got_init | 0x22138 | TRUE | bytes[8]=e859010000000000 sec=.got near=stdout+0x20 | 0 |
| plain | 176 | got_fini | 0x22140 | TRUE | bytes[8]=0062010000000000 sec=.got near=stdout+0x28 | 0 |
| plain | 177 | got_register_frame_info | 0x22148 | TRUE | bytes[8]=0000000000000000 sec=.got near=stdout+0x30 | 0 |
| plain | 178 | got_cxa_finalize | 0x22150 | TRUE | bytes[8]=3461010000000000 sec=.got near=stdout+0x38 | 0 |
| plain | 179 | got_deregister_frame_info | 0x22158 | TRUE | bytes[8]=0000000000000000 sec=.got near=stdout+0x40 | 0 |
| plain | 180 | got_stderr | 0x22160 | TRUE | bytes[8]=1021020000000000 sec=.got near=stdout+0x48 | 0 |
| plain | 181 | got_LLVMFuzzerInitialize | 0x22168 | TRUE | bytes[8]=0000000000000000 sec=.got near=stdout+0x50 | 0 |
| plain | 182 | got_stdout | 0x22170 | TRUE | bytes[8]=1821020000000000 sec=.got near=stdout+0x58 | 0 |
| plain | 183 | got_environ | 0x22178 | TRUE | bytes[8]=6834030000000000 sec=.got near=stdout+0x60 | 0 |
| plain | 184 | got_progname_full | 0x22180 | TRUE | bytes[8]=c037050000000000 sec=.got near=stdout+0x68 | 0 |
| plain | 185 | got_progname | 0x22188 | TRUE | bytes[8]=b837050000000000 sec=.got near=stdout+0x70 | 0 |
| plain | 186 | got_init_array_end | 0x22190 | TRUE | bytes[8]=0821020000000000 sec=.got near=stdout+0x78 | 0 |
| plain | 187 | got_init_array_start | 0x22198 | TRUE | bytes[8]=0021020000000000 sec=.got near=stdout+0x80 | 0 |
| plain | 188 | got_stack_chk_guard | 0x221a0 | TRUE | bytes[8]=a837050000000000 sec=.got near=stdout+0x88 | 96 lines in 62 files |
| plain | 189 | got_fini_array_end | 0x221a8 | TRUE | bytes[8]=1021020000000000 sec=.got near=stdout+0x90 | 0 |
| plain | 190 | got_fini_array_start | 0x221b0 | TRUE | bytes[8]=0821020000000000 sec=.got near=stdout+0x98 | 0 |
| plain | 192 | (driver static cell, line 192) | 0x238a0 | FALSE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=read_stage+0x487[cli.c] | 0 |
| plain | 193 | (driver static cell, line 193) | 0x231c8 | TRUE | bytes[8]=0100000000000000 sec=.data near=<driver static>+0x0 | 0 |
| plain | 194 | (driver static cell, line 194) | 0x238b0 | FALSE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=read_stage+0x497[cli.c] | 0 |
| plain | 205 | (driver static cell, line 205) | 0x33424 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=<driver static>+0x0 | 0 |
| plain | 206 | (driver static cell, line 206) | 0x33430 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=<driver static>+0x0 | 1 lines in 1 files |
| plain | 212 | atexit_lock | 0x53584 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=lock+0x0[atexit.c] | 0 |
| plain | 213 | atexit_slot | 0x53588 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=slot+0x0[atexit.c] | 0 |
| plain | 214 | atexit_head | 0x53590 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=head+0x0[atexit.c] | 0 |
| plain | 215 | atexit_builtin | 0x53598 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=builtin+0x0[atexit.c] | 0 |
| plain | 229 | stderr_buf | 0x53c00 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=buf+0x0[stderr.c] | 0 |
| plain | 230 | stdout_buf | 0x53c08 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=buf+0x0[stdout.c] | 0 |
| ubsan | 143 | const_double_0x1p28 | 0x103a8 | FALSE | bytes[8]=693a207265616420 sec=.rodata near=$d+0x2e[fuzz_state.c] in C string @0x103a6 'cli: read error on %s\n' | 0 |
| ubsan | 144 | const_double_1_0 | 0x103b0 | FALSE | bytes[8]=6572726f72206f6e sec=.rodata near=$d+0x36[fuzz_state.c] in C string @0x103a6 'cli: read error on %s\n' | 0 |
| ubsan | 145 | const_HIGHS_0x8080808080808080 | 0x10438 | TRUE | bytes[8]=8080808080808080 sec=.rodata near=$d+0x8[floatscan.c] | 17 lines in 3 files |
| ubsan | 146 | const_double_0_5 | 0x103c0 | FALSE | bytes[8]=006e616e00626173 sec=.rodata near=$d+0x46[fuzz_state.c] in C string @0x103bd 'NAN' | 0 |
| ubsan | 147 | const_ONES_0x0101010101010100 | 0x10448 | TRUE | bytes[8]=0001010101010101 sec=.rodata near=$d+0x0[memchr.c] | 17 lines in 3 files |
| ubsan | 148 | const_double_0x1p1023 | 0x103d0 | FALSE | bytes[8]=6c693a20696e7075 sec=.rodata near=$d+0x56[fuzz_state.c] in C string @0x103cf 'cli: input shorter than header\n' | 0 |
| ubsan | 149 | const_double_1_5 | 0x103d8 | FALSE | bytes[8]=742073686f727465 sec=.rodata near=$d+0x5e[fuzz_state.c] in C string @0x103cf 'cli: input shorter than header\n' | 0 |
| ubsan | 150 | const_u64_fmt_fp_1e9_recip_misc | 0x103e0 | FALSE | bytes[8]=72207468616e2068 sec=.rodata near=$d+0x66[fuzz_state.c] in C string @0x103cf 'cli: input shorter than header\n' | 0 |
| ubsan | 151 | const_double_0x1p_969_0x1p_1022_0x1p | 0x103e8 | FALSE | bytes[8]=65616465720a005c sec=.rodata near=$d+0x6e[fuzz_state.c] in C string @0x103cf 'cli: input shorter than header\n' | 0 |
| ubsan | 152 | const_u64_0x0101010101010102 | 0x103f0 | FALSE | bytes[8]=7525303478007b00 sec=.rodata near=$d+0x76[fuzz_state.c] in C string @0x103ef '\\u%04x' | 0 |
| ubsan | 153 | const_double_0x1p120 | 0x103f8 | FALSE | bytes[8]=5c25630062797465 sec=.rodata near=$d+0x7e[fuzz_state.c] in C string @0x103f8 '\\%c' | 0 |
| ubsan | 154 | debruijn32 | 0x10564 | TRUE | bytes[32]=00011c021d0e18031e16140f191104081f1b0d17151310071a0c12060b050a09 sec=.rodata near=$d+0x0[malloc.c] | 82 lines in 56 files |
| ubsan | 155 | size_classes | 0x10584 | TRUE | bytes[96]=0100020003000400050006000700080009000a000c000f001200140019001f0024002a0032003f004800540066007f009200aa00cc00ff00240154019901ff014802aa023203 | 180 lines in 77 files |
| ubsan | 158 | jt_printf_core_1 | 0x11b40 | FALSE | bytes[16]=c1c8c9d2d3d4d5d6440e00440b000000 sec=.eh_frame near=.eh_frame+0x750 of [0x113f0,0x11d9c) (__EH_FRAME_LIST__[crtbegin.c] and __EH_FRAME_LIST_ | 0 |
| ubsan | 159 | jt_printf_core_2 | 0x11c20 | FALSE | bytes[16]=00000000380000003808000054a90000 sec=.eh_frame near=.eh_frame+0x830 of [0x113f0,0x11d9c) (__EH_FRAME_LIST__[crtbegin.c] and __EH_FRAME_LIST_ | 0 |
| ubsan | 160 | jt_pop_arg | 0x11c40 | FALSE | bytes[16]=04940595069607970898090a039805c8 sec=.eh_frame near=.eh_frame+0x850 of [0x113f0,0x11d9c) (__EH_FRAME_LIST__[crtbegin.c] and __EH_FRAME_LIST_ | 0 |
| ubsan | 173 | got_DYNAMIC | 0x22810 | TRUE | bytes[8]=0000000000000000 sec=.got near=stdout+0x10 | 0 |
| ubsan | 174 | got_main | 0x22818 | TRUE | bytes[8]=e82e010000000000 sec=.got near=stdout+0x18 | 0 |
| ubsan | 175 | got_init | 0x22820 | TRUE | bytes[8]=d060010000000000 sec=.got near=stdout+0x20 | 0 |
| ubsan | 176 | got_fini | 0x22828 | TRUE | bytes[8]=e868010000000000 sec=.got near=stdout+0x28 | 0 |
| ubsan | 177 | got_register_frame_info | 0x22830 | TRUE | bytes[8]=0000000000000000 sec=.got near=stdout+0x30 | 0 |
| ubsan | 178 | got_cxa_finalize | 0x22838 | TRUE | bytes[8]=1c68010000000000 sec=.got near=stdout+0x38 | 0 |
| ubsan | 179 | got_deregister_frame_info | 0x22840 | TRUE | bytes[8]=0000000000000000 sec=.got near=stdout+0x40 | 0 |
| ubsan | 180 | got_stderr | 0x22848 | TRUE | bytes[8]=f827020000000000 sec=.got near=stdout+0x48 | 0 |
| ubsan | 181 | got_LLVMFuzzerInitialize | 0x22850 | TRUE | bytes[8]=0000000000000000 sec=.got near=stdout+0x50 | 0 |
| ubsan | 182 | got_stdout | 0x22858 | TRUE | bytes[8]=0028020000000000 sec=.got near=stdout+0x58 | 0 |
| ubsan | 183 | got_environ | 0x22860 | TRUE | bytes[8]=583b030000000000 sec=.got near=stdout+0x60 | 0 |
| ubsan | 184 | got_progname_full | 0x22868 | TRUE | bytes[8]=b03e050000000000 sec=.got near=stdout+0x68 | 0 |
| ubsan | 185 | got_progname | 0x22870 | TRUE | bytes[8]=a83e050000000000 sec=.got near=stdout+0x70 | 0 |
| ubsan | 186 | got_init_array_end | 0x22878 | TRUE | bytes[8]=f027020000000000 sec=.got near=stdout+0x78 | 0 |
| ubsan | 187 | got_init_array_start | 0x22880 | TRUE | bytes[8]=e827020000000000 sec=.got near=stdout+0x80 | 0 |
| ubsan | 188 | got_stack_chk_guard | 0x22888 | TRUE | bytes[8]=983e050000000000 sec=.got near=stdout+0x88 | 96 lines in 62 files |
| ubsan | 189 | got_fini_array_end | 0x22890 | TRUE | bytes[8]=f827020000000000 sec=.got near=stdout+0x90 | 0 |
| ubsan | 190 | got_fini_array_start | 0x22898 | TRUE | bytes[8]=f027020000000000 sec=.got near=stdout+0x98 | 0 |
| ubsan | 192 | (driver static cell, line 192) | 0x23f90 | FALSE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=read_stage+0x487[cli.c] | 0 |
| ubsan | 193 | (driver static cell, line 193) | 0x238b0 | TRUE | bytes[8]=0100000000000000 sec=.data near=<driver static>+0x0 | 0 |
| ubsan | 194 | (driver static cell, line 194) | 0x23fa0 | FALSE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=read_stage+0x497[cli.c] | 0 |
| ubsan | 205 | (driver static cell, line 205) | 0x33b14 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=<driver static>+0x0 | 0 |
| ubsan | 206 | (driver static cell, line 206) | 0x33b20 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=<driver static>+0x0 | 1 lines in 1 files |
| ubsan | 212 | atexit_lock | 0x53c74 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=lock+0x0[atexit.c] | 0 |
| ubsan | 213 | atexit_slot | 0x53c78 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=slot+0x0[atexit.c] | 0 |
| ubsan | 214 | atexit_head | 0x53c80 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=head+0x0[atexit.c] | 0 |
| ubsan | 215 | atexit_builtin | 0x53c88 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=builtin+0x0[atexit.c] | 0 |
| ubsan | 229 | stderr_buf | 0x542f0 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=buf+0x0[stderr.c] | 0 |
| ubsan | 230 | stdout_buf | 0x542f8 | TRUE | bytes[8]=0000000000000000 sec=.bss (NOBITS, zero at load) near=buf+0x0[stdout.c] | 0 |

src0_A_start / src0_E_start and src0_A_set_thread_area / src0_E_set_thread_area (both files): size-0 cells (v6.4 `OK SIZE0`: only the A end is checked, the E end is the next function's start; start's E spans _start and _start_c), read by no file of the unit, so deleted as unread size-0 cells (deletion only, no value set); both ends were measured and correct in both images: start is the start-up region, _start to the first init function (plain 0x12d30..0x12d78, ubsan 0x12d9c..0x12de4, _start_c between), and set_thread_area runs from __set_thread_area to the next function _exit (plain 0x21050..0x2105c, ubsan 0x21738..0x21744).

The cell names of the driver-static rows, and the symbol they name, are in the internal record (the verbatim text of this file: sha256 d9ae9b4a21158b197a6ce83963260c84d9a1c2832fce45b6503cb390d9db93d4).

## 4. Final check on the series head (yh03check v6.4 fb3bfbc1eea8, `--pinned`, `--pins` harness.yaml)

- plain: rc 0; `# self-test: 223 known answers OK (yh03regen 163 + yh03check 60)`; `18 of 18 section cells equal the image's section headers`; `# rows checked: 105; rows not OK: 0`.
- ubsan: rc 0; the same self-test line; `18 of 18`; `# rows checked: 105; rows not OK: 0`.
- No line of either file holds two `_D_` definitions (`grep -cE "Definition [a-z0-9]+_D_.*Definition [a-z0-9]+_D_"` = 0, before and after).

## 5. Cross-check with a relocator sweep of the same cells

231 sweep rows name YH03 cells at 9a979984f23e: 30 it calls right (unchanged here, v6.4 OK too); of the 201 it calls wrong, 115 are removed here, 77 changed here (for the 44 rows with a numeric right value, this branch's value equals it in 44 of 44), 9 unchanged by the cell fix: str / str_2 (removed in section 6), and the FILE-sink cells read by YI5c (stdio_read, str_rwa), which the FILE-sink restatement in this series frees and removes. Cells v6.4 or the NOSYM judgment call right that the sweep calls wrong: 0.

## 6. Cells no checker row examines

Per file 37 definitions are neither a v6.4 row nor a NOSYM cell: the 18 section cells (text, rodata, eh_frame, init_array, fini_array, data_rel_ro, got, data, bss: lo / hi), examined by v6.4's section-bounds line (18 of 18); src0_debruijn_len = 32, TRUE (the length of the 32-entry ctz table src0_D_debruijn32, TRUE above); and 18 string cells, read here as the C string at the value in each pin (plain and ubsan hold the same bytes):

| cell | value | string in the pin | verdict | readers |
|---|---|---|---|---|
| str_n0X0x | 0x1029e | `-+   0X0x` | TRUE | 0 |
| str_n0X_0X_0X_0x_0x_0x | 0x102ca | `-0X+0X 0X-0x+0x 0x` | TRUE | 0 |
| str_cli_out_of_memory_n | 0x102dd | `cli: out of memory\n` | TRUE | 0 |
| str_d_n | 0x102f1 | `%d\n` | TRUE | 0 |
| str | 0x10370 | `rmat` (the tail of another string) | FALSE: the donor image holds `cli: input shorter than header\n` at this address | 0 |
| str_2 | 0x102d1 | `0X-0x+0x 0x` (the tail of another string) | FALSE: the donor image holds `.` at this address | 0 |
| str_usage_s_INPUT_n | 0x10303 | `usage: %s INPUT\n` | TRUE | 0 |
| str_cli_config_len_overruns | 0x10314 | `cli: config_len overruns input\n` | TRUE | 0 |
| str_inf / str_INF | 0x10338 / 0x10343 | `inf` / `INF` | TRUE | 0 |
| str_cli_input_u_bytes_refuse | 0x10347 | `cli: input >= %u bytes, refused\n` | TRUE | 0 |
| str_cli_cannot_open_s_n | 0x10391 | `cli: cannot open %s\n` | TRUE | 0 |
| str_cli_read_error_on_s_n | 0x103a6 | `cli: read error on %s\n` | TRUE | 0 |
| str_NAN / str_nan | 0x103bd / 0x103c1 | `NAN` / `nan` | TRUE | 0 |
| str_cli_input_shorter_than_h | 0x103cf | `cli: input shorter than header\n` | TRUE | 0 |
| str_dev_null | 0x10402 | `/dev/null` | TRUE | 0 |
| str_null | 0x1040c | `(null)` | TRUE | 0 |

str and str_2 still held the donor image's addresses (unchanged since 9a979984f23e); both are FALSE of this image and unread, so both are removed from both files (deletion only, no value set): "string cell, FALSE, 0 readers, removed". After the removal `git grep -n -w -E 'src0_D_str|src0_D_str_2' -- ':(glob)projects/omx-clap-core/fuzz_state/**/*.v'` prints nothing. The FILE-sink string cells of the shipped tree (str_wb, str_tmp_out_gif, str_3, str_rwa; they hold strings this image does not contain) were removed by the FILE-sink restatement once nothing read them.

