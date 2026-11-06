# YH03 address tables: yh03regen 1254e5c96a44 (v6.4), unread ABSENT cells removed

lib/Reusable/YH03.v (plain image) and lib/U/Reusable/YH03.v (ubsan image) are the output of yh03regen 1254e5c96a44,
run with `--proofs` and `--write`, taken byte for byte. The input was the two files of 7d9c0d2c1994; they are the files
of 68621f8c6f97, the commit that removed the ruled sink rows. No run uses `--accept`.

The run removes the 25 ABSENT A/E pairs: functions that the image does not link, and that no proof reads. Each pair
is one line, so the run removes 25 lines and 50 definitions per file and changes no other line. The ruling is the
release owner's (18:55Z), now in the series method: a cell that names a function the image does not link states
something false about the image, so an unread one is removed. The v6.3 record in ../README.md kept these cells
because the tools' README lists them as not evidence. The v6.4 README keeps that line under "NOT evidence":
"ABSENT A/E cells (stdio_read, strchr and others: yh03regen omits an unread one or keeps it as written; neither is a
measurement)". Removing them makes no claim about them.

## Tools

The v6.4 tools of record are yh03check fb3bfbc1eea8, yh03regen 1254e5c96a44 and README 7ae43e12f2bc. They are in
tools/yh03/ at commit 92c1ee13fc1a, which is one commit on top of v6.3 e44aee3ec337. v6.4 refuses a line that holds
more than one cell. It checks all 18 section-bound cells. It lists the definitions that no rule checks.

## Commands

Run from the root of a `git archive` tree of 7d9c0d2c1994 (proofs/libreac/fuzz_boxreg and
projects/libreac/fuzz_boxreg). `<pinned>` and `<twins>` are as in ../README.md. `<side>` is plain for
lib/Reusable/YH03.v and ubsan for lib/U/Reusable/YH03.v.

    yh03regen.py /dev/null <file> --syms-elf <twins>/fuzz_boxreg.<side> --pinned <pinned>/fuzz_boxreg.<side> \
      --elf <pinned>/fuzz_boxreg.<side> --unchecked-ok --proofs proofs/libreac/fuzz_boxreg --write \
      --report regen-1254e5c96a44.<side>.report.tsv
    yh03check.py --pinned <pinned>/fuzz_boxreg.<side> <twins>/fuzz_boxreg.<side> <file>     (on the written file)
    grep -cE "Definition [a-z0-9]+_D_.*Definition [a-z0-9]+_D_" <file>
    sh grep-readers.sh 7d9c0d2c1994 <the 50 names>                (grep-absent-readers.7d9c0d2c1994.txt)
    sh grep-readers.sh 7d9c0d2c1994 src0_debruijn_len src0_vmlock (grep-unchecked-readers.7d9c0d2c1994.txt)
    measure-vmlock.py <twins>/fuzz_boxreg.plain <twins>/fuzz_boxreg.ubsan   (measure-vmlock.out)

## Self-test lines

- yh03regen, both files: `# self-test: 163 known answers OK`
- yh03check, both files: `# self-test: 223 known answers OK (yh03regen 163 + yh03check 60)`

## Results

yh03regen, each file (regen-1254e5c96a44.<side>.err), rc 0, no refusal:

- 18 of 18 section cells equal the image's section headers.
- The build is identified by the pin sha, and unit identity is checked for the twin and the `--elf` image.
- `# OMITTED: 25 of the 25 ABSENT cell(s)`. The output lists the 25 names.
- Counts: KEEP 152, KEEP-SIZE0 2, KEEP-SPAN 3, OMITTED 25, NOSYM 45, KEEP-BY-LOAD 1, KEEP-GOT0 1, INTERIOR-OWN 1,
  UNCHECKED 2 (str and str_2, no reader).

yh03check on the written files, each file (check-fb3bfbc1eea8.<side>.err), rc 0:

- 101 rows checked, 0 rows not OK.
- D cells by symbol: 41 OK, 0 BAD. OK-BY-LOAD 1. OK-GOT0 1: src0_D_got_DYNAMIC_reserved is 0x1d260 (plain) and
  0x1d660 (ubsan). NOSYM 45. No refusal.

The two-definitions grep returns 0 for each file (grep-two-D.<side>.txt).

The diff (drop-absent.git.diff, `git diff -U0`; drop-absent.<side>.diff, `diff` of input and output) removes 25 lines per file
and adds none. A script checked that each removed line is `Definition src0_A_<X> ... Definition src0_E_<X> ...` for
one X of the list below, that the 25 X are exactly the 25 names the regen lists, and that the kept lines are the
input's other lines in the same order.

Output sha256: lib/Reusable/YH03.v d51a3c28ca7e384b7f761630a64142cc812400d17f2049ba9960aeddbfac2371,
lib/U/Reusable/YH03.v 2e477a2c57370841d3a22c727ca969816c1bcebbb454a0a75b65ce32267ac220. Input sha256 (7d9c0d2c1994):
d1f7951b69a9f952d895d14d258032c08ddede0988e1d09f20eba9ab17bbc58e and
e1457637a2023dc64a5edbad4ce15bf06a9d2a992b41dc646ba82b22f0ace0f8.

## The 25 removed pairs: ABSENT, 0 readers, removed

Each of these is ABSENT, has 0 readers, and is removed, in both files: LZW_GenerateStream, cgif_addframe, cgif_close,
cgif_newgif, cgif_raw_addframe, cgif_raw_close, cgif_raw_newgif, cgif_writecb, cmpPixel, create_byte_list,
create_byte_list_block, fclose, fdopen, flushFrame, fmodeflags, fopen, freeCGIF, freeFrame, ofl_add,
read_frameconfig, strchr, strchrnul, strlen, unlink, unlist_locked_file. For each X, both src0_A_X and src0_E_X go.

The readers come from `git grep -w` over every .v of the unit except the two YH03.v, on 7d9c0d2c1994
(grep-absent-readers.7d9c0d2c1994.txt). Each of the 50 names has 0 readers. Controls: src0_D_ofl_lock has 6 readers,
and src0_A_LZW_GenerateStream has 2 matches in the two YH03.v. yh03regen `--proofs` agrees ("OMITTED" only when no .v
of the file's build reads the cell). No proof names a removed cell, so no proof file changes.

## Definitions no rule checks

Both tools print `# not checked by any rule: <file>: src0_debruijn_len, src0_vmlock` for each file. Each name is
checked by hand (release owner, 18:5xZ) and again here:

- src0_debruijn_len: not checked by v6.4, and 0 readers. git grep -w over the unit finds only the two YH03.v
  definitions (grep-unchecked-readers.7d9c0d2c1994.txt: 0 readers outside YH03.v; 2 matches in the two YH03.v).
- src0_vmlock: read, and its value None is right. Its readers (60 lines, both copies) are YH02.v:24 (the ms_vmlock
  field of src0_msyms), YV00.v, and the Hvml hypotheses of YN0g / YN0h and their _cf twins. In both images,
  musl's __vm_wait is `dummy`. The symbols __vm_wait and dummy are both at 0x15ff4 (plain) and 0x163f4 (ubsan), with
  size 4 and the bytes 67 80 00 00 (`jalr zero,0(ra)`, a bare return). No symbol name holds "vmlock". So the routine
  reads no lock word, and YV00.v's comment says Some v is only for the real routine. Measured from the unstripped
  twins' .symtab and bytes by measure-vmlock.py (measure-vmlock.out).

## Files kept outside the repository

These files repeat YH03 cell names that the binary scanner of record flags in a text file, but not in a .v file. Each
is written by the command above, on the tree named there.

| file | sha256 | command |
|---|---|---|
| check-fb3bfbc1eea8.plain.rows | 431a2aabac613595cd1fbf01ca020974b13610e6841c43981e6c35223507a7e6 | yh03check above, plain, on the written file (stdout) |
| check-fb3bfbc1eea8.ubsan.rows | 006b3ef1700eb63158444fb5c1a6b675b00e39ae50ee477f2bf2f38a37aa5f83 | yh03check above, ubsan, on the written file (stdout) |
| regen-1254e5c96a44.plain.report.tsv | cd23a863d3cb8b02bc2abd87a969fdc17fa00daacea264c628ab4a72f9807f92 | yh03regen above, plain (`--report`) |
| regen-1254e5c96a44.ubsan.report.tsv | 9d0d4aaf4e52ad17558971d7fb9fd5e12eab87cba0aa692504cddff50fb4fbf2 | yh03regen above, ubsan (`--report`) |
| check-fb3bfbc1eea8.final.plain.rows | e34768d413a14c6ce72fc95f50ad1efbd93a71adfcccecc80d0ebc137b37c466 | yh03check above, plain, on the files after the NOSYM removal (stdout) |
| check-fb3bfbc1eea8.final.ubsan.rows | 7b01c708c8910d6c95e1ff79a794495303910ba96a13e9dcdba9dc88940eff23 | yh03check above, ubsan, on the files after the NOSYM removal (stdout) |
| regen-1254e5c96a44.final.plain.report.tsv | 7da57654597c267a39b4b8ac85446dec0aab4e81bc34f2ef71040b5cc66c2a38 | yh03regen above without `--write`, plain, after the NOSYM removal |
| regen-1254e5c96a44.final.ubsan.report.tsv | 86e40bff71fee93433cb32e9cbf78ee793d22f6673787767bf258c2c1febc56c | yh03regen above without `--write`, ubsan, after the NOSYM removal |

In the .err files, each host path is replaced by `<pinned>/`, and the scratch tree's root is removed from paths.

## NOSYM D cells judged against the pins; the FALSE ones removed

v6.4 does not judge a D cell that no symbol names (NOSYM, 45 per file). By the release owner's ruling (19:53Z), each one is read
against the unit's pins: a constant's bytes against the constant its name encodes, a string cell's bytes, and a jump
table, .got slot or harness cell against the object it names. A FALSE cell with 0 readers is removed. A TRUE cell
stays. No value is set by hand.

nosym-judge.py does this, with the rule for each kind of name in its docstring. It reads bytes from the pinned binary
through its PT_LOAD headers and symbols from the unstripped twin. It takes readers from `git grep -w` over the unit's
.v files except the two YH03.v. It ran on the files of cea4e0ec210f (the output of the v6.4 run above), with the
yh03check rows of that run:

    nosym-judge.py <side> <file> <pinned>/fuzz_boxreg.<side> <twins>/fuzz_boxreg.<side> \
      check-fb3bfbc1eea8.<side>.rows HEAD          -> nosym-table.<side>.tsv

nosym-table.{plain,ubsan}.tsv list every NOSYM cell: its YH03.v line, cell, value, measured bytes or object, verdict,
rule and readers. A cell of the harness prefix is shown as src0_D_<p>_<X>, and its line names it. The result is the
same in both files: 31 TRUE (6 of them read) and 14 FALSE (0 of them read).

### FALSE, 0 readers, removed (14 per file)

Each row below is recorded as "NOSYM, FALSE (value, why), 0 readers, removed". The line is the line in the files of
cea4e0ec210f.

| file | line | cell | value | measured | why FALSE |
|---|---|---|---|---|---|
| plain | 136 | src0_D_const_double_0x1p28 | 0x103a8 | 20 62 6c 6f 63 6b 20 64 = 2.0305190335991665e+174 | wants the double 268435456.0 |
| plain | 137 | src0_D_const_double_1_0 | 0x103b0 | 6f 65 73 20 6e 6f 74 20 = 2.4386118008599217e-152 | wants the double 1.0 |
| plain | 139 | src0_D_const_double_0_5 | 0x103c0 | 31 33 31 30 37 32 2d 62 = 8.406462893055637e+164 | wants the double 0.5 |
| plain | 141 | src0_D_const_double_0x1p1023 | 0x103d0 | 74 69 6e 5f 74 6c 73 20 = 2.3178912835471016e-152 | wants the double 8.98846567431158e+307 |
| plain | 142 | src0_D_const_double_1_5 | 0x103d8 | 62 75 66 66 65 72 3b 20 = 2.0470803195151433e-153 | wants the double 1.5 |
| plain | 143 | src0_D_const_u64_fmt_fp_1e9_recip_misc | 0x103e0 | 72 65 66 75 73 69 6e 67 | no number in the name: TRUE only when code forms the value |
| plain | 144 | src0_D_const_double_0x1p_969_0x1p_1022_0x1p | 0x103e8 | 20 74 6f 20 6d 61 70 20 = 1.9547501249297973e-152 | wants the double 2.004168360008973e-292 |
| plain | 145 | src0_D_const_u64_0x0101010101010102 | 0x103f0 | 69 74 0a 00 00 01 1c 02 = 0x021c0100000a7469 | wants the u64 0x0101010101010102 |
| plain | 146 | src0_D_const_double_0x1p120 | 0x103f8 | 1d 0e 18 03 1e 16 14 0f = 4.935434773486494e-236 | wants the double 1.329227995784916e+36 |
| plain | 151 | src0_D_jt_printf_core_1 | 0x11b40 | value in (no section); .rodata addresses printf_core forms by auipc + addi: 0x10298, 0x1038b, 0x104a8, 0x10588, 0x10640, 0x10691, 0x10810 | wants a jump table that printf_core forms |
| plain | 152 | src0_D_jt_printf_core_2 | 0x11c20 | value in (no section); .rodata addresses printf_core forms by auipc + addi: 0x10298, 0x1038b, 0x104a8, 0x10588, 0x10640, 0x10691, 0x10810 | wants a jump table that printf_core forms |
| plain | 153 | src0_D_jt_pop_arg | 0x11c40 | value in (no section); .rodata addresses pop_arg forms by auipc + addi: 0x105a8 | wants a jump table that pop_arg forms |
| plain | 185 | src0_D_<p>_arg0 | 0x1e9e0 | oft_arg0 at 0x1e300 size 5; the value is in read_stage+0x487 | wants the harness object oft_arg0 |
| plain | 187 | src0_D_<p>_argv | 0x1e9f0 | oft_argv at 0x1e310 size 16; the value is in read_stage+0x497 | wants the harness object oft_argv |
| ubsan | 136 | src0_D_const_double_0x1p28 | 0x103a8 | 63 20 54 4c 53 20 62 6c = 1.220437107212923e+214 | wants the double 268435456.0 |
| ubsan | 137 | src0_D_const_double_1_0 | 0x103b0 | 6f 63 6b 20 64 6f 65 73 = 7.4936326522669e+247 | wants the double 1.0 |
| ubsan | 139 | src0_D_const_double_0_5 | 0x103c0 | 20 74 68 65 20 31 33 31 = 1.0862230782858597e-71 | wants the double 0.5 |
| ubsan | 141 | src0_D_const_double_0x1p1023 | 0x103d0 | 20 62 75 69 6c 74 69 6e = 7.360988352059416e+223 | wants the double 8.98846567431158e+307 |
| ubsan | 142 | src0_D_const_double_1_5 | 0x103d8 | 5f 74 6c 73 20 62 75 66 = 3.634395875477088e+185 | wants the double 1.5 |
| ubsan | 143 | src0_D_const_u64_fmt_fp_1e9_recip_misc | 0x103e0 | 66 65 72 3b 20 72 65 66 | no number in the name: TRUE only when code forms the value |
| ubsan | 144 | src0_D_const_double_0x1p_969_0x1p_1022_0x1p | 0x103e8 | 75 73 69 6e 67 20 74 6f = 7.628632042973205e+228 | wants the double 2.004168360008973e-292 |
| ubsan | 145 | src0_D_const_u64_0x0101010101010102 | 0x103f0 | 20 6d 61 70 20 69 74 0a = 0x0a74692070616d20 | wants the u64 0x0101010101010102 |
| ubsan | 146 | src0_D_const_double_0x1p120 | 0x103f8 | 00 00 01 1c 02 1d 0e 18 = 8.250330240033663e-193 | wants the double 1.329227995784916e+36 |
| ubsan | 151 | src0_D_jt_printf_core_1 | 0x11b40 | value in (no section); .rodata addresses printf_core forms by auipc + addi: 0x10298, 0x1038b, 0x104b0, 0x10590, 0x10648, 0x10818, 0x10a91 | wants a jump table that printf_core forms |
| ubsan | 152 | src0_D_jt_printf_core_2 | 0x11c20 | value in (no section); .rodata addresses printf_core forms by auipc + addi: 0x10298, 0x1038b, 0x104b0, 0x10590, 0x10648, 0x10818, 0x10a91 | wants a jump table that printf_core forms |
| ubsan | 153 | src0_D_jt_pop_arg | 0x11c40 | value in (no section); .rodata addresses pop_arg forms by auipc + addi: 0x105b0 | wants a jump table that pop_arg forms |
| ubsan | 185 | src0_D_<p>_arg0 | 0x1ede0 | oft_arg0 at 0x1e700 size 5; the value is in read_stage+0x487 | wants the harness object oft_arg0 |
| ubsan | 187 | src0_D_<p>_argv | 0x1edf0 | oft_argv at 0x1e710 size 16; the value is in read_stage+0x497 | wants the harness object oft_argv |

The constant cells point into the text of a .rodata error message, or into the de Bruijn table after it. No
instruction pair of .text forms their addresses. The jump-table cells point past .rodata, into no section; the real
tables that printf_core and pop_arg form are listed. The two harness argument cells point into read_stage, and the
real oft_arg0 / oft_argv are elsewhere. These are the 14 cells of the FALSE class known from units moved from
fuzz_knock. The 14 lines are removed from each file. A script checked, before the removal, that each line is one
definition with the table's value. No other line changes.

### TRUE, kept (31 per file)

- const_HIGHS_0x8080808080808080 and const_ONES_0x0101010101010100: the bytes are those u64 values, and memchr forms
  the addresses. Read (YI5c.v's sk_highs_addr / sk_ones_addr).
- debruijn32: the 32 bytes are the de Bruijn bit-position table of the multiplier 0x077cb531. __libc_malloc_impl and
  alloc_slot form the address exactly. Read (YH02.v).
- size_classes: __malloc_size_classes. Read (YH02.v).
- got_* (18 cells): each .got slot holds the address of the object it names: main, _init, _fini, __cxa_finalize,
  stderr, stdout, __environ, __progname_full, __progname, __init_array_start / _end, __fini_array_start / _end and
  __stack_chk_guard (read: YH02.v). Four slots hold 0: got_DYNAMIC, got_register_frame_info,
  got_deregister_frame_info and got_LLVMFuzzerInitialize. The objects they name are undefined (_DYNAMIC) or undefined
  weak, so 0 is their address. These four are TRUE by their bytes only, because their bytes cannot tell one slot that
  holds 0 from another. None of the four is read.
- The harness cells <p>_argc, <p>_in_callback and <p>_aligned_copy_empty: oft_argc, oft_in_callback and
  oft_aligned_copy.empty are at the values. <p>_aligned_copy_empty is read (YL0s.v).
- atexit_lock / _slot / _head / _builtin: atexit.c's lock, slot, head and builtin are at the values.
- stderr_buf / stdout_buf: stderr.c's and stdout.c's buf are at the values, and __stderr_FILE.buf / __stdout_FILE.buf
  are value + 8 (musl: .buf = buf + UNGET).

### After the removal

The final runs use the files of this commit, copied into a `git archive` tree of 79d6a43ce879:

- yh03check fb3bfbc1eea8 (check-fb3bfbc1eea8.final.<side>.err): `# self-test: 223 known answers OK (yh03regen 163 +
  yh03check 60)`. 18 of 18 section cells. 101 rows, 0 not OK. D 41 OK / 0 BAD. OK-GOT0 1. NOSYM 31. No refusal. rc 0.
- yh03regen 1254e5c96a44 with `--proofs`, no `--write` (regen-1254e5c96a44.final.<side>.err): `# self-test: 163 known
  answers OK`. rc 0. No OMITTED and no refusal. The file is unchanged.
- The two-definitions grep gives 0 in both files.

Pins of every v6.4 run in this directory: the plain file was checked against <pinned>/fuzz_boxreg.plain, sha256
76a5b76842fcfa903088d14284b1d3d84d3fa4358e865ab144f74123af312e0c, with the twin df5e36f7548846b54db2f80f004446f2fe8b67e22bafbd952cb597e70c84d6cb.
The ubsan file was checked against <pinned>/fuzz_boxreg.ubsan, sha256
d63ba804708e835e57646043730f6bdd8fc3e34ba6e2204407d533a65213a34d, with the twin
cf86f9e4b963eb831bba41459bf33730253d4c6b8cb549ea8bc5ae27afdb45c3. Each .err file prints the pin sha it used.

Output sha256 after the removal: lib/Reusable/YH03.v d33df822f46eae483aebaf28ced8c6cd561937629c3b5b64ea0f37e9cd7d0cbe,
lib/U/Reusable/YH03.v 14dbf8e63a5eb29243f06eb69465c33329a055c5257b723e22038d93a4d4ee45.
