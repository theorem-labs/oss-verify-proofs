# YH03 address tables regenerated after the FILE-sink restatement (superseded: history)

SUPERSEDED. This is the record of commit 0dbfaec69fb2, an earlier commit of this branch that committed yh03regen
4e9a57e74cac's output. The branch was rewritten: one YH03 commit now sits on b5dd72116a44, with the output of yh03regen
f357a8df6e49 (v6.3). Its record is ../README.md. Below, "the committed output" and "this commit" mean 0dbfaec69fb2.
Every other file in this directory is unchanged, except that the per-row tool outputs and read-cells.tsv are now kept
outside the repository (../README.md, "Files kept outside the repository", lists each one with its sha256 and command).

lib/Reusable/YH03.v (plain image) and lib/U/Reusable/YH03.v (ubsan image) are the output of yh03regen 4e9a57e74cac,
taken byte for byte. The input was the two files at b5dd72116a44, which is the restatement commit; that commit did not
change the YH03 files. The tool is `tools/yh03check/5e92f52b8caa/yh03regen.py` of the tools registry (commit 15105b1e46cf), the newest
regen of record. yh03regen cf4d51a1ec60 (`tools/yh03check/ca63d81d7725/`) gives byte-identical output on both files.

## Commands

Run from the repository root. `<pinned>` holds the pinned images. Their sha256 equal the `builds:` pins of
projects/libreac/fuzz_boxreg/harness.yaml, which is the same file here and on ossv/recipes. `<twins>` holds their
unstripped twins. The tool proves twin = pin with `--pinned`: all 4 PT_LOADs are equal.

    yh03regen.py /dev/null proofs/libreac/fuzz_boxreg/lib/Reusable/YH03.v \
      --elf <pinned>/fuzz_boxreg.plain --syms-elf <twins>/fuzz_boxreg.plain --pinned <pinned>/fuzz_boxreg.plain \
      --zero-absent --unchecked-ok --write --report regen-4e9a57e74cac.plain.report.tsv
    yh03regen.py /dev/null proofs/libreac/fuzz_boxreg/lib/U/Reusable/YH03.v \
      --elf <pinned>/fuzz_boxreg.ubsan --syms-elf <twins>/fuzz_boxreg.ubsan --pinned <pinned>/fuzz_boxreg.ubsan \
      --zero-absent --unchecked-ok --write --report regen-4e9a57e74cac.ubsan.report.tsv

    yh03check.py (5e92f52b8caa) --pinned <pinned>/fuzz_boxreg.<side> <twins>/fuzz_boxreg.<side> <file>
    yh03check.py (ca63d81d7725) <twins>/fuzz_boxreg.<side> <file>
    yh03check.py (09f5eb289e5e) <twins>/fuzz_boxreg.<side> <file>

Each check ran on both files before the regen (b5dd72116a44) and after it (this commit).

`--zero-absent` writes 0 for a cell whose function or string the image does not have. Before the restatement, YI5c's
src0_env_addr_range bounded four such string cells into the image, and 0 would have made that lemma false. After the
restatement, src0_sink names no FILE function or string, so no lemma reads those cells.

`--unchecked-ok` accepts the three string cells that have no slug. The hand verdicts, from the bytes of `.rodata`,
are the same in both images:

- src0_D_str = 0x102cd: the start of an empty string (one 00 byte). This is right for a cell with no slug.
- src0_D_str_2 = 0x102d1: one byte into "usage: %s INPUT\n" (that string starts at 0x102d0). It is not the start of a
  string. No file reads this cell.
- src0_D_str_3 = 0x10311: five bytes into "cli: input >= %u bytes, refused\n" (that string starts at 0x1030c). It is
  not the start of a string. It was src0_sink's sk_trailer_addr before the restatement; after it, no file reads it.

The tool keeps these three cells as written. src0_D_str_2 and src0_D_str_3 are still wrong values. No file reads
either of them.

## Inputs and outputs (sha256)

| file | sha256 |
|---|---|
| yh03regen.py 4e9a57e74cac (tools/yh03check/5e92f52b8caa/) | 4e9a57e74cac7e8f807ddeb49972900d357141c9dbaba4933e5ad2b2966db2a8 |
| yh03check.py 5e92f52b8caa | 5e92f52b8caa0fcfb55a13ab18beee046fac4447e5c053bdf4215479fc6cf643 |
| yh03check.py ca63d81d7725 | ca63d81d7725a715cde6cb5101ea28f72a77f3557ad0b841673b8289d818f018 |
| yh03regen.py cf4d51a1ec60 (tools/yh03check/ca63d81d7725/) | cf4d51a1ec600156a976e31290635329b4e24e7632bd4d073b8adb29ec792d0b |
| yh03regen.py b05e25845c37 (tools/yh03check/09f5eb289e5e/) | b05e25845c37269e2f22cb04c00ee676119a0ce71fceb088e62d63ae8e980f6d |
| yh03check.py 09f5eb289e5e | 09f5eb289e5e77147af5c159c4f7ccd48dd03bff45acb958b9fcf4660c3d0ba7 |
| <pinned>/fuzz_boxreg.plain | 76a5b76842fcfa903088d14284b1d3d84d3fa4358e865ab144f74123af312e0c |
| <pinned>/fuzz_boxreg.ubsan | d63ba804708e835e57646043730f6bdd8fc3e34ba6e2204407d533a65213a34d |
| <twins>/fuzz_boxreg.plain | df5e36f7548846b54db2f80f004446f2fe8b67e22bafbd952cb597e70c84d6cb |
| <twins>/fuzz_boxreg.ubsan | cf86f9e4b963eb831bba41459bf33730253d4c6b8cb549ea8bc5ae27afdb45c3 |
| lib/Reusable/YH03.v before (b5dd72116a44) | ec58217e1a1f9213e1d80c2db2c175039584b44873c8a23868067be7229efaae |
| lib/U/Reusable/YH03.v before (b5dd72116a44) | 688ac3c7c6673e58a433fc6474b839a369634811e374c19e5627dc70798e2a4b |
| lib/Reusable/YH03.v after (this commit; also cf4d51a1ec60's output) | 2edadeece1153f899cbf07259c964852dca59c6806d3e487b580fd62a4f0b25b |
| lib/U/Reusable/YH03.v after (this commit; also cf4d51a1ec60's output) | 6b6fece0d22cc4bfd0dfdf8eb0f55f0410732759424a13e6e2130bc7a769d1bc |
| lib/Reusable/YH03.v by b05e25845c37 (not committed) | 751ba2f662d85b7a4d2b64d529b71e6ae7c39ebb3f2907d6c2c012f6623e636e |
| lib/U/Reusable/YH03.v by b05e25845c37 (not committed) | 14836b9d4891633624ce0e4d22543bfb92f66466174f8750d638150292e41ce9 |

## Results

The regen exits 0 on both files. Each file has 14 of 14 section cells equal to the image's section headers, and unit
identity is checked against the pin. The regen counts per file are: KEEP 124, KEEP-SIZE0 2, KEEP-SPAN 3, FIX 29,
ABSENT 29 (26 functions and 3 strings, each written as 0), NOSYM 46, KEEP-BY-LOAD 1 (src0_D_fe_getround),
INTERIOR-OWN 1, UNCHECKED 3. The regen changes 86 cell values in each file.

yh03check, both files, after the regen:

| check | A/E rows | not OK | A/E BAD | D cells by symbol | D by code | NOSYM |
|---|---|---|---|---|---|---|
| 5e92f52b8caa | 128 | 26, all ABSENT EMPTY | 0 | 41 OK, 0 BAD | OK-BY-LOAD 1 | 46 |
| ca63d81d7725 | 128 | 26, all ABSENT EMPTY | 0 | 41 OK, 0 BAD | OK-BY-LOAD 1 | 46 |
| 09f5eb289e5e | 128 | 26, all ABSENT EMPTY | 0 | 41 OK, 1 BAD (src0_D_fe_getround) | - | 46 |

The 26 ABSENT EMPTY rows are functions that the image does not link, such as the donor's cgif_* functions, fopen and
stdio_read. Each is now 0..0. Before the regen, all three checks reported 51 rows not OK in each file.
09f5eb289e5e's one D BAD row is its known false positive: it matches the function __fe_getround (registry note of
ca63d81d7725). The other two checks find that the code of __fe_getround forms the cell's value 0x110d0 (plain) /
0x110d8 (ubsan), so they report it OK-BY-LOAD.

### Cells that a proof reads

A cell is read when a `.v` file under proofs/libreac/fuzz_boxreg other than the two YH03.v names it. read-cells.tsv
lists each cell that is read before or after the restatement, with its values before and after the regen and the
5e92f52b8caa check verdict of its row.

- Before the restatement, 49 cells per file are read. After it, 41 are read. The restatement removed these readers:
  src0_A_stdio_read, src0_A_stdio_write, src0_A_stdio_seek, src0_A_stdio_close, src0_D_str_wb, src0_D_str_tmp_out_gif,
  src0_D_str_3 and src0_D_str_rwa (YI5c's src0_sink only).
- The 41 cells that are read after the restatement keep their values through the regen. After the regen, 0 of their
  rows is BAD in any of the three checks.
- Before the regen, the rows of five read cells were BAD: src0_A_LLVMFuzzerTestOneInput, src0_A_memchr,
  src0_A_memset, src0_A_munmap and src0_A_strnlen. Each A value was the symbol's start (symbol+0x0). Only E was wrong,
  and no file reads E.
- The wrong cells that YI5c read before the restatement: src0_A_stdio_read (ABSENT: the image has no such function;
  now 0), src0_A_stdio_seek (0x16b90 / 0x16f90, BAD; now __stdio_seek, 0x16bbc / 0x16fbc), src0_D_str_wb,
  src0_D_str_tmp_out_gif and src0_D_str_rwa (ABSENT; now 0), and src0_D_str_3 (UNCHECKED; kept, see above).

## yh03regen b05e25845c37: run, not committed

b05e25845c37 ran with the same options (except `--pinned`, which that version does not have) on copies of the same two files, and exited 0. Its output is equal to the
committed output except for one line per file (b05e25845c37-vs-4e9a57e74cac.diff):

    lib/Reusable/YH03.v    src0_D_fe_getround  b05e25845c37: 0x1aaa0   committed: 0x110d0
    lib/U/Reusable/YH03.v  src0_D_fe_getround  b05e25845c37: 0x1aea0   committed: 0x110d8

The registry marks b05e25845c37 as superseded: registry commit d96b415187e5 records ca63d81d7725 + cf4d51a1ec60 as of
record in its place, and 15105b1e46cf registers 5e92f52b8caa + 4e9a57e74cac, which supersede the later b33d74d0f5c5 /
7db890412b8a. b05e25845c37 also writes a function address into a table cell. src0_D_fe_getround is the rounding-mode
table that __fe_getround reads, and b05e25845c37 sets it to the address of __fe_getround itself. No file reads
src0_D_fe_getround.

## Files

- regen-4e9a57e74cac.{plain,ubsan}.err: the regen of record (stderr with the self-test, section bounds, identity and
  counts). Its report rows, regen-4e9a57e74cac.{plain,ubsan}.report.tsv, are kept outside the repository.
- check-<version>.{before,after}.{plain,ubsan}.err: each check's summary (stderr). Its rows (stdout),
  check-<version>.{before,after}.{plain,ubsan}.rows, are kept outside the repository.
- b05e25845c37-vs-4e9a57e74cac.diff: the superseded regen's output against the committed output. Its report rows,
  regen-b05e25845c37.{plain,ubsan}.report.tsv, are kept outside the repository.
- read-cells.tsv (kept outside the repository): the cells a proof reads, before and after.

In the .err files, each host path is replaced by `<pinned>/`, `<twins>/` or `<scratch>/`, and the repository root is
removed from paths. The files are otherwise unchanged.
