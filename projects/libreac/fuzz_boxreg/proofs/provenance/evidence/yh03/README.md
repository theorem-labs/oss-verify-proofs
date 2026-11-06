# YH03 address tables: yh03regen f357a8df6e49 (v6.3)

This is the record of a60f6b380c99. Two later commits change the same files. 68621f8c6f97 removes the ruled sink
rows (../sink-restatement/README.md). The v6.4 commit removes the 25 unread ABSENT A/E pairs that this record keeps
(v64/README.md).

lib/Reusable/YH03.v (plain image) and lib/U/Reusable/YH03.v (ubsan image) are the files of b5dd72116a44 (the FILE-sink
restatement commit, which did not change them), changed in two steps:

1. One recorded line per file: src0_D_got_DYNAMIC_reserved is set to the value that the refusal line of yh03check
   e5d7cbda4e27 prints for that file's image (gotfix.plain.diff, gotfix.ubsan.diff).
2. The output of yh03regen f357a8df6e49 on those files, taken byte for byte, with no `--accept`.

The tools are the v6.3 tools of record: commit e44aee3ec337, tools/yh03/ (yh03check e5d7cbda4e27, yh03regen
f357a8df6e49, README ab534b0079e9). The same two files are at tools/yh03check/e5d7cbda4e27/ in the tools registry,
commit c10c6f6cf6e0.

The run stays inside the tools' evidence scope:

- A/E cells whose function the image links, and D cells named by a data symbol, are fixed to the symbol.
- src0_D_got_DYNAMIC_reserved is checked by the OK-GOT0 rule.
- String cells are judged by the slug rule. This needs `--pinned` and an `--elf` image whose unit identity the tool
  checks. Here `--elf` is the pinned binary itself.
- A cell with no slug is never judged.

Every cell outside that scope keeps its input value and is listed in hand-decisions.tsv for a hand decision. The
earlier yh03regen 4e9a57e74cac run (commit 0dbfaec69fb2, no longer on the branch) is kept as history in 4e9a57e74cac/.

## Step 1: src0_D_got_DYNAMIC_reserved

yh03check e5d7cbda4e27 --pinned on the input files (check-e5d7cbda4e27.before.*.err) refuses one cell per file:

    proofs/libreac/fuzz_boxreg/lib/Reusable/YH03.v:196: src0_D_got_DYNAMIC_reserved = 0x1ed90 is not OK-GOT0: the value is not .got's start (the cell is GOT[0], the word at .got's start); the pinned binary 76a5b76842fc: .got sh_addr 0x1d260, the 8 bytes there 00 00 00 00 00 00 00 00 = 0x0, OK-GOT0 wants 0 (the pinned binary has no .dynamic)
    proofs/libreac/fuzz_boxreg/lib/U/Reusable/YH03.v:196: src0_D_got_DYNAMIC_reserved = 0x1ed90 is not OK-GOT0: the value is not .got's start (the cell is GOT[0], the word at .got's start); the pinned binary d63ba804708e: .got sh_addr 0x1d660, the 8 bytes there 00 00 00 00 00 00 00 00 = 0x0, OK-GOT0 wants 0 (the pinned binary has no .dynamic)

0x1ed90 is a donor's value. It is wrong in both files. The cell is set to the `.got` sh_addr each refusal line prints:

    lib/Reusable/YH03.v:196    0x1ed90 -> 0x1d260   (plain pin 76a5b76842fc)
    lib/U/Reusable/YH03.v:196  0x1ed90 -> 0x1d660   (ubsan pin d63ba804708e)

No `.v` other than the two YH03.v names the cell (grep-changed-names.txt). After step 2, yh03regen keeps the cell
(KEEP-GOT0) and yh03check passes it (OK-GOT0). Both print the 8 bytes of GOT[0] (all 0; the pinned binaries have no
`.dynamic`).

## Step 2: commands

Run from the repository root on the files of step 1. `<pinned>` holds the pinned images. Their sha256 equal the
`builds:` pins of projects/libreac/fuzz_boxreg/harness.yaml (the same file here and on ossv/recipes). `<twins>` holds
their unstripped twins. The tools check the build (by the pin sha) and unit identity (all 4 PT_LOADs of the twin and of
the `--elf` image equal the pin's).

    yh03regen.py /dev/null proofs/libreac/fuzz_boxreg/lib/Reusable/YH03.v \
      --syms-elf <twins>/fuzz_boxreg.plain --pinned <pinned>/fuzz_boxreg.plain --elf <pinned>/fuzz_boxreg.plain \
      --unchecked-ok --write --report regen-f357a8df6e49.plain.report.tsv
    (the same for lib/U/Reusable/YH03.v with fuzz_boxreg.ubsan)

    yh03check.py (e5d7cbda4e27) --pinned <pinned>/fuzz_boxreg.<side> <twins>/fuzz_boxreg.<side> <file>
      before: on the input files (b5dd72116a44); after: on this commit's files

    grep -cE "Definition [a-z0-9]+_D_.*Definition [a-z0-9]+_D_" <file>     (beside each check: *.grep-two-D.txt)

    readers run, no --write, on this commit's files: the regen command plus --proofs proofs/libreac/fuzz_boxreg
      -> regen-f357a8df6e49-readers.<side>.*

No run uses `--accept`. `--proofs` is left out of the run of record on purpose. With it and `--write`, the tool would
remove the definitions of the 26 unread ABSENT A/E pairs (OMITTED). The tools' README says ABSENT A/E cells are not
evidence: "yh03regen omits an unread one or keeps it as written; neither is a measurement". The readers run shows
what `--proofs` would do and lists every reader.

Self-test lines (the auditor check), one per run:

- regen of record, plain and ubsan: `# self-test: 151 known answers OK`
- readers runs, plain and ubsan: `# self-test: 151 known answers OK`
- yh03check before and after, plain and ubsan: `# self-test: 208 known answers OK (yh03regen 151 + yh03check 57)`

## Inputs and outputs (sha256)

| file | sha256 |
|---|---|
| yh03regen.py f357a8df6e49 | f357a8df6e49145f3fe45a7e5ac4235dfbdef83b93414642f84b36195b03c6d6 |
| yh03check.py e5d7cbda4e27 | e5d7cbda4e27043766a3d3bb15f55f5bed0d383a8fa060bd8cc8d730d76fb919 |
| tools/yh03/README.md (e44aee3ec337) | ab534b0079e9ea3d202bee114584442303d1a35c3b636a1d2665c77077f44ec9 |
| <pinned>/fuzz_boxreg.plain | 76a5b76842fcfa903088d14284b1d3d84d3fa4358e865ab144f74123af312e0c |
| <pinned>/fuzz_boxreg.ubsan | d63ba804708e835e57646043730f6bdd8fc3e34ba6e2204407d533a65213a34d |
| <twins>/fuzz_boxreg.plain | df5e36f7548846b54db2f80f004446f2fe8b67e22bafbd952cb597e70c84d6cb |
| <twins>/fuzz_boxreg.ubsan | cf86f9e4b963eb831bba41459bf33730253d4c6b8cb549ea8bc5ae27afdb45c3 |
| lib/Reusable/YH03.v input (b5dd72116a44) | ec58217e1a1f9213e1d80c2db2c175039584b44873c8a23868067be7229efaae |
| lib/U/Reusable/YH03.v input (b5dd72116a44) | 688ac3c7c6673e58a433fc6474b839a369634811e374c19e5627dc70798e2a4b |
| lib/Reusable/YH03.v after step 1 | e63b51b5eb5bd56f2957f043d8caa74ae01623bff675ba2d76ca690c374d037c |
| lib/U/Reusable/YH03.v after step 1 | 3fa60fcd2d1e7c53b0166f76a9f56e6719bc92823c69eabbe64c69728704ef6c |
| lib/Reusable/YH03.v output (this commit) | 7b94711d7b44536c68d2fda3fb4d652cb73e85a51dd5ada54e2435b079889161 |
| lib/U/Reusable/YH03.v output (this commit) | e983ad56df86d7bef27e52dadda69885f51a9496e219658a0bd4dffadb704b4d |
| lib/Reusable/YH03.v at 0dbfaec69fb2 (4e9a57e74cac) | 2edadeece1153f899cbf07259c964852dca59c6806d3e487b580fd62a4f0b25b |
| lib/U/Reusable/YH03.v at 0dbfaec69fb2 (4e9a57e74cac) | 6b6fece0d22cc4bfd0dfdf8eb0f55f0410732759424a13e6e2130bc7a769d1bc |

## Results

Regen of record, each file: rc 0, no refusal. Section bounds 14 of 14; build plain / ubsan by the pin sha; unit
identity checked for the twin and the `--elf` image. Counts: KEEP 124, KEEP-SIZE0 2, KEEP-SPAN 3, FIX 29, ABSENT 29
(26 A/E pairs and 3 strings, kept as written), NOSYM 45, KEEP-BY-LOAD 1 (src0_D_fe_getround), KEEP-GOT0 1
(src0_D_got_DYNAMIC_reserved), INTERIOR-OWN 1, UNCHECKED 3. Against step 1, the regen changes 31 cell values (29
lines) per file: the 25 FIX A/E pairs' cells that move, and str_inf, str_INF, str_NAN and str_nan, each to its
string.

yh03check e5d7cbda4e27, each file:

| | rows checked | rows not OK | D by data symbol | OK-BY-LOAD | OK-GOT0 | NOSYM | refusals | two `_D_` definitions on one line |
|---|---|---|---|---|---|---|---|---|
| before (input) | 128 | 51 | 41 OK, 0 BAD | 1 | 0 | 45 | 1 (src0_D_got_DYNAMIC_reserved) | 0 |
| after (this commit) | 128 | 26 | 41 OK, 0 BAD | 1 | 1 | 45 | 0 | 0 |

After: the 26 rows not OK are the ABSENT A/E pairs: functions the image does not link, such as the donor's cgif_*
functions, fopen and stdio_read. They keep their input values, and no proof reads them. 0 A/E rows are BAD. The
check exits 1 for those 26 rows only, with no refusal line.

### Against 0dbfaec69fb2 (yh03regen 4e9a57e74cac)

diff-vs-0dbfaec69fb2.diff: 30 lines and 56 cells per file. They are:

- src0_D_got_DYNAMIC_reserved (step 1);
- the 55 cells 4e9a57e74cac wrote as 0 with `--zero-absent`: the 26 ABSENT A/E pairs (52 cells), src0_D_str_wb,
  src0_D_str_tmp_out_gif and src0_D_str_rwa. v6.3 never writes 0, so these are back at their input values.

Every other cell that this commit changes has the same value that 4e9a57e74cac gave it.

grep-changed-names.txt runs `git grep -w` over every `.v` under proofs/libreac/fuzz_boxreg except the two YH03.v. It
searches for each of the 87 names that differ from the input or from 0dbfaec69fb2, and finds no match for any of
them. The control, src0_A_memset, matches 2 lines. So no cell that a proof reads differs from 0dbfaec69fb2. The record
build of 0dbfaec69fb2 (CACHE=none, all 2902 files compiled, rc 0) and its Print Assumptions comparison therefore
stand for this tree.

### Cells for a hand decision (hand-decisions.tsv, 110 per file)

| category | per file | read by a .v |
|---|---|---|
| ABSENT A/E (26 pairs; v6.3 with --proofs would omit them) | 52 | no |
| string cells with no image string (known-wrong-unused): str_wb, str_tmp_out_gif, str_rwa | 3 | no |
| string cells with no slug (UNCHECKED, never judged): str, str_2, str_3 | 3 | no |
| NOSYM (no symbol of the name, not checked) | 45 | 6: const_HIGHS, const_ONES, debruijn32, size_classes, got_stack_chk_guard, and the D cell of the harness's empty aligned-copy buffer |
| E of size-0 functions (E_start, E_set_thread_area) | 2 | no |
| no tool checks them: data_rel_ro_lo/hi, bss_lo/hi, debruijn_len | 5 | no |

The readers column searches both builds' `.v` files, with the YH03.v excluded.

## Files

In the repository:

- gotfix.{plain,ubsan}.diff: step 1, one line per file.
- regen-f357a8df6e49.{plain,ubsan}.err: the regen of record (stderr: self-test, section bounds, identity, counts).
- regen-f357a8df6e49-readers.{plain,ubsan}.err: the readers run (`--proofs`, no `--write`).
- check-e5d7cbda4e27.{before,after}.{plain,ubsan}.err / .grep-two-D.txt: yh03check v6.3 (stderr) and the
  two-definitions grep, on the input and on the output.
- grep-changed-names.txt: the readers of every changed name.
- reproduce.py: regenerates every file of the table below.
- 4e9a57e74cac/: the record of the superseded 4e9a57e74cac run (commit 0dbfaec69fb2).

In the .err files, each host path is replaced by `<pinned>/`, `<twins>/` or `<scratch>/`, and the repository root is
removed from paths. The files are otherwise unchanged.

### Files kept outside the repository

These files list YH03 cell names. The binary scanner of record flags some of these names in a text file, but not in a
.v file. So the files are kept outside the repository, and this table records them. `reproduce.py <pinned> <twins>
<tools> <out>` (run from the repository root, with pyelftools) writes all 27 files. On 2026-10-30, its output was
byte-identical to each sha256 below. `<tools>/<dir>/` is tools/yh03check/<dir>/ of the tools registry.

Each tool runs from the root of a `git archive` tree of the named commit, on the repository path of the YH03.v file:
`<file>` is proofs/libreac/fuzz_boxreg/lib/Reusable/YH03.v for plain and proofs/libreac/fuzz_boxreg/lib/U/Reusable/YH03.v
for ubsan. `.rows` files are stdout.

| file | sha256 | command |
|---|---|---|
| check-e5d7cbda4e27.after.plain.rows | ae832469f4ccd44a914005cdbd85f5e7b53f36cdd4dc8f5bdeea5c4a3c991135 | tree a60f6b380c99: `e5d7cbda4e27/yh03check.py --pinned <pinned>/fuzz_boxreg.plain <twins>/fuzz_boxreg.plain <file>` |
| check-e5d7cbda4e27.after.ubsan.rows | 3337638faf2a830df1b2144d8c71d8751eef519cf514c12d9a119f0d91425ccf | tree a60f6b380c99: `e5d7cbda4e27/yh03check.py --pinned <pinned>/fuzz_boxreg.ubsan <twins>/fuzz_boxreg.ubsan <file>` |
| check-e5d7cbda4e27.before.plain.rows | f2be54add96e849ba14b6dee6342c01e19ad0ee6433be6098442517ae0689309 | tree b5dd72116a44: `e5d7cbda4e27/yh03check.py --pinned <pinned>/fuzz_boxreg.plain <twins>/fuzz_boxreg.plain <file>` |
| check-e5d7cbda4e27.before.ubsan.rows | 4c1c427b9722ee88de67693a6292e53bc5d8254cb06325576285f73afb426ce5 | tree b5dd72116a44: `e5d7cbda4e27/yh03check.py --pinned <pinned>/fuzz_boxreg.ubsan <twins>/fuzz_boxreg.ubsan <file>` |
| diff-vs-0dbfaec69fb2.diff | 7ce6a774dc97d47b3319ba38783cf37106c788988b9864cd1fba5e38a5e72615 | plain then ubsan: `diff -u --label '<tag> at 0dbfaec69fb2 (yh03regen 4e9a57e74cac)' --label '<tag> (this commit)' <0dbfaec69fb2's file> <a60f6b380c99's file>`, `<tag>` = lib/Reusable/YH03.v or lib/U/Reusable/YH03.v |
| hand-decisions.tsv | 7838b3e1ad9265003486f8baf5d4f3c9cc5a054619e4b1d31c4d654575db36d3 | derived by reproduce.py (`derived`): one row per cell that regen-f357a8df6e49-readers.{plain,ubsan}.report.tsv reports OMITTED (A and E), ABSENT, UNCHECKED, NOSYM or KEEP-SIZE0 (E), then the five cells no tool checks; value from a60f6b380c99's YH03.v; readers by `git grep -n -w <cell> a60f6b380c99` over the unit's .v files without the two YH03.v |
| regen-f357a8df6e49-readers.plain.report.tsv | 2ef651111174317e961a2935b7be6c5c650d64cfc1b4e36cfd6d3b007c8cc08b | tree a60f6b380c99 (the whole unit): `e5d7cbda4e27/yh03regen.py /dev/null <file> --syms-elf <twins>/fuzz_boxreg.plain --pinned <pinned>/fuzz_boxreg.plain --elf <pinned>/fuzz_boxreg.plain --unchecked-ok --proofs proofs/libreac/fuzz_boxreg --report regen-f357a8df6e49-readers.plain.report.tsv` |
| regen-f357a8df6e49-readers.ubsan.report.tsv | 0f444c85f0348a327a09cdeb44169184868c6dab3cf7fceffed22b3f5cfdd0ce | tree a60f6b380c99 (the whole unit): `e5d7cbda4e27/yh03regen.py /dev/null <file> --syms-elf <twins>/fuzz_boxreg.ubsan --pinned <pinned>/fuzz_boxreg.ubsan --elf <pinned>/fuzz_boxreg.ubsan --unchecked-ok --proofs proofs/libreac/fuzz_boxreg --report regen-f357a8df6e49-readers.ubsan.report.tsv` |
| regen-f357a8df6e49.plain.report.tsv | 8ed395c2052d32b377fca89603bb6457bf061383c701865fae22d6e682cdaae2 | tree b5dd72116a44 with gotfix.plain.diff applied: `e5d7cbda4e27/yh03regen.py /dev/null <file> --syms-elf <twins>/fuzz_boxreg.plain --pinned <pinned>/fuzz_boxreg.plain --elf <pinned>/fuzz_boxreg.plain --unchecked-ok --write --report regen-f357a8df6e49.plain.report.tsv` (the file it writes equals a60f6b380c99's) |
| regen-f357a8df6e49.ubsan.report.tsv | bae3ceb4b94b3649aa53b4ffd99adccc2e087de19c0874ac1f5a54fd4397b915 | tree b5dd72116a44 with gotfix.ubsan.diff applied: `e5d7cbda4e27/yh03regen.py /dev/null <file> --syms-elf <twins>/fuzz_boxreg.ubsan --pinned <pinned>/fuzz_boxreg.ubsan --elf <pinned>/fuzz_boxreg.ubsan --unchecked-ok --write --report regen-f357a8df6e49.ubsan.report.tsv` (the file it writes equals a60f6b380c99's) |
| 4e9a57e74cac/check-09f5eb289e5e.after.plain.rows | a904ab60c087214adba92384a487128f893e998117b361e8fb7444dac7793688 | tree 0dbfaec69fb2: `09f5eb289e5e/yh03check.py <twins>/fuzz_boxreg.plain <file>` |
| 4e9a57e74cac/check-09f5eb289e5e.after.ubsan.rows | 7875e0ceab5e8b913c35425bd2f037cf15bbf005c1f0e2a87d067366034a5a91 | tree 0dbfaec69fb2: `09f5eb289e5e/yh03check.py <twins>/fuzz_boxreg.ubsan <file>` |
| 4e9a57e74cac/check-09f5eb289e5e.before.plain.rows | a940684aaf6fbba77eb943a6980161346c68e95c779c71d71baac2e7fe39e2ac | tree b5dd72116a44: `09f5eb289e5e/yh03check.py <twins>/fuzz_boxreg.plain <file>` |
| 4e9a57e74cac/check-09f5eb289e5e.before.ubsan.rows | 5cc7731d6a630575578744a1e10fd19ade7c0e472704b33d69bfde2a7826f44e | tree b5dd72116a44: `09f5eb289e5e/yh03check.py <twins>/fuzz_boxreg.ubsan <file>` |
| 4e9a57e74cac/check-5e92f52b8caa.after.plain.rows | c68670bd882ca034ad818f359b5411a931d5cb1299a36d259e0a1b82bc9ed583 | tree 0dbfaec69fb2: `5e92f52b8caa/yh03check.py --pinned <pinned>/fuzz_boxreg.plain <twins>/fuzz_boxreg.plain <file>` |
| 4e9a57e74cac/check-5e92f52b8caa.after.ubsan.rows | 5e6b4d6f6d78d7a5000c0c25861f3c21734e6a09154fa9c5e26d6086095edd4c | tree 0dbfaec69fb2: `5e92f52b8caa/yh03check.py --pinned <pinned>/fuzz_boxreg.ubsan <twins>/fuzz_boxreg.ubsan <file>` |
| 4e9a57e74cac/check-5e92f52b8caa.before.plain.rows | e7193c032b18bdafa837eef007af20a9caf355d07094c4b0da4ec61ae6128e04 | tree b5dd72116a44: `5e92f52b8caa/yh03check.py --pinned <pinned>/fuzz_boxreg.plain <twins>/fuzz_boxreg.plain <file>` |
| 4e9a57e74cac/check-5e92f52b8caa.before.ubsan.rows | c458181c6a9378171045dcc290b75bbde5b1340803af85aa1e2dbb63bae42fd7 | tree b5dd72116a44: `5e92f52b8caa/yh03check.py --pinned <pinned>/fuzz_boxreg.ubsan <twins>/fuzz_boxreg.ubsan <file>` |
| 4e9a57e74cac/check-ca63d81d7725.after.plain.rows | c68670bd882ca034ad818f359b5411a931d5cb1299a36d259e0a1b82bc9ed583 | tree 0dbfaec69fb2: `ca63d81d7725/yh03check.py <twins>/fuzz_boxreg.plain <file>` |
| 4e9a57e74cac/check-ca63d81d7725.after.ubsan.rows | 5e6b4d6f6d78d7a5000c0c25861f3c21734e6a09154fa9c5e26d6086095edd4c | tree 0dbfaec69fb2: `ca63d81d7725/yh03check.py <twins>/fuzz_boxreg.ubsan <file>` |
| 4e9a57e74cac/check-ca63d81d7725.before.plain.rows | e7193c032b18bdafa837eef007af20a9caf355d07094c4b0da4ec61ae6128e04 | tree b5dd72116a44: `ca63d81d7725/yh03check.py <twins>/fuzz_boxreg.plain <file>` |
| 4e9a57e74cac/check-ca63d81d7725.before.ubsan.rows | c458181c6a9378171045dcc290b75bbde5b1340803af85aa1e2dbb63bae42fd7 | tree b5dd72116a44: `ca63d81d7725/yh03check.py <twins>/fuzz_boxreg.ubsan <file>` |
| 4e9a57e74cac/read-cells.tsv | 42e02435bcd063758beeada547981d7e3f54453d4276f69d0ea1c66ea19a5ca9 | derived by reproduce.py (`derived`): the cells of YH03.v (the first definition on each line) that a .v other than the two YH03.v names, at b2e59f3b3308 (before the port) and b5dd72116a44 (after); values at b5dd72116a44 and 0dbfaec69fb2; verdicts from 4e9a57e74cac/check-5e92f52b8caa.{before,after}.<side>.rows and regen-4e9a57e74cac.<side>.report.tsv |
| 4e9a57e74cac/regen-4e9a57e74cac.plain.report.tsv | d7ea03c2f9503ce25fdb8404fec11139fdfdce267fe7212ca2ca26dc777bb1a0 | tree b5dd72116a44: `5e92f52b8caa/yh03regen.py /dev/null <file> --elf <pinned>/fuzz_boxreg.plain --syms-elf <twins>/fuzz_boxreg.plain --pinned <pinned>/fuzz_boxreg.plain --zero-absent --unchecked-ok --write --report regen-4e9a57e74cac.plain.report.tsv` |
| 4e9a57e74cac/regen-4e9a57e74cac.ubsan.report.tsv | 3d5b54121448385e692503fbb375432081e618d9170243733f55cdcc43047208 | tree b5dd72116a44: `5e92f52b8caa/yh03regen.py /dev/null <file> --elf <pinned>/fuzz_boxreg.ubsan --syms-elf <twins>/fuzz_boxreg.ubsan --pinned <pinned>/fuzz_boxreg.ubsan --zero-absent --unchecked-ok --write --report regen-4e9a57e74cac.ubsan.report.tsv` |
| 4e9a57e74cac/regen-b05e25845c37.plain.report.tsv | 56ad26af4061e5b4dd374b2cd380937f4ba05b55ac2b7df778947ec93ca1ffc0 | tree b5dd72116a44: `09f5eb289e5e/yh03regen.py /dev/null <file> --elf <pinned>/fuzz_boxreg.plain --syms-elf <twins>/fuzz_boxreg.plain --zero-absent --unchecked-ok --write --report regen-b05e25845c37.plain.report.tsv` (this version has no --pinned) |
| 4e9a57e74cac/regen-b05e25845c37.ubsan.report.tsv | 2cf6251a8307236ec4975f8d4660dd60ac55beb1a4a932fb69201b332362eebb | tree b5dd72116a44: `09f5eb289e5e/yh03regen.py /dev/null <file> --elf <pinned>/fuzz_boxreg.ubsan --syms-elf <twins>/fuzz_boxreg.ubsan --zero-absent --unchecked-ok --write --report regen-b05e25845c37.ubsan.report.tsv` (this version has no --pinned) |

## Cell-parse coverage (2026-10-31)

An independent cell-parse count, 2026-10-31, read the unit's two YH03 address tables at this series. It counted every
declaration with comments removed (any keyword, any layout) and applied the tools' own regexes to the raw text. Per
table, declarations : one-line cells : tool read : not read:
- lib/Reusable/YH03.v: 307 : 305 : 305 : 2 (read by yh03check: 99 A/E rows, 198 cells, + 89 D + 18 section);
- lib/U/Reusable/YH03.v: 307 : 305 : 305 : 2 (the same).

Every declaration is a one-line `Definition` with no comment before its name, so no cell is skipped in silence: no
cell has a hidden shape (no Example, Let, Fact or Lemma ... Defined, no cell split over lines), and the tools read no
name from inside a comment.

The 2 definitions not read as cells, in each table (yh03check names both as not checked by any rule):
- src0_vmlock := None: TRUE. Readers: YH02.v:24 (a constructor argument), YV00.v, and the `src0_vmlock = Some v ->
  ...` hypotheses of YN0g, YN0h, YN0k, YN0l, YN0m, YN0n, YN0o and YN1f (each also as `_cf`), in both builds; with None
  they are vacuous. The pinned images hold no vmlock object, and __vm_wait is a 4-byte `ret` (word 0x00008067).
- src0_debruijn_len: 0 readers (YH02.v passes the literal 32, not the name). In lib/Reusable/YH03.v it is 32, TRUE: the
  table at 0x103f4 in the plain pin 76a5b76842fc is a 32-byte permutation of 0..31. In lib/U/Reusable/YH03.v it is 33,
  FALSE: the table at 0x103f9 in the ubsan pin d63ba804708e is the same 32-byte permutation, and byte 32 there (0) is
  not part of it (both measured again here).

Removal list, next series:
- lib/U/Reusable/YH03.v src0_debruijn_len := 33 — FALSE (the table at 0x103f9 is 32 bytes), unread; removed in the next series
