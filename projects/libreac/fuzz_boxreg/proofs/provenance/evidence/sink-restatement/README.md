# The FILE-sink restatement, ported from fuzz_decode

## Source

- Commit b49cbe64fa19f7d8b72491435bb0810d5c3ffbbd, "libreac/fuzz_decode: the FILE sink is option-typed,
  and decode has none" (a cherry-pick of 061eeaaa50d1dd93842cabfc5fd161ddba4f4988). It changes six files:
  lib/Reusable/{YI14,YI5c,YL03}.v and lib/U/Reusable/{YI14,YI5c,YL03}.v.
- Pull request #412 ("Pau proofs (libreac/fuzz_decode)", head 78320e0a354bf87c0eca8fb44b94e5a5e489d8fe,
  base fa84fc40b9f6ff78bda73d624d30730620409f22) carries the same change: its diff of these six files is
  byte-identical to the diff of b49cbe64fa19.

## The change

sink_syms keeps the stdio lock, the threaded flag and the two word constants. The FILE functions and strings move
to file_sink_syms, carried as sk_file : option file_sink_syms. stdio_env, env_addr and env_ivl state the FILE
strings only under Some F; sink_at is False under None; fopen_spec and unlink_spec quantify over F with
sk_file = Some F. fuzz_boxreg's statements and walks use no FILE sink (lib/Contract.v, lib/U/Contract.v and
lib/SlotPack.v state sink_none; no file outside YI14.v uses YI14's sink_at, fopen_spec, unlink_spec or file_at,
or a FILE field of src0_sink; lib/Reusable/YE00.v defines its own file_at over its own record), so its src0_sink
has sk_file := None, as fuzz_decode's has.

## Method

For each of the six files: base = fuzz_decode's file at b49cbe64fa19^, theirs = fuzz_decode's file at
b49cbe64fa19, both with `fuzz_decode` replaced by `fuzz_boxreg`; ours = fuzz_boxreg's file at b2e59f3b3308.
`git merge-file -p ours base theirs` merged all six with no conflict. Before the merge, base and ours were
equal in five files; in lib/Reusable/YI5c.v they differ only in fuzz_boxreg's image bounds (0x50000 and
0x32000 where fuzz_decode has 0x4f000 and 0x31000), which the change does not touch.

## Files

- mapped.patch: `git diff b49cbe64fa19^ b49cbe64fa19 -- proofs/libreac/fuzz_decode/lib`, with
  `fuzz_decode` replaced by `fuzz_boxreg`.
- 412-fuzz_decode.patch: #412's change of the six files (`git diff fa84fc40b9f6 78320e0a354b -- <six files>`).
- fuzz_boxreg.patch: the change as applied here (`git diff b2e59f3b3308 -- <six fuzz_boxreg files>`).
- diff-of-diffs.txt: `diff -u` of 412-fuzz_decode.patch and fuzz_boxreg.patch, `index` lines removed.

## Result of the diff of diffs

It shows only the unit name (the six paths, the `Require` lines in two hunk headers and context lines, and the
unit name in the src0_sink comment) and one unit value: the context line of src0_env_addr_range, whose bound is
0x50000 in fuzz_boxreg and 0x4f000 in fuzz_decode. No added or removed line differs except by the unit name.
The same diff of mapped.patch and fuzz_boxreg.patch shows only that context line.

## After the port: the form of fuzz_knock's restatement

The restatement's code has fuzz_knock's form (e4ef51a4690; also fuzz_pin's a5b1a8b6ae5).

### Code against knock and pin

YI14 / YI5c / YL03 were compared with e4ef51a4690 and a5b1a8b6ae5 in both copies, with unit names mapped and with
comments stripped. They differ only in:

- the bounds of YI5c.v (0x50000 and 0x1e000);
- two YI14.v lines that fuzz_boxreg's released file never had (`Require Import Cfg` and
  `Context {AM : AllocMode}`). b2e59f3b3308 and fuzz_decode's b49cbe64fa19 do not have them either. Neither
  restatement touches them. This is a known base difference.

### Comments

The port added four comment blocks to YI14.v / YI5c.v and reworded one comment line of YI14.v, in both copies.
b9a381e05b2c removed them by hand, as e4ef51a4690 does for fuzz_knock. 7140626464aa reverts that commit, because
lane-added or reworded comments in the copied Reusable files are removed only by the tool of record, lane-comments.
The added and reworded comment lines are therefore still in the tree, for lane-comments to remove. They are the
lines that b9a381e05b2c removes or changes.

### YH03 rows removed (yh03-rows/, then ../yh03/v64/)

The rows that a5b1a8b6ae5 removes in fuzz_pin are removed from lib/Reusable/YH03.v and lib/U/Reusable/YH03.v.
There are six lines in each file: src0_A_stdio_read / src0_E_stdio_read, src0_A_stdio_seek / src0_E_stdio_seek,
src0_D_str_wb, src0_D_str_tmp_out_gif, src0_D_str_3 and src0_D_str_rwa (old lines 85, 87, 146, 154, 155 and
164). In b2e59f3b3308, the only readers of these names were src0_sink in the two YI5c.v and its `cbv` lists
(grep-ruled-rows.b2e59f3b3308.txt). src0_E_stdio_read and src0_E_stdio_seek had no reader. Since the
restatement, src0_sink has sk_file := None and names none of them.

- grep-ruled-rows.sh REF runs `git grep -w` on each name over every .v of the unit except the two YH03.v.
  grep-ruled-rows.b9a381e05b2c.txt is its output on the tree before the removal: 0 readers for each of the eight
  names. The controls match: src0_D_ofl_lock has 6 readers, and each name has 2 matches in the two YH03.v.
- The rows are removed by hand (drop.diff), because yh03regen f357a8df6e49 cannot be limited to them. Its
  readers run on a60f6b380c99's files (`--proofs` without `--write`, ../yh03/regen-f357a8df6e49-readers.*.err)
  shows what `--proofs --write` would do. It would remove all 26 unread ABSENT A/E pairs, and stdio_read is only
  one of them. It would keep src0_A/E_stdio_seek, because the image links __stdio_seek. It would keep str_wb,
  str_tmp_out_gif and str_rwa ("known-wrong-unused", value not 0) and str_3 (UNCHECKED). The same run on the files of
  68621f8c6f97 (regen-f357a8df6e49-readers.{plain,ubsan}.err) would remove the 25 pairs that are left. Both
  runs print `# self-test: 151 known answers OK`. Commit cea4e0ec210f then removes those 25 pairs with yh03regen
  1254e5c96a44 (v6.4) `--proofs --write`, as the release owner ruled. Its record is ../yh03/v64/README.md.
- yh03check e5d7cbda4e27, run the same way as in ../yh03/. Its self-test line is
  `# self-test: 208 known answers OK (yh03regen 151 + yh03check 57)`. Each file has 126 rows. 25 rows are not OK,
  and all of them are ABSENT A/E pairs. 41 D cells are OK and 0 are BAD. There is 1 OK-GOT0 row and there are 0
  refusals (check-e5d7cbda4e27.<side>.err). In check-rows-vs-a60f6b380c99.diff, the only rows that change against
  a60f6b380c99 are the two removed A/E rows (stdio_read ABSENT, stdio_seek OK).
- `grep -cE "Definition [a-z0-9]+_D_.*Definition [a-z0-9]+_D_"` returns 0 for each file
  (check-e5d7cbda4e27.<side>.grep-two-D.txt).

Each host path in the .err files is replaced by `<pinned>/`, and the repository root is removed from paths.

The full per-row outputs are kept outside the repository. They repeat YH03 cell names that the binary scanner of
record flags in a text file, but not in a .v file. Each one is regenerated from the repository root on the YH03.v
files of 68621f8c6f97. `<side>` is plain for lib/Reusable/YH03.v and ubsan for lib/U/Reusable/YH03.v. `<pinned>`
and `<twins>` are as in ../yh03/README.md.

| file | sha256 | command |
|---|---|---|
| check-e5d7cbda4e27.plain.rows | a9bd3af389080bb1a19a69e9f68118651a33c83c1976ee24b3b032eb77ccf515 | `yh03check.py --pinned <pinned>/fuzz_boxreg.plain <twins>/fuzz_boxreg.plain proofs/libreac/fuzz_boxreg/lib/Reusable/YH03.v` (stdout) |
| check-e5d7cbda4e27.ubsan.rows | 6341160f7eb0d9b56cdffa1fa23bacbabf0f32b55629fb352a9073140a13711e | the same with ubsan and lib/U/Reusable/YH03.v |
| regen-f357a8df6e49-readers.plain.report.tsv | cd23a863d3cb8b02bc2abd87a969fdc17fa00daacea264c628ab4a72f9807f92 | `yh03regen.py /dev/null proofs/libreac/fuzz_boxreg/lib/Reusable/YH03.v --syms-elf <twins>/fuzz_boxreg.plain --pinned <pinned>/fuzz_boxreg.plain --elf <pinned>/fuzz_boxreg.plain --unchecked-ok --proofs proofs/libreac/fuzz_boxreg --report regen-f357a8df6e49-readers.plain.report.tsv` |
| regen-f357a8df6e49-readers.ubsan.report.tsv | 9d0d4aaf4e52ad17558971d7fb9fd5e12eab87cba0aa692504cddff50fb4fbf2 | the same with ubsan and lib/U/Reusable/YH03.v |

The YH03.v files of 68621f8c6f97 have these sha256: lib/Reusable/YH03.v
d1f7951b69a9f952d895d14d258032c08ddede0988e1d09f20eba9ab17bbc58e, lib/U/Reusable/YH03.v
e1457637a2023dc64a5edbad4ce15bf06a9d2a992b41dc646ba82b22f0ace0f8.

### YI5cSat.v (d6bd729122c5)

lib/Reusable/YI5cSat.v and lib/U/Reusable/YI5cSat.v use fuzz_knock's form (48e73552fe1), with three changes: the
unit name, boxreg's base (the YL0t Require block has no `Cfg`, and the section has no `AllocMode` context), and the
bound 0x50000.

### By-use call sites (CALL-SITES.md)

`call-sites.py REF > CALL-SITES.md` lists every line of a .v file of the unit that names src0_sink, sk_file, sink_at,
fopen_spec, unlink_spec, fwrite_spec, fclose_spec, stdio_env, env_addr or env_ivl (`git grep -n -w`, path-scoped to
the unit). Each line has its enclosing declaration, and comment-only lines are marked. CALL-SITES.md is its output on
d6bd729122c5. Every name except src0_sink occurs only in YI14.v, YI5c.v, YI5cSat.v, YL03.v and YL0t.v (both copies).
src0_sink is named by its consumers: the frame and slot theorems, the zlib contracts and the ASan tops' sink gates.
