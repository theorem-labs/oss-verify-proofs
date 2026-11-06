# notice-claims.tsv: each donor notice of the unit, measured against the file it cites

`notice-claims.tsv` has one row for each donor notice in `proofs/lib/`: each `(* Modified by ... *)` comment that
says its file was "copied from" or "made from" another file, or that some of its lines "match lines of" one.
For each notice, the row gives what the notice claims (the kinds of change it declares, and its line counts if it
gives any), what was measured, and whether the two agree. `notice_claims.py`, in this directory, generates the
table; its docstring defines the measure and every verdict. Run it from the repository root:

```
python3 projects/libreac/fuzz_identity/proofs/provenance/evidence/notice_claims.py \
    --repo . --unit projects/libreac/fuzz_identity --rev HEAD --base 1aeda8ab8602 > notice-claims.tsv
```

`--base` is the commit this series starts from. The last two columns compare each notice with the same notice at
that commit, measured on the file as it was there. The measure gives exactly the counts of the three "made from"
notices whose files did not change after the notices were written (`lib/Reusable/YH01.v`, `YL0t.v`, `YL0v.v`).
The script reads each donor at `--rev` with `git cat-file`, so a sparse checkout is enough.

## What the table says

1645 notices. At this head:

| verdict | rows | at the base |
|---|---|---|
| agrees | 1123 | 1014 |
| agrees up to Require layout | 28 | 28 |
| counts differ | 7 | 7 |
| donor holds under half | 8 | 8 |
| omits changes | 293 | 394 |
| numerals only (not decided) | 125 | 129 |
| worded (not decided) | 61 | 42 |

At the base, 409 notices were wrong by the measure: 7 with false counts, 8 that cite a file holding less than
half of theirs, and 394 that declare fewer changes than the file has (for example a `_cf` file that renames
`SR` to `SR_cfv` but says only "with its module paths changed"). Another 129, which declare addresses, differ
from their donor only in numerals, and 42 declare their changes in words; a program does not decide these.

## Where these notices come from

Every one of the base's 1622 notices had, at the base, the same text it had when its file first came into the
repository with the unit's proofs (commit `84b1ffc6d7d` for the plain and ubsan proofs, `cffeac4df63` for the
asan and asan-ubsan proofs), except for the path layout of the donor. So the 409 defects came with the port. Up
to the base, no change was made to them. This series reworded 7 of them (the 5 in "The 7 notices this series
rewrote first" below, and `lib/Reusable/YG00.v` and `YG03.v`, whose allocator-model labels it renumbered), and in
the other 402 it changed only the donor path, to the `projects/<p>/<t>/proofs/` layout, until `notice_fix.py`
rewrote the 96 of them that are ours (next section).

Before that run, at `fc7687b9b1f7`, 406 rows were `counts differ`, `donor holds under half` or `omits changes`:
those 402, the `Modified by Rares Buhai` notices of `lib/Reusable/YL0s.v` and its `lib/U` copy (both agreed at the
base), and the 2 added notices of `lib/Reusable/YL06.v:5` and its `lib/U` copy (the section after next). 98 of the
406 are our own lines (`Modified by Theorem Labs`), and the next section says how each was made true. The other
308 are an outside contributor's lines (`Modified by Rares Buhai`), and they are the 308 wrong rows at this head
(column `changed_since_base` is `no` for each). This series does not change them: under item 17 of the OSS Verify
release's comment-pass rulings (2026-11-01), a contributor's notice line changes
only by the layout rewrite of its donor path. They are routed to the licence tool of record
(`fix/licence-of-record`), next series, per the CI/CD lead 04:44Z. This table is the record of what each of them
gets wrong.

## The 102 notices of ours, made true from their rows

`notice_fix.py`, in this directory, rewrote them. Its header states its rule. A later run of the same committed
version rewrote 2 more, `lib/Reusable/YK09.v:4` and `lib/ReusableB/YK09.v:4`, after the `ASAN` and `BOTH`
tables of those files were removed ("The ASAN and BOTH tables of YK09, removed" in `address-cell-labels.md`).
A third run wrote again only the figures of `lib/A/AB1w.v:4` and `lib/ReusableB/YB1w.v:4`, after the cell
`tfib_D_libc_progname_area_musl_bss` was removed from those files ("The cell tfib_D_libc_progname_area_musl_bss,
removed" in `address-cell-labels.md`).
A fourth run wrote the figures of the same two lines again, after the cell `tfib_D_environ_musl` was removed from
those files ("The cell tfib_D_environ_musl, removed" in `address-cell-labels.md`).
Each version of it was committed alone before the run that used it: the first (`89e0cc675420`), and the one at
this head (`c06d19b04f21`). After those runs, one line of its header was reworded to drop an internal reference
the repository lint keeps out of shipped files, so the file here is not byte-equal to the one that ran; the
change is in the header text only, and every rule, check and output of the four runs is unchanged. A reader
found that the first version copied the `categories` column into each new body, and that column only repeats what
the old notice declared. So 8 `lib/ReusableB` bodies said "module paths and addresses changed" where no address
changed, while their `lib/A` twins, with the same changes and counts, said "module paths changed". The rule now
keeps a category only when the measure needs it: a category is dropped when the measure without it gives the
row's `matched`.

The run of this version started from the state before the first run. The 98 lines were put back to their text at
`fc7687b9b1f7`, and the script read that commit's table (sha256 `9898c06fb310...`). It changed one line for each
of the 98 rows:

- 96 rows (`omits changes`, each a "copied from" notice that gives no figures) now say "made from <donor>, with its
  <categories> changed; N of its M lines of code are new or changed and K lines of the source are left out". The
  donor and the figures come from the row's columns, and the categories are those of the column that the measure
  needs. All 96 keep module paths. 57 keep addresses. 15 drop addresses, because the addresses mask (0x numerals
  only) changes none of their figures: `lib/A/AFf4.v`, `AFg0.v`, `AFg4.v`, and `lib/ReusableB/YFey.v`, `YFez.v`,
  `YFf1.v`, `YFf2.v`, `YFf3.v`, `YFf4.v`, `YFfq.v`, `YFg0.v`, `YFg4.v`, `YFhf.v`, `YFhl.v`, `YFia.v`. In 7 of these
  (`AFf4.v`, `AFg0.v`, `AFg4.v`, `YFf4.v`, `YFg0.v`, `YFg4.v`, `YFia.v`), an address written in decimal changed. A
  program cannot tell a decimal address from a count, so that line is counted among the N new or changed lines.
  Each of the 37 pairs of a `lib/A` file and its `lib/ReusableB` twin among the 96 now declares the same
  categories. The old words that are not columns (a donor image sha256, "for libreac/fuzz_identity's program
  walk", "its addresses moved to libreac/fuzz_identity's ASan build") are gone.
- 2 rows (`counts differ`, `lib/Reusable/YL06.v:5` and its `lib/U` copy) changed only their figure: 112 of the
  file's 244 lines of code match lines of cgif `YL05.v`, not 109. Their other words stay. The table does not
  measure their second clause, "82 match lines of" cgif `YL06.v`; the same measure gives 82 for that file.

Against the text of the first run, this run changed 15 lines, the 15 above, and only by dropping "and addresses".
It refused no row, changed no other line and added no line, so no line number that cites these files moves. Its
checks: each of the 98 changed lines is the line of one row, and each row has one changed line; each of the 98
files, with its comments removed, is byte-equal to the file before; each of the 669 contributor lines is
byte-equal to its line at `0a3a06762f6b`, and equals its line at the merge base `1aeda8ab8602` once the donor path
is moved to the new layout (item 17 above). The table was then generated again with the command above: each of
the 98 rows agrees.

## The 7 notices this series rewrote first, and the 23 it added

Before `notice_fix.py`, this series rewrote 7 notices and added 23. Each one agrees with the measure at this head;
the 2 added notices of `lib/Reusable/YL06.v:5` and its `lib/U` copy agree since `notice_fix.py` put the measured
112 in place of 109 (previous section). Each added notice is a `Modified by Theorem Labs` line under a
`Modified by Rares Buhai` line, which keeps its text of the base, with the donor path in the new layout:

- The series made 13 notices less true with its own changes to the code: `lib/Reusable/YH03.v` and its
  `lib/U` copy (address cells removed and renamed), `lib/Reusable/YL0s.v` and its `lib/U` copy (one cell
  renamed), `lib/A/AB1w.v` and `lib/ReusableB/YB1w.v` (address-cell labels removed, then the cells
  `tfib_D_libc_progname_area_musl_bss` and `tfib_D_environ_musl`), `lib/A/ACeg.v`,
  `lib/ReusableB/YCeg.v` and `lib/A/Prog/YC81.v` (a `timeout` tactical removed), `lib/A/AD1g.v` and
  `lib/ReusableB/YD1g.v` (a fallback tactic removed), and `lib/Reusable/YK09.v` and `lib/ReusableB/YK09.v` (the
  third image's `ASAN`/`BOTH` tables removed). Each of the 7 rewritten notices, the notice added under each of the
  4 Rares Buhai lines, and the 2 `YK09.v` notices that `notice_fix.py` rewrote (previous section) now has the
  "made from ..., N of its M lines of code are new or changed and K lines of the source are left out" form, with
  the measured counts.
- 15 notices say their file was copied from a cgif file with only its module paths changed. That is false for
  each: from 19 to 396 of the file's lines of code are new or changed. The files are `lib/Reusable/YL0i.v`,
  `YL06.v`, `YN02_cf.v`, `YN2b_cf.v`, `YP0g_cf.v`, `YO03_cf.v`, `YO0j_cf.v`, `YO0l_cf.v`, `YO0m_cf.v`, `YO0n_cf.v`,
  and the `lib/U` copies of the first five. For each of them, the released proof files of the repository that
  have its file name (with or without `_cf`), or that declare one of its declared names (with or without `cf`),
  were measured, and the commit that first added each was found. A file is the source when it holds at least
  half of the file's lines of code and was added before it. A file found by neither test was not measured.
  - For `YN2b_cf.v`, `YP0g_cf.v`, `YO0l_cf.v`, `YO0m_cf.v` and `YO0n_cf.v`, the cited cgif file is the older file
    that holds the most, and it holds at least half. The added notice says "made from" it, with the counts.
  - For `YL0i.v`, `YL06.v`, `YN02_cf.v`, `YO03_cf.v` and `YO0j_cf.v`, no measured older file holds half; the
    files that do were added with this unit or after it. The added notice says "no single donor found by
    measurement", and how many lines match the older file that holds the most. For `YL06.v` and `YO0j_cf.v` that
    is not the file the older notice cites, so the added notice names both.
- 4 notices do not name their real source: `lib/ZAllocator.v` and `lib/ZImage.v` and their `lib/U` copies are
  copies of `projects/zlib/checksum_fuzzer/proofs/lib/ZAllocator.v` and `ZImage.v`. `ZImage.v` equals the zlib
  file up to module paths, addresses and numbers; `ZAllocator.v` has 3 of its 30 lines new or changed (the
  `CallocCert` import, `Let CAL` and the `zlib_API` line) and leaves out 2 of the zlib file's lines. The notices
  added under them cite the zlib files, and the comments under those name this unit's image and certificates.

## Limits

- `numerals only`: a decimal numeral can be an address, so a notice that declares "addresses" but not "numbers"
  may be right for these rows. The table does not decide them.
- `worded`: words such as "its two allocator-model labels renumbered as the tags 1 and 2" are not checked.
- A module renamed in this unit (for example `YP0d` copied as `PaRun`) counts as a changed line, not as a changed
  module path.
- The alignment is `difflib`'s, which is not always the longest common subsequence. A different alignment can
  give other counts for the same pair of files.
- Comments that are not donor notices are not in the table. 28 such lines, base text that this series did not
  change, cite a document that is not in the repository: `CONVENTIONS` (23 lines), `idst/col/NOTES.md` (2),
  `LLVMFuzzerTestOneInput.notes.md` (1), `REPORT.md` (1), and the sha256 `82901a424bb97a7d...` of a
  `lib/B/AF0m.v` that is not in the tree (`lib/B/IdentHimgOwned.v:4`).
- 5 citations in 3 lines of `lib/A/IdentTop.v` (`:68`, `:69`, `:73`), base text that this series did not change,
  give a line of `lib/A/AF0m.v` that was already wrong at the base. Each points one or two lines above a real
  definition: `Tfib_owned_static` is at 1551, not 1549; `TFIB_ERRNO` at 24, not 23; `Tfib_zero_shadow` at 1549, not
  1547; `Tfib_const_shadow` at 833, not 831; `TfibSyms` at 1612, not 1610.
- The comparison ignores whitespace inside a line: after the masks, all whitespace is removed from each line.
