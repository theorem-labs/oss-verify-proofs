# provenance/evidence/alloc-B-recheck: the image-B Allocate comparison, re-certified on cmpkit 86da41d3ef68

Provenance only: no file here proves a function. This slice is a measurement record.

## What it re-certifies

The shipped record `provenance/evidence/kit-rerun/B/fncmp.cmpkit-4bbd3a74be89.log` (sha256 2fce19debbe3), with its
settled rows `provenance/evidence/kit-rerun/cmpkit-4bbd3a74be89/settled.tsv` (sha256 41d7ccff1f7f), makes the image-B
Allocate comparison. The relocation of the closed primary-size Allocate pairs 8 functions between
cgif_file_fuzzer.asan-ubsan ("cgif B") and fuzz_decode.asan-ubsan ("decode B"). That record finds the 8 pairs to be the
same code, with one kit difference: Allocator::Allocate +0xdc, which settled.tsv settles as a bounded 64-byte table.
That record ran on the old kit, cmpkit 4bbd3a74be89.

`fncmp-cmpkit-86da41d3ef68/` is a byte copy of the record that runs the same comparison on cmpkit 86da41d3ef68, over
the 8 functions and their whole call closure. Its own text is `fncmp-cmpkit-86da41d3ef68/RECORD.md` (sha256
b026e89a7f93) and its review is `fncmp-cmpkit-86da41d3ef68/REVIEW.md` (sha256 a6caa2397dd4). For this claim, it
supersedes the old-kit record `provenance/evidence/kit-rerun/B/fncmp.cmpkit-4bbd3a74be89.log` as the kit-of-record
measurement. The old-kit files stay unchanged, because `tools/rerun8cmp.py` reads them as its input.

## The kit verdict

On cmpkit 86da41d3ef68 (strictcmp3, `out/strictcmp3-cmp.out`), the 8 claim functions are unchanged. Every field of
every row is the same as in the old-kit run, except one verdict word: strictcmp3 prints Allocate's row as
DIFFERENT-target where strictcmp2 printed EQUAL-mod-pcrel, for the same +0xdc difference. Against the old-kit record's
T:E rows (the same image pair as this record's C:D), `out/rerun8cmp.out` finds 0 disagreements. It finds 2 on S:E:
PoisonShadow's .got TLS cell, a difference in the input only. Allocator::Allocate's only differing target is +0xdc.
That target is the 64-byte De Bruijn ctz table, and its bytes are equal in both images; its planted control is caught.
The 786-member call closure was compared; each of its differing targets was measured by address or classed, and each
of its lui rows was traced in both images and classed (RECORD.md section 5). The closure has 164 differing targets:
148 are settled by a measurement, 16 are NOT CERTIFIED: REAL 0, and none is a measured difference. Of the 109 lui
rows, 70 are settled and 39 are NOT CERTIFIED: REAL 0; each of the 39 is a use that the settlement classes do not
cover, not a measured difference. The constant / base scan for the kit's fail-opens (a)-(h) finds 2934 sites and
0 DIFFERS (2811 equal or settled, 123 NOT CERTIFIED: REAL 0). The 96
sites of the 8 claim functions are all EQUAL. The 21 lui+lui sites (two lui values in one base) have equal targets. All
7 planted controls are refused, and 1 untouched baseline copy is accepted. The kit's own controls (negctl.py and the
40-plant suite.py) give the verdicts that the kit registered. `tools/run.sh` reproduces every `out/` and `scans/`
file: in three end-to-end runs in fresh copies, `diff -r` gave 0 lines (RECORD.md section 10).

## Review

A fresh reviewer approved the record: `REVIEW.md` reads "APPROVE — 0 rejected rows, 3 doubtful rows". The reviewer
re-ran these steps from a pristine kit copy: the 8-function compare (byte-identical apart from the two scrubbed path
lines), the closure and jtcheck (0 diff lines). The reviewer also ran a separate tracer on all 70 settled lui rows and
re-ran the four plant scripts (byte-identical). The 3 doubtful rows were a plant count, two citation line numbers and an
unpinned psABI citation. RECORD.md section 12 fixes all three. No count, class or verdict changed.

## Reading and re-running it here

- The record finds the old-kit re-run "beside the record" (RECORD.md sections 0 and 10, `tools/run.sh`,
  `tools/rerun8cmp.py`) at `../fncmp.cmpkit-4bbd3a74be89.log` and `../../cmpkit-4bbd3a74be89/settled.tsv`. In this tree
  these files are `provenance/evidence/kit-rerun/B/fncmp.cmpkit-4bbd3a74be89.log` and
  `provenance/evidence/kit-rerun/cmpkit-4bbd3a74be89/settled.tsv`. Set RERUN8_LOG and RERUN8_SETTLED to them (the
  script's own overrides). The record read the log before the log moved into kit-rerun/: sha256 eff9ccb831d8, in the
  first line of `out/rerun8cmp.out`. The shipped log has the same 145 lines, and only its two `#` header lines (1 and 4)
  differ. These lines hold paths and no tab. rerun8cmp.py reads only the tab-separated compare rows, and its row parser
  gives equal rows for both logs, on T:E and on S:E. A run against the shipped log prints its sha256 (2fce19debbe3) in
  line 1. settled.tsv is byte-identical (41d7ccff1f7f).
- The kit files are not copied. RECORD.md section 0 tells where they come from. `kit/SHA256SUMS` is the kit's
  checksum list: its own sha256, 86da41d3ef68..., is the kit's name. The four images are named by sha256 in RECORD.md
  "Inputs".
- `../fncmp-cmpkit-4bbd3a74be89/` (RECORD.md sections 0 and 9) is the earlier version of this record, on the old kit.
  This slice does not ship it, because a reader does not need it to check this record: run.sh and the tools do not read
  it, and RECORD.md only says that it exists, unchanged, and that its field scan came before the stack-slot rule.
- `controls/negctl.out` and `controls/suite-planted.sha256` are from a re-run of the kit's controls negctl.py and
  suite.py with every input under a relative name (`controls/run-controls-rel.sh`, which runs the driver copies
  `controls/negctl-rel.py` and `controls/suite-rel.py`). `controls/RERUN-RELATIVE.md` gives the inputs and the driver
  copies by sha256 and shows that every sha256, every verdict line and the line order are those of the first run
  (RECORD.md section 11); only the path text changed.

## Files not shipped

`tools/` here holds 38 of the record's 41 tools. The 3 tools that are not here are hand-work helpers. No step of
run.sh runs them, no tool imports them, and neither RECORD.md nor REVIEW.md names them. No `out/` or `scans/` file
depends on them.

- disas2.py (sha256 442f70655a8b; internal record): disassembles one function by address in both images, for a hand
  argument.
- dwarfparams.py (sha256 b079c5d7a816; internal record): writes the DWARF parameter list of each function to a
  `scans/` file that the record does not hold.
- probe.py (sha256 a86d8788ff98; internal record): a read-only probe of one target pair that the kit reports.

Every other file of the record is here, with the same bytes and the same relative path as in the record.
