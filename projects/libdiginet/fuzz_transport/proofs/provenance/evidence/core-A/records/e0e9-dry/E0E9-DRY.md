# DRY cross-check of the port_core of record against the run of record (83f5203d2a2f, work-rec5)

proves no function (kind: measurement). Row TCA, libdiginet/fuzz_transport image-A core. It compares two tool runs on
the same inputs.

## Which tag, and why

- The tool registry (README.md, sha256 44131f52b660; internal record; 2026-10-31T07:59:38Z) names the port_core of record in
  tools/pg-reloc-portcore/LATEST: `e0e94a04094b` (README.md line 2394: `pg-reloc-portcore: LATEST = e0e94a04094b`; line
  2296: `port_core e0e94a04094b OF RECORD, SUPERSEDES 83f5203d2a2f`). There is no tools/port_core/LATEST on that ref.
- d6572d099856 is released as a tool directory (port_core.py, sha256 d6572d099856; README.md, sha256 c05f21a8df56;
  internal records; `pg-reloc d6572d099856: 465c9cffd0b8 + item 109, two fixes and a row per known limit`), and
  465c9cffd0b8 also (port_core.py, sha256 465c9cffd0b8; internal record). The registry names neither; its README has no
  entry for either. So the tag run here is e0e94a04094b, the LATEST of record when the run started.

## Command (run once, 2026-10-31T08:04:40Z to 08:11:02Z)

    REL=REL_E0E9 DON=<fuzz_grant lib 25e3d17bdb50, normalised> PG=<fuzz_grant images> P=<fuzz_transport images> EV=EV
    SYMS=<fuzz_grant.asan.syms.txt b46268790c46> LIB=LIB GRANTB=<recipes 4f87de75d67 lib/B> sh run.sh WORK_E0E9

- run.sh is the run of record's own (14 `--patch` files), not edited; only REL and the run directory differ. REL_E0E9 is
  the release directory tools/pg-reloc/e0e94a04094b (port_core.py, sha256 e0e94a04094b1f52...; internal record);
  release-sha256.txt lists every file's sha256, each equal to the release README's list.
- Exit status 3 (run.log), as the run of record. e0e94a04094b accepts every argument run.sh passes.

## Result (compare.out: `python3 compare.py WORK WORK_E0E9 OUT`)

- FAIL rows in check.tsv: the record 16, this run 15; NEW FAIL rows 0 (new-fail-rows.tsv: header only).
- FAIL shadow-offset rows: 0. shadow-offset is no class of this tag (its README lists the case as a known answer it does
  not cover); the shadow classes it has (shadow-window, shadow-unmapped, shadow-unmoved) give no new row.
- override-no-file / override-not-found rows: 0. In this tag NO-FILE is a status in overrides.tsv: 0 NO-FILE rows; the 59
  rows (37 applied, 22 removed by --patch) are byte-equal to the record's. required.tsv byte-equal (4 require-unresolved
  rows).
- Interval-delta, tot-bound, hypothesis-decimal-moved, bound-name-mismatch: 0 FAIL rows each (2 tot-bound information rows
  on A/AFem.v:128 and A/AFek.v:34, values 127008 and 131072 as the record's).
- The only FAIL row the record has and this run has not: A/AFem.v:206 value-role-conflict (gone-fail-rows.tsv). e0e94a04094b
  leaves it out because an override row writes the value; both runs write 127008.
- stage-out: 492 files in each; every file differs in one line only, the provenance line, and only in its tool sha (`by
  port_core 83f5203d2a2f` / `by port_core e0e94a04094b`); 0 other cells differ (stage-out-cells.tsv: header only;
  stage-out.diff). So the stage-out is byte-identical apart from the tool sha the provenance line names.
- check-diff.tsv: 8 rows (4 cells) whose check / review row differs, no value changed (A/AFem.v:206 and :128, A/AFek.v:34,
  A/AB1w.v:11 `bound-name-mismatch` -> `bound-by-name`, value 0xa2948 in both: the target .text end 0x310d0 + 0x71878 and
  .tbss start; measure.out).
- Verdicts: no new FAIL row and no differing value cell, so nothing to classify as REAL or TOOL-LIMIT. VALUE findings: none.

An earlier run of the same tag on the inputs of work-rec4 (13 patches; the run before afet-cost.patch) gave the same
result: 0 new FAIL rows, the same gone row, the same 8 check-diff rows (byte-equal), stage-out differing only in the
provenance lines.
