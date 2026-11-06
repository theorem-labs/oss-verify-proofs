# provenance/evidence/stackmalloc1-B: fuzz_uci image-B class-1 __asan_stack_malloc_1 contract

The files a reader needs to re-derive lib/B/Rt/YF0r.v, lib/B/Rt/YF0s.v and lib/Reusable/YF0v.v and their gate
numbers. Environment of the scripts: `P` libreac's pinned image tree, `R` reac-repacer's, `REL` the extracted port_core
0e4e065eab9f, `DON` the donor lib made by ../core-B/mkdon.sh, `LIB` the unit's lib, `WORK` run.sh's work dir; the gate
tools as gates/run-gates.sh lists them.

| file | role |
|---|---|
| METHOD.md | the route (core-B's, for three files) |
| GATES.md | the gate numbers, each with its planted control |
| BYTECMP.md | bytecmp of __asan_stack_malloc_1 and of every body the proofs step through; uci A and uci B carry it at the same address |
| bytecmp.py | the body comparison (with --plant for its control) |
| run.sh | the relocation run of record (port_core flags) |
| files-sm1.txt | --files: the three donor files, each with its reason |
| overrides-sm1.tsv | --override: the one value no rule decides |
| measure-sm1.py, measure-sm1.out | measures that value by role, with the donor's own value as control |
| B-fs-ranges.patch | --patch: the code table without fuzz_grant's class 0 / 2 / 4 rows |
| apply-sm1.sh, applied.txt | copies the staged files by --apply's rule; the list of the 3 files written |
| header-sm1.py | comments-only header step; checks code bytes unchanged |
| header-sm1-restore.py | the corrected header rule: inherited licence lines restored from the donor blob (scrub table only), our line dated; checks code bytes unchanged |
| gates/run-gates.sh | every gate and control over the committed files |
| gates/triage-sm1.py | one measured reason per flagged row of port_addr_check e165063a0081; exit 1 on any unexplained row |
| gates/codeptr-notaddr-sm1.tsv, gates/codeptr-occurrences-sm1.tsv | codeptr's non-address declarations and every occurrence they cover |
| gates/rangetab-sm1.py | the keyed range-table check of fs_ranges (in place of atable) |
| gates/decval-sm1.py | the by-value check (core-B's decval-B.py with this file list, plus --declare) |
| gates/records-sm1.py | writes records/ from the gate outputs and the cb logs, with role names for paths |
| records/bytecmp-bodies.out | bytecmp.py's output over the 13 bodies |
| records/bytecmp-control-1.out, records/bytecmp-control-2.out | bytecmp.py controls: a planted `or` for the `and` at FS_LOOP; a planted call re-pointed |
| records/bytecmp-control-3.out, records/bytecmp-control-4.out | bytecmp.py controls on the TLS-index .got cell: a planted module id; the cell pointed at another symbol |
| records/bytecmp-control-5.out | bytecmp.py control on a pair's partner: a planted destination register |
| records/strictcmp2-bodies.out | the superseded comparison kit (cmpkit 4bbd3a74be89, strictcmp2 16982e3ef42b) over the same 13 bodies |
| records/strictcmp3-bodies.out | the comparison kit of record (cmpkit 86da41d3ef68, strictcmp3) over the same 13 bodies |
| records/luiscan.out, records/ambiscan.out | the kit's exposure scans over the 4bbd3a74be89 record (lui-built addresses; duplicated names) |
| records/settle-rcf.out, gates/settle-rcf-sm1.py | the hand settlement of the one target the kit does not settle (RegisterCommonFlags +0x1218) |
| records/flag-gate.txt, records/flag-triage.tsv | the flag gate's FLAGGED lines (run and control); per-row reasons |
| records/codeptr.txt | codeptr per file, per run (base, declared, donor, plant, plant-declared) |
| records/atable-replacement.txt | keyset classes / check and the range-table check with its controls |
| records/byvalue.txt, records/byvalue-rows.tsv, records/byvalue-review.tsv | the by-value check: summaries, per-numeral rows, review rows |
| records/settings-count.txt | v10 counts of the files, of the donor's counterparts and of the control |
| records/yh03check.txt | yh03check (N/A) and its controls |
| records/build.txt, records/print-assumptions.txt | the cb build of record and its control; Print Assumptions of stack_malloc1_contract |
