# provenance/evidence/core-B: fuzz_uci image-B core relocation

The files a reader needs to re-derive the image-B core files in lib/B (all except the 19 start-up files) and their gate
numbers. No generation logs. Environment of the scripts: `P` libreac's pinned image tree, `R` reac-repacer's, `REL` the
extracted port_core 0e4e065eab9f, `DON` the donor lib made by mkdon.sh, `LIB` the unit's lib, `HUB` a clone of the
proofs repository.

| file | role |
|---|---|
| METHOD.md | the route: donor, tool, inputs and their controls; shared by every reac-repacer image-B core |
| GATES.md | the gate numbers, each with its planted control |
| run.sh | the relocation run of record (port_core flags) |
| mkdon.sh | makes the donor: fuzz_grant's released lib/B over lib/Reusable at the lib root |
| mksyms.py | the donor symbol list from its unstripped twin |
| fuzz_grant.asan-ubsan.syms.txt | --old-syms, the output of mksyms.py |
| files-B-core.txt | --files: the release's core-files-Y.txt minus 8 files, each with its reason |
| no-stage-B.txt | --no-stage: the 19 start-up files and two files the core never stages |
| overrides-B.tsv | --override: 47 values no rule decides, each with its measured reason |
| measure-B.py, measure-B.out | measures each override value by role, with the donor's own value as control |
| B-zero-shadow-forallb.patch, B-cell-lookup.patch, B-ad1q-shape.patch | --patch: image A's structural patches for B |
| mkpatch-B.py | re-cuts an image-A patch for image B by content |
| reusable-local.py | makes every Zify flag redefinition in lib/Reusable/YA09.v and YA0e.v Local; checks the code equals the released lib/B copy with every site Local |
| apply-B.sh, applied.txt | copies the staged files by --apply's rule; the list of the 370 files written |
| imgtop-require.py | post-step: B files that Require YImgTop take image B's lib/B/YImgTop.v (port_core names image A's); changes only that sentence |
| gates/pac-B.sh | port_addr_check runner (flag gate and 3186) |
| gates/triage-B.py | one measured reason per flagged / GENERATOR-FILL row; exit 1 on any unexplained row |
| gates/decval-B.py | the by-value check (image A's check with image-B inputs) |
| gates/codeptr-B.sh, gates/codeptr-notaddr.tsv, gates/codeptr-occurrences.tsv | codeptr with its controls; the non-address declarations and every occurrence they cover |
| gates/records-B.py | writes records/ from the gate outputs, with role names for paths |
| records/flag-gate.txt, records/flag-triage.tsv | FLAGGED / FLAG-CLASSES lines (run and controls); per-row triage |
| records/byvalue.txt, records/byvalue-rows.tsv | by-value summary (run and control); per-numeral table |
| records/codeptr.txt | codeptr lines with findings, per run |
| records/settings-count.txt | global_settings counts of this core and of the donor's counterparts |
