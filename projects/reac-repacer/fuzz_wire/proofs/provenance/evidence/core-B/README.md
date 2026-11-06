# provenance/evidence/core-B: fuzz_wire image-B core relocation

The files a reader needs to re-derive the image-B core files in lib/B that this record writes (247 of the 372 staged
files; the other 125 and 11 new files are the empty-depot consumer side, recorded in provenance/evidence/depot-B; the 19
start-up files are the start-up layer's) and their gate numbers. No generation logs. The route is fuzz_uci's:
proofs/reac-repacer/fuzz_uci/provenance/evidence/core-B/METHOD.md. Environment of the scripts: `P` libreac's pinned
image tree, `R` reac-repacer's, `REL` the extracted port_core 7a74e72920e6, `DON` the donor lib made by mkdon.sh, `LIB`
the unit's lib, `HUB` a clone of the proofs repository. The commit ids this record cites are internal working commits;
each is preserved, with its date and subject, in the unit's internal records (PRESERVED-COMMITS.tsv).

| file | role |
|---|---|
| run.sh | the relocation run of record (port_core flags), with what differs from fuzz_uci's run |
| mkdon.sh | makes the donor: fuzz_grant's released lib/B over lib/Reusable at the lib root |
| mksyms.py | the donor symbol list from its unstripped twin |
| fuzz_grant.asan-ubsan.syms.txt | --old-syms, the output of mksyms.py |
| files-B-core.txt | --files: the release's core-files-Y.txt minus 6 files, each with its reason |
| no-stage-B.txt | --no-stage: the 19 start-up files and two files the core never stages |
| overrides-B.tsv | --override: 59 values no rule decides, each with its measured reason |
| measure-B.py, measure-B.out | measures each override value by role, and reads the start-up tables, with the donor's own values as control |
| B-zero-shadow-forallb.patch, B-cell-lookup.patch, B-ad1q-shape.patch | --patch: image A's structural patches for B |
| mkpatch-B.py | re-cuts an image-A patch for image B by content, with measured OLD=NEW value pairs (here the image top 0x5f5000=0x5f6000) |
| reusable-local.py | the script that made lib/Reusable YA09.v / YA0e.v's Zify redefinitions Local (applied by image A's core) |
| apply-B.sh, applied.txt | copies the staged files by --apply's rule; the list of the 372 files written |
| icpt-memmove.py | post-step: YE34.v icpt_ranges takes __asan_memmove's range (0x510b0, 220 words; fuzz_wire calls it, the donor does not), checked against the symtab |
| yd1j-x2.py | post-step: YD1j.v drops the cell lemma mu0 and passes no MU0 to x2_realizes (0 descriptors: the start-up layer's exit walk reads no mu cell) |
| kernel-depot-B.py | post-step: image A's lib/Reusable empty-depot hunks on the per-image YC5d / YCbp / YCbq / YCe5 (patch by position, zero fuzz; comment-only hunks skipped) |
| yb1w-rows.py | post-step: knock's image-B YB1w rows StackStore_Store, StackStore_BlockInfo_Create, TwoLevelMap_Create_71714, each checked as a function of the twin |
| yb1w_clause2_lockB.py, yb1w-clause2.tsv, yb1w-clause2.out | the classifier of record for YB1w.v's named cells (fuzz_lock core-B's e46125e3f178, here as its comment-only edit sha256 a1fa17a61c4c from 7e4fe76d8554; options in GATES.md section 8); its per-cell table and counts for the YB1w.v of afb40eec804 |
| yb1w-drop-unread.py, yb1w-drop.tsv | post-step: removes from YB1w.v the 237 cells the table classes FALSE or unverifiable by symtab, each checked again on the twin with a second key, with 0 readers outside lib/A by the table, a comment-free token scan and `git grep -w`; one record row per cell |
| yb1w_clause2_v4.py, yb1w-clause2-v4.tsv, yb1w-clause2-v4.out | the classifier with name rule v4 (fuzz_lock core-B's 53e5ca93b62c, here as its comment-only edit sha256 b953becc4241 from 7e4fe76d8554; GATES.md section 9); its table and counts for the YB1w.v of e0194e87996 |
| yb1w-drop-v4.tsv | yb1w-drop-unread.py's record of the 12 cells rule v4 classes FALSE named-other, removed from YB1w.v |
| yb1w_clause2_v5.py, yb1w-clause2-v52.tsv, yb1w-clause2-v52.out, yb1w-clause2-v52-after.out | the classifier v5.2.1 (fuzz_lock core-B's, sha256 600920ff3e78, unchanged; GATES.md section 10); its table and counts for the YB1w.v of 63a960d3030, and its counts on the file after the removal (FALSE 0) |
| yb1w-drop-v52.tsv, yb1w-v52-meaning.tsv | yb1w-drop-unread.py's record of the 80 cells v5.2 classes FALSE named-other, removed from YB1w.v; each one read by meaning (TRUE by meaning / FALSE by rule, FALSE, or a donor-address label) |
| records/yd3j-plant.txt | the planted control of lib/B/YD3j.v's window end (bound 0x13242c fails at the cell C4, 0x13242d compiles; GATES.md section 11) |
| gates/pac-B.sh | port_addr_check runner (flag gate) |
| gates/triage-B.py | one measured reason per flagged / GENERATOR-FILL row; exit 1 on any unexplained row |
| gates/decval-B.py | the by-value check (image A's check with image-B inputs) |
| gates/codeptr-B.sh, gates/codeptr-notaddr.tsv, gates/codeptr-occurrences.tsv | codeptr with its controls; the non-address declarations and every occurrence they cover |
| gates/records-B.py | writes records/ from the gate outputs, with role names for paths |
| records/flag-gate.txt, records/flag-triage.tsv | FLAGGED / FLAG-CLASSES lines (run and controls); per-row triage |
| records/byvalue.txt, records/byvalue-rows.tsv | by-value summary (run and control); per-numeral table |
| records/codeptr.txt | codeptr lines with findings, per run |
| records/settings-count.txt | global_settings counts of this core and of the donor's counterparts |
| records/yb1w-flag-triage.tsv | triage-B.py's table for the flag scan of the run of record's stage-out with the committed B/YB1w.v (GATES.md section 8) |
| yb1w-side-stack-note.py | post-step: empties YB1w.v's donor note on side-stack rows that image B links and image A does not, after it measures on both twins that no such function exists (GATES.md section 13) |

GATES.md and records/yb1w-side-stack-note.txt were removed from the shipped tree on 2026-11-04 (internal record; in git history); the GATES.md sections cited above and in this directory's scripts are in that record.
