# provenance/evidence/stackmalloc1-A: fuzz_uci image-A class-1 __asan_stack_malloc_1 contract

The files a reader needs to re-derive lib/A/Rt/AF0r.v, lib/A/Rt/AF0s.v and lib/Reusable/YF0v.v and their gate
numbers. Environment of the scripts: `P` libreac's pinned image tree, `R` reac-repacer's, `REL` the extracted port_core
0e4e065eab9f, `DON` the donor lib made by mkdon-sm1.sh, `LIB` the unit's lib, `WORK` run.sh's work dir, `HUB` a clone of
the proofs repository; the gate tools as gates/run-gates.sh lists them.

| file | role |
|---|---|
| MANIFEST.md | this list |
| METHOD.md | the route (core-A's, the image-B record's with image B -> A, for three files) |
| GATES.md | the gate numbers, each with its planted control; Print Assumptions; the consumer's hypothesis closed by exact |
| BYTECMP.md | bytecmp of __asan_stack_malloc_1 and of every body the proofs step through (13 / 13 equal up to relocation with bytecmp.py), the data-place rules (pointer cell, NUL string + 64-byte window, p_filesz reader), the one measured change to the image-B tool, its six controls, the class-1 call site; the re-run on the comparison kit 4bbd3a74be89 (12 / 13 kit-EQUAL: RegisterCommonFlags' empty-string place at +0x1218 not certified by the kit) with its six controls; that place settled by hand as an acceptance (EQUAL as a C string; 13 / 13 after settlement); and the scans of cmpkit 86da41d3ef68 over that re-run (clear) |
| bytecmp.py | the body comparison (the image-B record's fixed tool f31bad62a6cb with the image-A shas and the addi-0 partner rule; --no-addi0, --plant, --plant-data) |
| sites.py | every call into an __asan_stack_malloc_<k> of one image (the class-1 call site and the classes the image links) |
| cmpkit-sm1.py | runs the 13 pairs and six controls on the comparison kit 4bbd3a74be89 (strictcmp2's tcmp; checks the kit directory and SHA256SUMS; adds no compare) |
| cmpkit-86da41d3ef68-scans.sh | runs cmpkit 86da41d3ef68's luiscan (the 13 functions, both images) and ambiscan (the records/cmpkit-4bbd3a74be89-*.out files) from a copy of the kit: `cmpkit-86da41d3ef68-scans.sh KIT P R OUT` |
| mkdon-sm1.sh | normalises fuzz_grant's released lib at recipes 4f87de75d67 into run.sh's DON (core-A's rule) |
| run.sh | the relocation run of record (port_core flags, image pins) |
| files-sm1.txt | --files: the three donor files, each with its reason |
| measure-sm1.py, measure-sm1.out | the image-B record's override value measured by role on both image-A images: the donor's bound holds on fuzz_uci.asan, so no override |
| A-fs-ranges.patch | --patch: the code table without fuzz_grant's class 0 / 2 / 4 rows |
| YF0v-lia.patch | --patch: YF0v.v shadow_apart's last step nia -> lia (the text rules forbid nia) |
| apply-sm1.sh, applied.txt | copies the staged files by --apply's rule; the list of the 3 files written |
| header-sm1.py | comments-only header step: inherited lines byte for byte the donor's, one dated notice; checks code bytes unchanged |
| gates/run-gates.sh | every gate and control over the committed files |
| gates/pac-sm1.sh | runs port_addr_check (efa19b81e92b of record, e165063a0081 beside it) on the donor text vs the ported text, image A |
| gates/triage-sm1.py | one measured reason per flagged row of port_addr_check; exit 1 on any unexplained row |
| gates/codeptr-notaddr-sm1.tsv, gates/codeptr-occurrences-sm1.tsv | codeptr's non-address declarations and every occurrence they cover |
| gates/rangetab-sm1.py | the keyed range-table check of fs_ranges (in place of atable) |
| gates/decval-sm1.py | the by-value check (the image-B record's decval-sm1.py with image B -> A) |
| gates/records-sm1.py | writes records/ from the gate outputs and the cb logs, with role names for paths (`-` for a scratch build's log leaves its record) |
| gates/settle-sm1.py | the named measurement of RegisterCommonFlags +0x1218: the place's C string in both images, every use of its address, every reader of the field it is stored in; refuses unless it is read only as a C string |
| records/bytecmp-bodies.out, records/bytecmp-bodies-b-tool.out | bytecmp.py's output on the two image-A twins (exit 0), and with --no-addi0 (the two rows the added rule decides) |
| records/bytecmp-control-1.out, records/bytecmp-control-2.out, records/bytecmp-control-3.out, records/bytecmp-control-4.out, records/bytecmp-control-5.out, records/bytecmp-control-6.out | bytecmp.py's six planted controls (three instruction words, the .got cell's module id, the cell re-pointed, a byte in an empty string's window; each exit 1) |
| records/bytecmp-control-6-before-fix.out | control 6 run with the tool of 2894d73b0f91: the empty-string plant missed (exit 0), the defect the window rule fixes |
| records/cmpkit-4bbd3a74be89-summary.out | the kit re-run, one line per pair (12 EQUAL, RegisterCommonFlags NOT EQUAL; its +0x358 words EQUAL) and per control (6 caught) |
| records/cmpkit-4bbd3a74be89-twins.out | drvcmp.py twins: each side's unstripped twin against its stripped pin |
| records/cmpkit-4bbd3a74be89-pairs.out | strictcmp2.py cmp over the 12 pairs named once in each image, with every C-string acceptance (CSTR rows) |
| records/cmpkit-4bbd3a74be89-pairs-by-address.out | strictcmp2's tcmp on the MemToShadow copy stack_malloc_1 +0x144 calls and on RegisterCommonFlags +0x358 (8 bytes) |
| records/cmpkit-4bbd3a74be89-fulllist.out | strictcmp2's tcmp called directly on all 13 pairs: the full differing-target list (1 target in all: RegisterCommonFlags +0x1218) and the acceptance counts per pair, each identical to the printed list |
| records/settle-sm1.out | settle-sm1.py's output: SETTLED EQUAL AS A C STRING, with every instruction it read |
| records/settle-sm1-review.md | the fresh reviewer's audit of that acceptance, with its verdict |
| records/cmpkit-acceptances-review.md | a fresh reviewer's audit of the kit's acceptances (200 C strings, 3 full-byte compares, 1 .got value, 1 tls_index): equality and consumer per acceptance, with its sample rule and verdict |
| records/cmpkit-4bbd3a74be89-region.out | the one differing target measured: both regions' lengths and first difference |
| records/cmpkit-4bbd3a74be89-control-1.out, records/cmpkit-4bbd3a74be89-control-2.out, records/cmpkit-4bbd3a74be89-control-3.out, records/cmpkit-4bbd3a74be89-control-4.out, records/cmpkit-4bbd3a74be89-control-5.out, records/cmpkit-4bbd3a74be89-control-6.out | the kit's compare on six planted file copies of the target twin (each caught) |
| records/cmpkit-86da41d3ef68-kit.out | the kit check of the scans: `sha256sum -c SHA256SUMS` (nine OK), sha256(SHA256SUMS) = kit id 86da41d3ef68, python / pyelftools / capstone versions |
| records/cmpkit-86da41d3ef68-luiscan.out | luiscan 9ae61e4a0e01 on the 13 functions in both images: exposure 0 in every row, cleared on memfed 0 / the section test (not proof alone: rule 8 is settled by records/cmpkit-86da41d3ef68-lui-trace.md) |
| records/cmpkit-86da41d3ef68-ambiscan.out | ambiscan 9f61b4cee422 on the 12 records/cmpkit-4bbd3a74be89-*.out files: 0 ambiguous hits |
| records/cmpkit-86da41d3ef68-lui-trace.md | rule 8 by hand: every lui of the 13 functions (10 per image) traced through every register-register and register-immediate ALU op (add / sub / sh*add, and / or / xor / andi / ori / xori included), memory, branches, calls and spills, to each register's next write, in both images, with the listings and the list of ops followed; none forms a static address, no row is `lui-const (dataflow)` |
| records/sites-target.out, records/sites-donor.out | sites.py on fuzz_uci.asan's and fuzz_grant.asan's twins |
| records/flag-gate.txt, records/flag-triage.tsv | the flag gate's FLAGGED lines (record run and two planted pointers, both checkers); per-row reasons of the run of record |
| records/codeptr.txt | codeptr per file, per run (base, declared, donor, plant, plant-declared) |
| records/atable-replacement.txt | keyset classes / check and the range-table check with its controls |
| records/byvalue.txt, records/byvalue-rows.tsv, records/byvalue-review.tsv | the by-value check: summaries, per-numeral rows, review rows |
| records/settings-count.txt | v10 counts of the files, of the donor's counterparts and of the control |
| records/yh03check.txt | yh03check (N/A) and its controls |
| records/build.txt | the cb build of record and its planted control |
| records/print-assumptions.txt | Check + Print Assumptions of stack_malloc1_contract (an uncommitted scratch file's source and compile output) |
| records/consumer-fit.txt | the consumer's hypothesis type (lib/A/UciClose.v:143 at 9ee6811b6c95) closed by exact on a scratch merge (source and compile output) |
