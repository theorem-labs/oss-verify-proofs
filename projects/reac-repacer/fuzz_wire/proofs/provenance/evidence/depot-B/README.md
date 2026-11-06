# provenance/evidence/depot-B: the consumer side of the empty-depot form, fuzz_wire image B

rule 24: no function proved. The lib/B files this record makes are libreac/fuzz_knock's RELEASED image-B text
(origin/ossv/recipes 88154566652a, proofs/libreac/fuzz_knock/lib/AU) relocated onto fuzz_wire.asan-ubsan by port_core
7a74e72920e6 and taken into the unit's grant-lineage lib/B text hunk by hunk, by the method of record of the unit's
image-A core (its step 2: proofs/reac-repacer/fuzz_wire/provenance/evidence/depot at 4483a8de6e6f, build round 31),
carried to image B.

Files made: the lib/B consumers (the Y twins of the image-A core's knock-files.txt that the unit's lib/B holds, without YB1w.v:
109), the 10 knock-only Require-closure files (YD3a YD3b YD3c YD3d YD3g YD3h YD3i YD3j YD3k YFk0g), the glue
lib/B/YD3dEnv.v, and the E6 line in the 16 E6 files that are not consumers (YFk5 YFkb .. YFkl YFko YFkw YFkx YFky).
lib/B/AWalkFw0.v is relocated but not laid: as on A (closure_awalk.py; the image-A core's lib/A has no AWalkFw0.v) every
Require of AWalkFw0 names YB1v, which defines tfibsegs itself. Not made here: lib/Reusable (the image-A core's kernel),
the per-image kernel hunks of lib/B YC5d YCbp YCbq YCe5 and the YB1w depot rows (the image-B core owner's
kernel-depot-B.py and yb1w-rows.py). The image-A core takes no consumer hunk of AB1w: it keeps its committed AB1w and
adds three rows by ab1w_rows.py.

## Environment

`UNIT` the unit (fuzz_wire); `HUB` a clone of the proofs repository; `TREE` the unit commit whose lib/B is the grant text;
`A_CORE` the image-A core commit: its lib/Reusable (the empty-depot kernel) is the relocation target's, its evidence/depot
(`A_EVIDENCE` names another path) gives consumer-classes.tsv, takes.tsv, knock-files.txt and the two flag tables;
`A_GRANT` / `A_KNOCK` the image-A pair that core's table compares (A/<F>: the relocated grant text; knock's text relocated
onto fuzz_wire.asan); `REL` the extracted tools/pg-reloc/7a74e72920e6; `P` libreac's result directory; `R` reac-repacer's;
`TWIN` the sha256 of the unit's unstripped asan-ubsan twin; `CZONE` the CZONE bound the core owner keeps; `S1` step 1's
out dir.

## Commands (fuzz_wire, this record)

    UNIT=fuzz_wire HUB=<clone> TREE=b55ba5ae509 A_CORE=4483a8de6e6f REL=<7a74e72920e6> P=<libreac> R=<reac-repacer> \
      bash step1.sh $S1
    bash compare-step1.sh $S1/work <the image-B core's step-1 work dir> > step1-compare.txt
    UNIT=fuzz_wire HUB=<clone> TREE=b55ba5ae509 A_CORE=4483a8de6e6f A_GRANT=<A grant> A_KNOCK=<A knock> S1=$S1 \
      REL=... P=... R=... TWIN=51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3 CZONE=0x80050000 \
      bash step2.sh $OUT [<unit lib>]
    bash record.sh $OUT run

step1.sh ran with A_CORE=cc592f53d4ff for this record; the two commits hold the same lib/Reusable (the image-A core left it
unchanged since a0f3b92af52c).

## Files

| file | role |
|---|---|
| step1.sh | step 1: mkdon.sh (../core-B) makes the donor from knock's lib/AU; target = the lib of the image-B core's commit + the image-A core's lib/Reusable, minus the lib/B files the run stages; run-knockB.sh |
| run-knockB.sh | the image-B core owner's port_core command of the knock relocation; adapted: REL, P, R come from the environment (its own lines 14-16 named host paths) |
| knockB-files.txt, fuzz_knock.asan-ubsan.syms.txt | that owner's inputs of step 1: the 88 Y twins of A's knock rows; --old-syms |
| compare-step1.sh, step1-summary.txt, step1-compare.txt | step 1's port_core summary and its comparison with that owner's run |
| reloc.sh | one port_core run over a file list on step 1's target (ADD_B: files the unit writes itself, laid into the target) |
| unit_root.sh | sourced by step1.sh, step2.sh and reloc.sh: the unit's proofs root at a commit (projects/reac-repacer/<unit>/proofs, or the earlier proofs/reac-repacer/<unit>) and the unit's lib inside an extracted tree, by the layout each has; no script hard-codes one layout. This record's inputs (the image-B core's grant-text commit and the image-A core's commits) are of the earlier layout |
| mk_glue_ad3d.py | (e) lib/B/YD3dEnv.v: env_agree_Ereg_app copied from knock's lib/AU/YF0r.v:313-319 (the image-A core's script, --image B, --unit-mod). Above the Requires the script copies the donor's own Copyright and SPDX lines (its lines 1-2) byte for byte and writes no notice; licence-lines --apply adds the notice afterwards, from the licence map row lib/B/YD3dEnv.v -> fuzz_knock lib/AU/YF0r.v. In --image A mode it writes the image-A core's AD3dEnv.v byte for byte |
| mk_yd3d_patch.py | (e) the --patch that makes B/YD3d.v Require YD3dEnv instead of YF0r (the B twin of the A core's ad3d-env.patch) |
| derive_overrides_knockB.py | the --override rows of the knock relocation by role and symbol (the A core's derive_overrides_knock.py for image B and any unit) |
| yd3j-window.py | post-step on the committed lib/B/YD3j.v: b2_mod_cells_kept's window end = page_up(common_flags_dont_use + 0x105) of the target's twin, in its statement and proof; then the three comment phrases that state the window ([lo, end) twice, and the end of the last cell read) get the target's values; a no-op on a file that holds them |
| step2.sh | step 2 end to end: file list, glue, patch, override rows, the relocation, (a) classification, row mapping, (b) depot_apply, (c) closure rules, ad1g_guard, (d) tail rule, d1w_close, E6 / E7, leak gate |
| depot_classify.py, consumer_classify.py | (a) the consumer class table (--consumer --sub B) and the residue report |
| map_rows.py | the image-A core's decisions (its classes, takes.tsv with its MERGE rows, a-merges.tsv, its AWalkFw0 rule) carried to the B hunks by line content |
| a-merges.tsv | the image-A core's four hand --merge rows that its takes.tsv does not carry (AD1g 6 / 33, AFex 38 / 39: its round-22 log) |
| depot_apply.py, imgtop_rule.py | (b) the hunk takes, merges and the YImgTop unfold rule. step2.sh always passes --lib-repo; the script's own default (the earlier layout's fuzz_wire lib) is the image-A core's text and is never used here |
| closure_glue.py, closure_awalk.py | (c) the two closure rules on the knock-only files |
| notice_split.py | (c) on YD3i.v, YD3j.v, YD3k.v (knock's released lib/AU text): line 3 opens a `Modified by` notice that runs on into the file's documentation in one comment, which the licence tool cannot bound; the notice (line 3 up to its attribution, or all of line 3 when the attribution runs on into line 4) becomes its own one-line comment and the documentation a second comment right after it. Every other line, the Copyright and SPDX lines and the code, is byte-unchanged; the comment-stripped code is equal. A second run changes nothing |
| ad1g_guard.py | the image-A core's dead-arm rule on YD1g.v (the xcell guard itself is already knock's form in the B grant text) |
| tail_generalize.py, d1w_close.py | (d) the E5 tail_ext_ok rule (YFjm YFis YFj6); the A core's D1W_ok closing rule (YFj1 YFjf) |
| zify_flag_sets.py, zify_flag.py | glue E6 / E7 of the image-A method (the Zify division flag set to false / to true): the files, from the A core's two flag tables; the one Local Zify flag line. The scripts are the A core's e6e7_sets.py and e6_flag.py renamed, byte for byte but their usage line, so their logs still print `e6_flag:` |
| leak_gate.py, leak-gate-exceptions.tsv | the image-A core's leak-watch gate over the applied consumers. Its rule: PASS (exit 0) iff every LINEAGE token of an applied piece is cleared by a row of leak-gate-exceptions.tsv (file, applied line, token, a needle the piece contains, reason) and every row clears a hit; step2.sh stops when it fails. The table has 2 rows: the k argument 8192 of FPP_site at YFk0.v:1529 and :1617, depot-zone arithmetic carried with knock's text, whose A twins the image-A core's record classes as knock-unmoved proof numerals |
| record.sh, run/ | the outputs of step 2 of this record. The relocation's own diff does not ship (its added lines copy .v comments of the image-A text that name lanes: inherited inside a .v file, new inside a patch). It is in the unit's internal record, commit 637e502429b1:depot-B/depot-B.patch, sha256 abad22c74edc6ac5f5373107d2dd5e05a32d18cdd1de5c8a194d934534a26407 (18202 lines), and record.sh writes it only where `PATCH_OUT` names. The scripts of this directory reproduce it from the image-A core at 4483a8de6e6f |
| controls.txt | each adapted script in image-A mode on the image-A core's inputs reproduces that core's output |
| adaptations/*.diff | each adapted script against the image-A core's text |

## Results

Step 1 (step1-compare.txt): 88 staged, 0 kept; required = the 9 CZONE rows (0x80050000) and B/YD3d.v
require-unresolved B.YF0r; stage-out 88 of 88 byte-identical to the image-B core owner's run.
Step 2 (run/): 120 files relocated (run/reloc-summary.txt: 14 override rows applied, 1 patch applied, required empty).
The 14 rows (run/overrides-knockB.tsv) are 2 for YD3b, 9 CZONE rows and 3 for YD3j: donor lines 435, 441 and 444,
each 0x131000 -> 0x133000, the window end of b2_mod_cells_kept = page_up(common_flags_dont_use + 0x105) (fuzz_wire
0x132328 + 0x105). The symbol gate explains those 3 (DIFFERENT-SYMBOL, override: port_core's by-symbol value is 0x133280
= useCounts + 0xbc0), 5 explained in all. The 136 lib/B files the run writes are byte-identical to the committed ones,
YD3j.v after its post-step: yd3j-window.py on the run's YD3j.v prints `already ends its window at 0x133000` and sets the
three comment phrases that state the window (lines 57, 58, 436, after the notice split) to the target's values, which gives the committed file.
(a) 109 consumers, 3312 hunks: depot 703, layout-grow 35, other 2574; map_rows: take 1894, keep 1384, mixed 10, B-only
24, A taken not on B 9 (each listed in run/rows-B.tsv); 1196 --take, 58 --merge. (c) closure_glue 72 names, closure_awalk
11 Require lines; notice_split 3 files. ad1g_guard: dead arm removed (6184960 is not 1507 * 4096). (d) tail_generalize 3 sites, d1w_close 2
sites. E6 18 files, E7 13 files. leak gate: PASS, LINEAGE hits 0 after the 2 exception rows (both used; without them
the 2 hits fail it, as they did before the table existed). port_core_refused markers left: 0. lib/B files: 136.
Build (cb a2bb66b099ce, dune, a build VM, a workspace made fresh from the unit's base 25e3d17bdb50, all 403 lib/B
targets, 2026-10-31T06:54Z): rc 0, 390 compiled, 13 restored from the cache, 0 failed; its vo check: `660 .vo read,
18868 Require digests compared with this build's .vo, 5445 with the checker image's .vo (41 of its libraries read under
<COQLIB>), 0 .vo failed (0 inconsistent, 0 missing a library, 0 unreadable)` (<COQLIB>: the checker image's Coq library
directory). The tree is the unit tree of 82a38b87d9ed: lib/B as the image-B core holds it at 2b7e14aaecf (this
record's 136 lib/B files, byte-identical to run/'s output; that owner's kernel-depot-B.py hunks of YC5d YCbp YCbq YCe5,
A_BEFORE 655d9c3e47c, A_AFTER cc592f53d4ff; its YB1w.v with the yb1w-rows.py rows StackStore_Store,
StackStore_BlockInfo_Create, TwoLevelMap_Create_71714) and lib/Reusable byte-identical to the image-A core's at
4483a8de6e6f.
