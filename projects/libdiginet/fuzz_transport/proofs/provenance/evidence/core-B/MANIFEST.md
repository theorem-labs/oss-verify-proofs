# Evidence of libdiginet/fuzz_transport's image-B core relocation

proves no function (kind: merge; relocation of libreac/fuzz_decode's released image-B core onto libdiginet
fuzz_transport.asan-ubsan, by libdiginet/fuzz_decode's image-B core route). One line per file: its role. Paths are
relative to this directory; an input that is not in the repository is named by its sha256 or its ref. This slice has no
METHOD.md or GATES.md: run.sh's header gives the route and its inputs, and each decision is written where it is used, in
the comment of its input row (overrides-B.tsv, placement-B.tsv, files-B-core.txt) or in the header of the script that
writes its patch. MANIFEST (beside this file) names every file of the slice with its sha256.

The relocation recorded here is run r17, the run of record: port_core 83f5203d2a2f with --src-rev 88154566652a, on a
lib that holds the image-A core (row TCA) at 7cc72d296fab, which carries the allocator-model tags (0ece7baefb1) and
EV_LIB 2048 (788c910512e), and the image-B start-up layer cut for the new pin (row T4r); this tree applied it. It
replaces run r11, which tree 5ce997ee04cb applied as INTERIM, pre-cut and UNBUILT (the image-B start-up layer on its
branch was still the old pin's). r17 differs from r11 by the 91 function-table cell pairs B-tfib-wrong.patch deletes,
the comment B-sec-cells.patch writes above `tfib_img_lo` / `tfib_img_hi`, the B/YFet.v proof text of
B-yfet-cost.patch, the 14 allocator-model labels written as the tags 1..14 in the seven image-B twins of
B-model-tags.patch, the read window's zero-shadow piece start in B/YD25.v (overrides-B.tsv: 0xa8fa0, the new start-up
list's own entry), the stdout buffers' consumer bound in B/YD1o.v (overrides-B.tsv: 0x5f2e80, the piece start rounded
up to 64 bytes), EV_LIB 2048 in B/YCfn.v and B/YCfl.v (overrides-B.tsv) and the untimed shok arm of B/YCeg.v
(B-untime.patch, README.md). Run r16 (applied in dd5df37d7398) was run r17 without B-untime.patch; r17's stage-out
differs from r16's in B/YCeg.v line 307 only. Run r13 was run r14 without the B/YD1o.v
bound; its applied tree 4d8cde586afb failed the whole-unit build there and at TransportDriverB.v's Require
(README.md). Run r14 (applied in 2d48500794db) was run r15 with 79 deleted pairs and without B-sec-cells.patch. Run
r15 (applied in a9ace4689126) was run r16 on the image-A core at 77e71b70bc6, without B-model-tags.patch and the two
EV_LIB rows; r16's stage-out differs from r15's in those nine files only (B/YFeu, YFft, YFfy, YFfz, YFg2, YFi3,
YFk0, YCfn, YCfl: 21 lines). port_core 83f5203d2a2f reports each of the 19 tags B-model-tags.patch writes as a FAIL
row `label-moved` (its rule: an opaque label keeps the donor's value), and 9 of them also as `value-role-conflict`
(the same label value kept at another line of the run); every one of these 28 rows is at a position the patch
writes, by the ruling that the labels are tags 1..14, not addresses (model_tags.py's header). B-stops-more.patch and
B-yd1q-shape.patch are taken by run.sh's own `B-*.patch` glob since run r15 (earlier runs passed them as `.draft`
files after the glob); the glob order is the file names' order. rehearsal/ holds the earlier runs r1, r3 and r4 of
the same route. README.md and TFIB-TABLE-B.tsv record the deletion of mislabelled function-table cells from
lib/B/YB1w.v, which run r17 makes by B-tfib-wrong.patch.

No file here holds a host path. The scripts take every input from an argument or a named variable (run.sh: REL, DON,
LIB, P, T; measure-B.py: P, T, STAGE; pins-B.py: P, T, HUB and optional refs; SECHI-B.py: HUB, TWIN, PIN, OUT). In the
records, each host path the tools printed is replaced by its variable, written `<NAME>`: `<WORK>` (the run's
directory, run.sh's `<workdir>`), `<port_core>` (the port_core release directory, run.sh's REL), `<P>` (libreac's
pinned image tree), `<T>` (fuzz_transport's image tree), `<core-B>` (this directory, from which run.sh reads its
inputs), and `<TWIN>` / `<PIN>` (SECHI-B.py's TWIN and PIN, in SECHI-B.out line 1). The internal name of the ASan tool
kit that port_core vendors, and the file names of the kit's two address tools, are replaced the same way: `<KIT>` (the
kit), `<KIT_MAP>` (its address-map script, which writes the run's map.json) and `<KIT_REWRITE>` (its numeral-rewrite
script, which writes remap.tsv and remap-out/); they occur in rehearsal/r4-port_core.log (line 1),
run-r17/port_core.summary (line 1) and 13 status cells of run-r17/review.tsv. Each replacement changes only the path or
name token; nothing else in
a record changed. In the prose of README.md and cmpkit/SETTLE5.md, in the scripts' headers and comments, and in the
reason column of placement-B.tsv, each worker, agent or branch name is replaced by the role it played: the image-A
core's row TCA, the image-B start-up layer's row T4r, the image-B G-patch work, the libreac owner, the release lead, a
fresh review subagent, the tool registry, the port_core release registry, this core's branch, the image-B
address-table branch. Row names (TCA, TCB, T3r, T4r, D6) stay. Those files differ from their earlier commits in these
tokens only, and SECHI-B.py also in the four lines that read HUB, TWIN, PIN and OUT from the environment and the two
output paths it builds from OUT (run with them, it writes SECHI-B.tsv, B-sec-cells.patch and its other outputs
byte-equal to the files it was first run to, and SECHI-B.out equal but for the two paths on line 1).

## The run and its inputs

| file | role |
|---|---|
| `run.sh` | the relocation: port_core (REL, checked against PC_SHA: d9e0589898fd by default, or 83f5203d2a2f, which runs r11 and r17 used) moves the donor's released lib/B (DON: libreac/fuzz_decode at recipes 88154566652a, normalised by mkdon.sh) onto fuzz_transport.asan-ubsan with the inputs below (`<core-B>` in the records), after it checks the six image pins; then `apply-B.sh` |
| `apply-B.sh` | copies a run's stage-out into LIB by port_core --apply's own rule (A/ always; any other file only when LIB lacks it), because --apply refuses while the run's known FAIL rows stand; it refuses when a refusal marker is left or a non-A file would be overwritten, and writes the copied paths |
| `files-B-core.txt` | run.sh's `--files`: libdiginet/fuzz_decode's image-B core list (port_core 8deb08754248's core-files-Y.txt, 625 entries) less YI0j.v and YO08.v, each with its measured reason |
| `no-stage-B.txt` | run.sh's `--no-stage` list: the 19 lib/B files of the unit's image-B start-up layer, and YI0a.v, YI17.v |
| `placement-B.tsv` | run.sh's `--placement` table: 12 modules, each with its placement (AU or SHARED) and why |
| `overrides-B.tsv` | run.sh's `--override` rows: 114, each with its measured reason in its comment (among them the stdio FILE buffers and BUFEND, the driver format shadow windows, __asan::instance + 0x328, the 49 rows that keep the donor's decimal 8, the zero-shadow pieces of the stdout buffers and of the read window, CZONE, the two value rows the gates found, and EV_LIB); since run r13 the read window's piece starts at 0xa8fa0, since run r14 the stdout buffers' consumer bound is 0x5f2e80, since run r16 EV_LIB is 2048 in B/YCfn.v and B/YCfl.v (2 * OPS_MAX 1024: receive calls malloc and free once on this image) |
| `libreac-fuzz_decode.asan-ubsan.syms.txt` | run.sh's `--old-syms`: name, address and size of every sized FUNC / OBJECT symbol of the donor twin (6744989bb2e6), written by `mksyms.py` |
| `mksyms.py` | writes that symbol list from an unstripped twin; its header line names the twin and the pin by sha256 only |
| `B-ceg-const.patch`, `cutceg-B.py` | --patch: B/YCeg.v `lib_const_addr` states this program's four own .rodata constant reads in place of the donor's five ranges; the script that writes it from a stage-out |
| `B-noodr.patch`, `noodr-B.py` | --patch: the donor's ODR-page hunks of B/YD1d.v, YD1e.v, YD1f.v and YD1g.v reversed (three head maps, as on decode, not the donor's four); the script that cuts it from the donor's four edit diffs |
| `B-qcache.patch`, `qcsplit-B.py` | --patch: the donor's `0x32dd0 beq a4,a1` case split in B/YFgg.v and B/YFgh.v removed, where this image does not need it (0xa9340 mod 4096 = 832, not 0); the script that computes the rule on both images and writes the patch |
| `B-yd1g-arm.patch`, `cutarm-B.py` | --patch: the dead alternation arm of B/YD1g.v's `tfib_layout_ok` proof removed (form (a)); the script that writes it |
| `B-stops-more.patch`, `cutstops-B.py` | --patch: B/YB1w.v `tfib_at_stops_more` gains the image's 13th self-loop site 0x6effc, in lib/B/YB12.v's order; the script that writes it |
| `B-yd1q-shape.patch`, `cutyd1q-B.py` | --patch: B/YD1q.v Requires A.TransportShape (the image-A core's shape module) in place of the donor's A.DecodeShape, without the dead Require of YO08; the script that writes it |
| `B-g-YCfn.patch`, `B-g-YD1m.patch`, `B-g-YD1p.patch`, `B-g-YD1q.patch`, `B-g-YD1r.patch`, `B-g-YD1w.patch`, `B-g-YD2f.patch` | --patch: the G patches, libreac/fuzz_pcap's G form (the slot over the program-global ranges G) in B/YCfn.v, YD1m.v, YD1p.v, YD1q.v, YD1r.v, YD1w.v and YD2f.v |
| `B-tfib-wrong.patch` | --patch: the 91 cell pairs of B/YB1w.v that README.md and TFIB-TABLE-B.tsv give, deleted: the 79 of `git diff 5ce997ee04cb af222741584e -- lib/B/YB1w.v` (the three deletion commits) and the 12 that fail rule (f), with the paths written `B/YB1w.v` |
| `B-sec-cells.patch`, `SECHI-B.py` | --patch: the comment above `tfib_img_lo` / `tfib_img_hi` in B/YB1w.v names the pinned image (sha256 41113a03c82f) and the two values from its headers, in place of the donor's `decode:` note (YImgTop computes the bounds), which is false here; the script that writes it (with SECHI-B.tsv and SECHI-B.out) |
| `B-yfet-cost.patch`, `cutfet-B.py` | --patch: the four quadratic membership blocks of B/YFet.v replaced by one forallb check each, decided by vm_compute (the image-A core's A/AFet.v fix); proof text only; the script that writes it from a stage-out |
| `B-model-tags.patch`, `cuttags-B.sh` | --patch: the 14 allocator-model labels (201364 .. 469488, read from lib/Reusable/YG00.v before the image-A core's commit 0ece7baefb1) written as the tags 1..14 in the seven image-B twins B/YFeu.v, YFft.v, YFfy.v, YFfz.v, YFg2.v, YFi3.v and YFk0.v (19 occurrences), as that commit wrote them in image A's twins and the shared lib/Reusable files; the script that cuts it: model_tags.py e1cb9c4fb27f (the tool registry's tools/model-tags/e1cb9c4fb27f/), unchanged, on the lib before that commit with a run's stage-out applied, the lib/B part of its diff (the lib/A and lib/Reusable files it writes are checked equal to the image-A core's) |
| `B-untime.patch`, `cutuntime-B.sh` | --patch: in B/YCeg.v the `timeout 30` token of `shok_auto_with`'s first arm and the `timeout-ok` marker comment on its line go (rule a of tools/publish/untime; the timed tactic and the fallback arm stay), as the image-A core's commit 3b8ca450689 did at lib/A/ACeg.v:308; the script that cuts it: `untime --commit` (publish/t14-untime 1e5c0ac35654), unchanged, on the tree the run is applied to, the lib/B part of its change (the row it adds to provenance/evidence/untime-removed.tsv goes into the tree with it) |

Inputs of run.sh that are not in this directory: the port_core release (the port_core release registry,
tools/pg-reloc/83f5203d2a2f/ and tools/pg-reloc/d9e0589898fd/), the donor's released lib/B (libreac/fuzz_decode at
recipes 88154566652a, normalised by mkdon.sh), the unit's lib before the run (LIB), and the images, each checked by
run.sh: libreac fuzz_decode.asan-ubsan (pin 5d05689fd5b1, twin 6744989bb2e6), fuzz_decode.asan (5973b76807d8),
fuzz_transport.asan-ubsan (pin 41113a03c82f, twin e217cb0a84f1) and fuzz_transport.asan (e89be137db17). noodr-B.py also
reads the donor's four edit diffs and measure_ad1g.py (sha256 247f39888c46), and cuttags-B.sh model_tags.py
e1cb9c4fb27f and the lib at the image-A core's 77e71b70bc6 with the start-up layer, and cutuntime-B.sh the untime
release (publish/t14-untime 1e5c0ac35654: tools/publish and tools/oft), which are not here either.

## Checks and measurements

| file | role |
|---|---|
| `pins-B.py` | the pins and the donor inputs, each with its control: each image against its harness.yaml pin, each twin against its pin, the --old-prog rule, the --old-syms list, the call sites of the walked runtime entries (record: rehearsal/pins-B.pre.out) |
| `measure-B.py` | the values of overrides-B.tsv and B-ceg-const.patch, each by its role, on the donor image (control: it must print the donor's released value) and on the target image (record: rehearsal/measure-B.r1.out) |
| `symsweep-B.py` | the donor-paired symbol + offset sweep of a run's relocated numerals; expected 0 hits; control: a row planted onto a .got cell (record: rehearsal/symsweep.r1.out) |
| `hypaudit-B.py` | every numeral in a hypothesis position of a run's stage-out, paired with its donor line, for a derivation by hand (record: rehearsal/hypaudit.r3.out) |
| `tfibcells-B.py` | the `tfib_*_lo` / `tfib_*_hi` section cells of the image-B lib against the pin's section headers; control: the donor lib against the donor pin |
| `tfibtable-B.py` | writes TFIB-TABLE-B.tsv: every `tfib_A_` / `tfib_D_` / `tfib_E_` cell under lib/B and lib/Reusable against the twin, its class by rules (a) to (f) in its header, and for each WRONG cell the alias screen: the interceptor or wrapper names at its value are of the function its label names (an own alias: the cell is correct and must not be deleted), of another function, or absent |
| `SECHI-B.py` | every section `_lo` / `_hi` cell of image B (lib/B, lib/Reusable and the address-table kit lib/B/Prog) against the twin's section headers: FALSE, MATCH-ABUTS or MATCH-PADDED, each with its readers and its writer; the comments that cover the cells; `--control` plants FALSE and abutting cells |

## Records

| file | role |
|---|---|
| `run-r17/port_core.summary` | port_core's summary lines of run r17: 388 files staged, the 19 start-up files not staged, 18 patches applied, 0 failed, status 3 (22 FAIL rows: the 3 of every earlier run and 19 `label-moved` at the tags B-model-tags.patch writes; 1 open required.tsv row) |
| `run-r17/check.tsv`, `run-r17/fixed.tsv`, `run-r17/review.tsv`, `run-r17/overrides.tsv`, `run-r17/required.tsv`, `run-r17/patches.log` | port_core's outputs of run r17, each equal to run r16's but patches.log (B-untime.patch's output): every numeral row with its status and class (8358: run r15's 8323, 7 `patched` rows and the 28 FAIL rows at the 19 tags); the 740 values written over the rewrite step's; the 280 rows for review (run r15's 252 and the 28 rows at the tags; one of r15's is the tfib_at_rw_len override value 0x571000, which the data-symbol check reports at line 513 because the patches delete 89 lines above it net, while its override row names the stage line 602); each --override row with its status (112 applied, 2 NOT-FOUND: IMG_LO 0x10000 kept); the one require-unresolved row (B.TransportDrvGB, a module the unit writes itself); the output of each --patch |
| `applied-r17.txt` | apply-B.sh's list of the 388 files copied from run r17's stage-out into the lib |
| `untime-B.before.txt`, `untime-B.after.txt` | `untime --report libdiginet/fuzz_transport` in cutuntime-B.sh, on the tree before and after its `--commit`: 1 site (B/YCeg.v:307, rule a, ltac:shok_auto_with), then 0 |
| `model-tags-B.check.txt`, `model-tags-B.run.txt` | model_tags.py e1cb9c4fb27f's `--check` and run output in cuttags-B.sh on run r16: 61 code occurrences in 19 files (image A's 42 in 12 files and the seven image-B twins' 19), 0 comment occurrences, 0 left after the run |
| `TFIB-TABLE-B.tsv` | tfibtable-B.py's table at tree 5ce997ee04cb, before the deletions: 1211 cells (OK-EXACT 814, OK-ALIAS 119, NO-SYMBOL 96, WRONG 182), each with the symbol at its value, its class and note, the donor's pairing, its readers and, for a WRONG cell, the alias screen (no-alias 176, other-function-alias 6; no cell is on an alias of its own function, so none is restored) |
| `SECHI-B.tsv`, `SECHI-B.out` | SECHI-B.py's cells and its output at tree 2d48500794db (and the address-table kit at a83315552115): 25 section cells checked, 0 FALSE, 14 MATCH-ABUTS, 11 MATCH-PADDED |
| `PAC-B.md`, `PAC-B.r17.flagged.tsv` | port_addr_check 45b78aaa48c3 on run r17: its run line, the checker's sha256, the flag counts against 205a90fd19b8 on the same run (670 / 669: 2 new rows, 1 gone, explained), and the rows decided by hand: the 7 CZONE rows of overrides-B.tsv and the changed bound of B/YE7d.v:78 (`snl_rom_low`, true for both values, 0 readers: no change); the 670 flagged rows with the checker's columns |
| `README.md` | four paragraphs: the 91 cell pairs deleted from lib/B/YB1w.v, by group, and the table that gives them; the two driver files copied into lib/B after apply-B.sh, and the lib/Reusable Require of TransportDriverB.v; the 25 section cells and B-sec-cells.patch; the untimed shok arm of B/YCeg.v and its removed marker |
| `rehearsal/pins-B.pre.out` | pins-B.py's output before the unit's harness.yaml carried the new pins (the target pins read DIFFERS against it; the donor's read EQUAL) |
| `rehearsal/measure-B.r1.out` | measure-B.py on run r1: the donor control and the target's values |
| `rehearsal/symsweep.r1.out` | symsweep-B.py on run r1: 11 hits; the three at __asan::instance + 0x328 are the real ones (overrides-B.tsv) |
| `rehearsal/hypaudit.r3.out` | hypaudit-B.py on run r3: 8455 lines listed, 117 differ from the donor, each with both numeral lists |
| `rehearsal/eight-rows.r3.tsv` | the 85 positions of run r3 where port_core's geometry rule wrote the donor's decimal 8 as 1560 (this pin's .relro_padding length), each with its line: the basis of the 49 overrides-B.tsv rows that keep 8 |
| `rehearsal/r4-port_core.log` | port_core's summary lines of run r4 (no --src-rev; status 3 with 40 open required.tsv rows) |

## cmpkit/: the five runtime functions

| file | role |
|---|---|
| `cmpkit/SETTLE5.md` | the record: cmpkit 86da41d3ef68's strictcmp3 over the five runtime functions row TCB names, the donor twin against the target twin; every refused target settled (EQUAL, or the lui values traced by hand), 0 REAL; the fresh review |
| `cmpkit/cmpkit-86da41d3ef68.SHA256SUMS` | the kit's 9 files with their sha256, checked before the run |
| `cmpkit/settle5-B.py`, `cmpkit/settle5-B.out` | the settlement of every target the kit refuses (the script runs beside the kit's strictcmp3.py), and its output |
| `cmpkit/luitrace-B.py`, `cmpkit/luitrace-B.T.out`, `cmpkit/luitrace-B.D.out` | the hand dataflow of the lui-built values, and its output on the target twin and on the donor twin |

The kit itself (the tool registry at 98e50c029045, tools/cmpkit/86da41d3ef68/) and its own `cmp` rows (cmpkit5.out) are
not in this directory.
