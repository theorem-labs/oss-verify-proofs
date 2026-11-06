# Evidence of libdiginet/fuzz_transport's image-A core relocation

proves no function (kind: merge; relocation of libreac/fuzz_grant's released image-A core onto libdiginet
fuzz_transport.asan). One line per file: its role. Paths are relative to this directory; an input that is not in the
repository is named by its sha256 or its ref. METHOD.md gives the route, the run status and every decision with its
measurement, GATES.md every gate's result. MANIFEST (beside this file) names every file of the slice with its sha256.

No file here holds a host path. The scripts take every input from a named variable; in the records, each host path the
tools printed is replaced by its variable: WORK (the run of record's directory), LIB (the lib it read), OUT (the gates'
output root), EV (this directory, the run's inputs), P and TIMG (fuzz_transport's image trees), PG (fuzz_grant's image
tree), DON (fuzz_grant's released lib, normalised), HUB (the hub repository), CKDIR and DONORS (port_addr_check's
directory and donor tree), ALRELOC and ALRELOC_DIR (alreloc's frozen script and its directory), MANIFEST_ELF and CGIF_ELF
(the alreloc model images), PINS (this tree's harness.yaml), CLONE (the clone of this tree), WORK_E0E9, REL_E0E9 and
E0E9_OUT (the e0e94a04094b dry cross-check's run directory, release and output directory), WORK_REC4 (the run before the
record, 13 patches, which the dry cross-check compared against), CLONE_AFET (the clone the A/AFet.v cost lane built),
REGISTRY_README_COPY (a copy of the tool registry's README.md), TCA (row TCA's scratch directory, for any other path under
it), and, in the debug build log, KIT, OSSV_BIN and `~` (the build VM's home). In the two build logs, the build VM's
locations and the clone's name are tokens: <VM_WS>, <VM_DCO> and <VM_CACHE> (the VM's workspace, checked-out copy and
cache), <CLONE> (the clone's name) and <CHECKER_IMAGE> (the checker image's registry path; its sha256 digest stays); in
the address checker's own log (records/rec.log) a person's name in the checker's text is the token <AGENT>. Nothing else
in a record changed. Every record is plain text. records/alreloc-crosscheck-rows.tsv (21,830,098 bytes, over the
repository's 5 MiB cap per file) is kept in five parts cut at line boundaries, records/alreloc-crosscheck-rows.part-1.tsv
to part-5.tsv; only part 1 has the header line. `cat records/alreloc-crosscheck-rows.part-*.tsv` restores
records/alreloc-crosscheck-rows.tsv byte for byte (sha256 9c5dc1563e33e376afcea11093f96d4666a76dfa9eef419dd2e5e2b6c4a84009).

No file here names an actor of the work by its roster name: each is written as the role it played (the image-A core's
writer, the integration owner, the address checker's owner, the ASan toolchain's owner, the relocation tool's reviewer, the
libreac owner, the image-B core's writer), and a decision as the integration owner's decision of its time. A commit that
is not released is not named: a file of it is named by its sha256 (`donor not released`), a tool or record by its basename
and sha256 (`internal record`).

## The run of record and its inputs

| file | role |
|---|---|
| `run.sh` | the relocation run of record: port_core 83f5203d2a2f with `--src-rev 25e3d17bdb50` moves fuzz_grant's released lib (origin/ossv/recipes 25e3d17bdb50, normalised) onto fuzz_transport.asan with 14 `--patch` files, then `hdrcheck.py` checks the header form and `reusable-local.py` makes the shared Zify settings Local; status 3 with the expected rows (records/run-of-record.txt). Its inputs are the files below (EV = this directory). One comment line was rewritten after the run (the run read sha256 be810dc6934d; the other lines are byte-equal; METHOD.md, Route) |
| `hdrcheck.py` | the header form 83f5203d2a2f writes, checked on every staged file: the donor's notice block byte for byte, then the one registered provenance line, no `Modified by` line |
| `reusable-local.py` | reac-repacer/fuzz_uci's core-B script (its bytes, sha256 f3b058010eab): the Zify redefinitions of the shared Reusable/YA09.v and YA0e.v made Local |
| `overrides.tsv` | run.sh's `--override` rows: 59 rows in 19 groups, each group with its measured reason; one comment line rewritten after the run (the run read sha256 e796f27baba3; the other lines are byte-equal) |
| `zero-shadow-forallb.patch`, `cell-lookup.patch`, `ad1q-shape.patch`, `imgtop-alias.patch`, `dead-arm-ad1g.patch`, `bss-zero-range.patch` | run.sh's first 6 `--patch` files, each with its reason in METHOD.md "Patches"; the last gives A/AD1o.v and A/AD25.v the zero-shadow piece their consumer needs |
| `g-ACfn.patch`, `g-AD1w.patch`, `g-AD1m.patch`, `g-AD1p.patch`, `g-AD1q.patch`, `g-AD1r.patch`, `g-AD2f.patch` | run.sh's `--patch` files 7-13, the G patches: the slot contract over the harness globals G, the driver's call at the hull DRV_G (METHOD.md "G patches"; records/ghunks/GHUNKS-A-rec3.md) |
| `afet-cost.patch` | run.sh's 14th `--patch` file: the A/AFet.v proof-script cost fix (four blocks checked by forallb + vm_compute; METHOD.md "Patches"; records/afet/AFET-COST.md) |
| `core-files-transport.txt` | run.sh's `--files`: the release's core-files.txt less YI0j, YO08 |
| `not-relocated-startup-layer.txt` | run.sh's `--no-stage` list: T3r's 19 start-up files (the cut layer, records/startup-layer.tsv) and cgif's YI0a.v, YI17.v |
| `versions.txt`, `required.tsv` | the run's own outputs: the sha256 of port_core.py and each helper; port_core's require-unresolved rows (4: the modules the G patches Require, which the unit writes itself) |
| `add-kit.sh`, `kit-rec.tsv` | the composition kit in the run's LIB: the script that writes the 17 kit files from the released libs by module path only (row TCA's preparation script, sha256 1cfe18d70bfd, with the hub path taken from HUB), and its table for the run of record |

Inputs of run.sh that are not in this directory: the port_core 83f5203d2a2f release (port_core.py,
sha256 83f5203d2a2f; internal record), fuzz_grant's released lib (origin/ossv/recipes 25e3d17bdb50, normalised) and its released
lib/B YA09.v / YA0e.v (recipes 4f87de75d67), fuzz_grant.asan's symbol list (sha256 b46268790c46), the images fuzz_grant.asan
(c2c7559b29bd), fuzz_transport.asan (e89be137db17), its unstripped twin (86efc3a80314) and fuzz_transport.asan-ubsan
(41113a03c82f), and the unit's lib (on the new pin, with T3r's cut layer records/startup-layer.tsv, the kit,
Reusable/YImgTop.v sha256 e4d179ca9a5a). run.sh checks each pin.

## Gates (gates/) and checks (checks/)

Every script runs as `script WORK LIB OUT`; `checks/run-gates.sh WORK LIB OUT` runs them all on one run directory.

| file | role |
|---|---|
| `checks/run-gates.sh` | every gate below as its own single command over WORK LIB OUT/<gate>, with each command, exit status and wall time in OUT/run-gates.txt |
| `gates/pac-A.sh`, `gates/flag-gate-A.sh`, `gates/triage-A.py` | gate (a): port_addr_check 205a90fd19b8 (its SHA256SUMS checked), one default pass, `--fail-on-flags`; the triage of every flagged row; the two planted pointers and the unplanted control |
| `gates/codeptr-A.sh`, `gates/codeptr-notaddr.tsv` | gate (b): codeptr 12348302dfd2 through the start-up set 2026-10-30d's frozen-run.sh; the not-address declarations, each measured at every occurrence |
| `checks/run-all.sh` | the value lane: items 1-6 below, each with its control; exits 1 when a step or a control fails |
| `checks/decval-A.sh`, `checks/decval.py`, `checks/decval_extra.py`, `checks/decval_hand.py` | gate (c): the by-value check, stages 1 and 2, the rows read from the target ELF, the plant |
| `checks/secbounds.py`, `checks/cellvals.py` | the 22 section-bound cells against the pin's section headers; the stated memory values against the image bytes |
| `checks/atable-A.sh` | the core side of the atable check: A/AB1w.v's `tfib_at_*` rows against atable's fields |
| `checks/gotwords.py`, `checks/gotwords-A.sh` | the .got words the core states, read in both images, and the control |
| `checks/compcheck.py`, `checks/compcheck-A.sh` | the four compensating checks of the port_core registry entry, and the control |
| `checks/symoff.py`, `checks/symoff-A.sh` | every relocated numeral that names data, resolved as symbol + offset on both images, and the control |
| `checks/rclane.py`, `checks/roundconst-A.sh` | roundconst-gate v2 32b39f3b34e9 over the run's gate TSV and the lane's own report, and the plants |
| `checks/v10-gate.py`, `checks/v10_table.py` | gate (d): global_settings v10 439f8e3bd463 over the files this core adds and their released donor files, the files the unit writes itself (UNIT_FILES), and the plant |
| `checks/yh03-gate.py` | gate (e): yh03check fb3bfbc1eea8 (v6.4) on the unit's YH03 files with --pinned, unit identity, COPIED, pairing, the plants, and the cells v6.4 does not judge read by content. Changed after the gate run of record: it reads the donor's symbol prefix and the name of the YH03.v:44 cell (written CELL44 in the record) from the input YH03.v instead of naming them; records/run-gates.txt names its earlier sha256 b27b9145631b, and the changed script, run again on the run of record, gives records/yh03check.txt byte for byte |
| `checks/ghunks-A.sh` | the G patches on the run of record: undone on WORK's stage-out and re-applied on the 6-patch text (check_gpatches.py), the hull and the region counts measured (asan_globals.py, measure_gcut.py), two controls |
| `checks/make_gpatches.py`, `checks/check_gpatches.py`, `checks/asan_globals.py`, `checks/measure_gcut.py` | the G work's tools (records/ghunks/GHUNKS-A-rec3.md, "Re-run"): the patch writer, the patch check, the asan_globals parser, the hull and count measurement |
| `checks/alreloc-gate.sh`, `checks/alreloc-xcheck.sh`, `checks/alreloc-xcheck-control.sh`, `checks/alreloc_compare.py`, `checks/alreloc_decide.py`, `checks/alreloc_plant.py`, `checks/alreloc_sweep.py`, `checks/alreloc_record.py` | the alreloc a5c53bb2bed4 cross-check of every relocated numeral as one command: the record run decided against the target ELF, the planted control, the two seeded sweeps, the generated tables |
| `checks/hypvalues.sh`, `checks/hyplist.py`, `checks/hypderive.py`, `checks/coqhyp.py`, `checks/imgs.py` | every value in a hypothesis position: the listing, the derivation of each differing one, the Rocq lexer, the ELF parser, the plants |
| `checks/strftime_a1_trace.py` | the closure of cmpkit 86da41d3ef68's two open __strftime_fmt_1 rows |
| `checks/pac_namediff.py` | the named-symbol rows of two port_addr_check runs on one run directory (0d24592683b6 flagged, 205a90fd19b8 SAME-SYMBOL), each read against the twins (records/PAC-NAMEDIFF.md) |
| `checks/czone_measure.py` | the highest constant shadow end, from the image's asan_globals descriptors |
| `checks/tfibtable-A.py`, `checks/tfib-hand-rows.tsv` | the whole tfib table of lib/A read against the twin: image B's tfibtable-B.py (sha256 1f1eb92bf82a; internal record) with lib/B -> lib/A, the FALSE screen (the pairs whose label names no symbol at its value, alias forms included), and the hand read's rows (the owner's test per cell: T1 / T2 -> WRONG, FALSE -> FALSE; the function the label names, where it really is) |

## Records (records/), each of the run of record

| file | role |
|---|---|
| `run-of-record.txt` | run.sh's summary lines, every check.tsv FAIL row with its reason, port_core's limits L1-L4, the run's outputs |
| `run-gates.txt` | the one gate command: each gate's command, exit status and wall time; the sha256 of every script |
| `PAC-GATE.md`, `flag-gate.txt`, `gate-205a90-TRIAGE.md`, `gate-205a90-triage-rows.tsv`, `rec-triage.out`, `rec.log` | gate (a): the prose record (with the findings of NON-ADDRESS-CHANGED and STALE-DONOR-CODE-POINTER new against 0d24592683b6); the record run and three controls; the triage by reason; one row per flagged row; the counts; the checker log |
| `PAC-NAMEDIFF.md`, `pac-namediff.tsv`, `flag-gate-0d24592683b6.txt` | addendum to gate (a): the named-symbol rows 0d24592683b6 flagged and 205a90fd19b8 passes as SAME-SYMBOL (54, each read against the twins); the table of the readings; the record of the 0d24592683b6 run on the run of record it compares |
| `codeptr.txt`, `codeptr-occurrences.tsv` | gate (b): the runs, roles and controls; every occurrence of every declared value with its role |
| `VALUES.md`, `RESULTS.txt` | the value lane: the prose record with the rows decided by hand; every result and control line |
| `decval.txt`, `decval-hand-rows.tsv`, `decval-open-rows.tsv` | gate (c): the result lines and plant; the rows read from the target ELF; the 22 open stage-2 rows, each read by hand |
| `symoff-hand-rows.tsv` | the symbol + offset sweep's 24 rows, each read by hand |
| `secbounds.txt`, `cellvals.txt`, `cellvals.tsv`, `atable.txt` | the section cells, the stated memory values, the atable core side, each with its control |
| `gotwords.txt`, `gotwords-control.txt`, `gotwords.tsv` | the .got words and the control |
| `compcheck.txt`, `compcheck-control.txt`, `compcheck-rows.tsv`, `compcheck-decided.tsv`, `compcheck-a2-unique.txt` | the compensating checks: counts, control, every row; the 468 rows decided by hand (each applies where part, file:line and value match; one row moved with the line g-AD2f.patch shifts); the a2 contexts read by hand |
| `symoff.txt`, `symoff-control.txt`, `symoff.tsv` | the symbol + offset sweep: counts and its rows, the control, every row |
| `roundconst.txt`, `roundconst-read.txt` | roundconst-gate v2: the runs, plants and every non-SAME row; the 1751 non-SAME rows read by hand (the same rows as in the dry run) |
| `settings-count.txt`, `v10-donor-lines.tsv` | gate (d): the counts and the plant; every settings row with the identical line of its released donor file |
| `yh03check.txt` | gate (e): the runs, plants and the cells read by content |
| `ghunks.txt`, `ghunks-check_gpatches.out`, `ghunks-measure_gcut.out`, `ghunks-measure_gcut-plant.out`, `ghunks-asan_globals.tsv` | the G patches on the run of record (checks/ghunks-A.sh): the record, check_gpatches.py's output, the measurement, the control's measurement, the twin's asan_globals |
| `ghunks/GHUNKS-A-rec3.md`, `ghunks/GHUNKS-A.md`, `ghunks/check_gpatches.out`, `ghunks/measure_gcut.out`, `ghunks/measure_gcut-control.out`, `ghunks/asan_globals-86efc3a80314.tsv` | the G work's own record (on work-rec3): GHUNKS-A-rec3.md for the cut layer, GHUNKS-A.md (its section 3, the hunk classification, and section 9 still hold), its patch check, its measurement, its control on the uncut list, the asan_globals table |
| `e0e9-dry/E0E9-DRY.md`, `e0e9-dry/run.log`, `e0e9-dry/release-sha256.txt`, `e0e9-dry/compare.py`, `e0e9-dry/compare.out`, `e0e9-dry/new-fail-rows.tsv`, `e0e9-dry/gone-fail-rows.tsv`, `e0e9-dry/check-diff.tsv`, `e0e9-dry/stage-out-cells.tsv`, `e0e9-dry/stage-out.diff`, `e0e9-dry/measure.py`, `e0e9-dry/measure.out` | the DRY cross-check with port_core e0e94a04094b (of record now) on the run of record's inputs: the record; its run log, the release's sha256 list, the comparison script and its output, the new and gone FAIL rows, the changed check rows, the stage-out cells, the stage-out diff, the image measurements |
| `ALRELOC-CROSSCHECK.md`, `alreloc-gate.txt`, `xcheck.log`, `control.log`, `sweep.log`, `sweep2.log`, `record-tables.md`, `alreloc-crosscheck-rows.part-1.tsv` to `alreloc-crosscheck-rows.part-5.tsv`, `alreloc-wrong-rows.tsv` | the alreloc cross-check: the prose record; each step's status; the record run; the control; the two sweeps; the generated tables; one row per numeral position (alreloc-crosscheck-rows.tsv in five parts); the 22 rows the rules call WRONG, each read by hand |
| `RESULT.txt`, `hyplist.txt`, `hypvalues.txt`, `hyplist-plant.txt`, `hypvalues-plant.txt`, `control.txt`, `content.tsv`, `kept.tsv`, `differs.tsv`, `hyplist.tsv`, `unlisted-derived.tsv`, `unlisted-differs.tsv`, `WRONG-ROWS.md` | the values in hypothesis positions: the result and control; the listing and derivation of the run and of the planted copy; the memory facts; the kept rows; every differing row derived; every listed numeral; the differing numerals outside hypothesis positions; the WRONG rows, each read by hand |
| `STRICTCMP-RUNTIME.md`, `strictcmp3-five.txt`, `jtcheck-five.txt`, `strftime-neutral-oldpin.s` | cmpkit 86da41d3ef68 over the five runtime functions the row names (image-only): the record, the raw outputs, the neutral listing strftime_a1_trace.py reads |
| `startup-layer.tsv` | the 19 start-up files of row T3r's cut layer that the run read, each with its file sha256 (the layer by content; its commit is not released) |
| `czone.txt` | the 40 asan_globals descriptors of the twin and the highest constant shadow end 0x800b663c (checks/czone_measure.py; its last line checks the dry runs' bound 0x800bac00; 0x800b663c is below the run of record's 0x800b9c00 too) |
| `afet/AFET-COST.md` | the A/AFet.v cost fix: the lane report (cause, the cell counts and A/AFet.vo times per unit, the patch, the build); its build log (line 51: A/AFet.vo 8.48 s, 706944 ko) was removed from the shipped tree on 2026-11-04; internal record, in git history |
| `TFIB-WHOLE-TABLE.md`, `tfib-whole-table.tsv` | the whole tfib table of lib/A (1201 cells) read against the twin: the lane report with each class, the integration owner's WRONG test of 2026-10-31 (T1 / T2) per cell, the function-label rule (FALSE, 11:55Z, corrected 12:07Z: an interceptor or wrapper alias of the named function stays; the two region-bracket cells are OK-REGION by the bracket convention, to which the function-label test does not apply) with its 41 screened pairs decided one by one, the list of all 83 removed pairs with each one's class, the function it names and the function at its value, re-checked under the 12:07Z alias correction (0 of 83 holds an alias of its own function; 0 restored), the two kept region brackets and the label-by-label diff against image B, and the table itself, one row per cell, written on the lib before both removals. The 160 WRONG cells (80 _A / _E pairs) and the 6 FALSE cells (3 pairs), every one the released donor's own label with 0 readers, were removed from lib/A/AB1w.v in two commits; the run of record's stage-out still holds them, so from those commits the committed file and WORK/stage-out/A/AB1w.v differ in exactly those 83 lines |
| `model-tags/check.txt`, `model-tags/run.txt` | the record of model_tags.py e1cb9c4fb27f on the unit: the check run and the real run (the 14 allocator-model label literals become the tags 1..14, 42 occurrences in 12 files, 0 remaining) |
