# The value gate of record: port_addr_check 3d2eee813cce

Tool: port_addr_check.py sha256 3d2eee813cce (the installed gate of record since 2026-10-30 16:32Z; versioned copy
`audit-tools/versions/3d2eee813cce/` with its helper modules), run once per pairing with `--fail-on-flags`, `--paired-only`,
`--summary`, the full row output (`--out full.tsv`, every row, not only flags), images keyed by build (A = asan,
B = asan-ubsan), each pinned image given with its unstripped twin (same link: equal PT_LOAD table, equal allocated
sections, equal loaded bytes except `.note.gnu.build-id`, measured with pyelftools). Command form (`$PAC` = the
versioned tool directory, `$HUB` = a clone of the proofs repository, `$IMG` = the image copies below, `$BIN` = the pinned
donor set the tool reads by default):

    python3 $PAC/port_addr_check.py --git $HUB --src <SRC> --dst <DST> \
      --src-image <KEY>=<donor pin>:<donor twin> --dst-image <KEY>=<our pin>:<our twin> \
      --donors-from $BIN --cache cache --paired-only --summary --fail-on-flags --out full.tsv [--include ..] [--dst-include ..]

| image | sha256 | twin sha256 |
|---|---|---|
| cgif_file_fuzzer.asan (donor, key A) | 7093581aab04 | 488e39500746 |
| cgif_file_fuzzer.asan-ubsan (donor, key B) | 1c29845fe605 | ce511d541cda |
| fuzz_command.asan (ours, key A) | c0661b96b5bd | 68db792d5fa7 |
| fuzz_command.asan-ubsan (ours, key B) | bbe55d24d096 | 658cefbe806b |

## Runs

| run | SRC (donor) | DST (ours) | keys | files paired | numerals | FLAGGED | full.tsv sha256 / rows |
|---|---|---|---|---|---|---|---|
| RA (record, image A core) | c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib/A, `A*.v` | repository tree (git tree 1c3596a429a4; internal record):proofs/plugin-hostd/fuzz_command/lib/A, `A*.v` | A | 389 | 212053 | 25054 | 4a709c0abb3b / 212083 |
| RB (record, image B core) | c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib, `Y*.v` | repository tree (git tree 1c3596a429a4; internal record):.../lib/B, `Y*.v` | B | 389 | 212121 | 25107 | 989144f32040 / 212151 |
| RU (lib/Reusable) | c8557374ad2e:.../lib, `Y*.v` | repository tree (git tree 1c3596a429a4; internal record):.../lib/Reusable, `Y*.v` | B | 400 | 97050 | 1957 | a12f3cea2f1e / 97081 |
| RAB (relay view) | repository tree (git tree 1c3596a429a4; internal record):.../lib/A, `A*.v` (image A) | repository tree (git tree 1c3596a429a4; internal record):.../lib/B, `Y*.v` (image B), `--map A=Y` | B on both sides | 389 | 208131 | 4483 | f80e902f659a / 208160 |

`summary-<run>.txt` holds each run's INPUTS USED block and verdict counts (host paths replaced by `$...` names);
`flagged-<run>.txt` its FLAGGED line and exit code (4 = flags present, as `--fail-on-flags` defines). The full row files are
not in this record (34 MB each); the commands above reproduce them, and their sha256 are in the table.

## Controls (each must fire)

| control | expected | got | result |
|---|---|---|---|
| CA donor-on-donor, cgif lib/A on itself, image A | no row of a "names something different" class | 724 files, 341220 numerals; only HASH-UNCHANGED 4 and UNRESOLVED 124 (both are the tool's own limits on an unchanged file: a hash left unchanged is the same hash; unnamed both sides) | PASS |
| CB donor-on-donor, cgif root Y on itself, image B | as CA | 1449 files, 606645 numerals; only HASH-UNCHANGED 4, TARGET-OUTSIDE 171, UNRESOLVED 393 | PASS |
| PA / PB planted controls: four plants per image in copies of our files (`plants.tsv`), each run against an unplanted base copy of the same four files | each plant flagged, nothing else changes | stale donor code pointer: STALE-DONOR-CODE-POINTER (A and B); stale donor data pointer: STALE-DONOR-DATA-POINTER (A and B); model constant moved by a code delta (class B): DIFFERENT-SYMBOL (A and B); .got cell moved to the next GOT word (class A): NOT flagged, verdict SAME-SYMBOL-ROUNDED (A and B) | 3 of 4 classes PASS; the .got class FAILS: see "Limits" |

## Limits of this gate, named (and how this record covers each)

1. FALSE-EQUAL classes registered for this tool line: SAME-CONTENT across two symbols cut at a NUL; INSN-SAME for a
   jal compares opcode + rd only; ROUND-CONSTANT-SAME; PREDICT MAPS-STRING. Covered by `../false-equal/` (every row of
   those verdicts checked another way) and by `../roundconst/` and `../counts/`.
2. The named-symbol rule depends on the donor: a cell the donor already had wrong passes. The keyed runs RA / RB measured it
   on 1053 named cells per image core (0 unmeasured); RU left its 366 named cells (lib/Reusable/YH03.v, a plain-build
   file) unmeasured, because RU is keyed B.
3. MEASURED HERE: a .got cell moved to the next 16-aligned GOT word reads SAME-SYMBOL-ROUNDED (planted control above).
   Covered by `../got/` (every GOT cell's pointee checked against the donor's and against its name).
4. A BY-ADDRESS move onto an UNRELATED cell reads SAME (registry, 2026-10-30 19:51Z). Covered by `../sweep/` (donor
   symbol + offset against ours for every address-valued paired numeral).
5. codeptr 12348302dfd2 (used in `../codeptr/`): its CELL rule accepts a different symbol when the value equals the pin
   word.
6. Unpaired numerals (sentences the port wrote by hand, UNPAIRED-PORTED) are not compared with a donor by this tool;
   they are triaged below by resolving them in our image.

The later version 0d24592683b6 was run on RA, RB, PA and PB with the same inputs: `../rerun-0d24/README.md` says which
of the limits above it removes and lists every changed verdict (0 findings; the planted .got moves now fire).

## Older runs of this tool on our tree (superseded by RA / RB)

| run | when | tool version | what it did not cover |
|---|---|---|---|
| run 1's stage-out, lib/A (a lane's own check of a superseded run) | 2026-10-28 20:31Z | before 094df145c920 (first version) | interval ends, GEOM class, STALE-DONOR-CODE-POINTER, image auto-assignment and every later rule |
| lib/A -> lib/B (the image-B lane's gate) | 2026-10-29 01:16Z | 39e67a7eb166 (installed 2026-10-28 23:10Z) | STALE-DONOR-DATA-POINTER, use-context roles, donor sym+off as default, STALE-DONOR-ROUNDED, the flag gate (`--fail-on-flags`), the named-symbol rule; its stale-donor rule is unaudited against the codeptr positive control (registry) |
