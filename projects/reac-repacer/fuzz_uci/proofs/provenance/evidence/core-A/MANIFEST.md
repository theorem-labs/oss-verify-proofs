# Evidence of reac-repacer/fuzz_uci's image-A core relocation

rule 24: no function proved. One line per file: its role. Paths are repository-relative; an input that is not in the
repository is named by its sha256.

## Scripts of record and their inputs

| file | role |
|---|---|
| `run.sh` | the relocation run of record: port_core 0e4e065eab9f moves fuzz_grant's released lib (origin/ossv/recipes 25e3d17bdb50) onto fuzz_uci.asan, then `header_rule.py` rewrites the comments of WORK/stage-out; its WORK/stage-out/A files equal the lib's relocated lib/A files byte for byte (status 3: the one expected `rename-new-undeclared` row) |
| `header_rule.py` | the header rule as a post-step: undates every `Modified by <name>, <date>:` notice, turns an absolute path to a repository file into a repository-relative one, refuses a comment that still names a host path, an agent, a date or a lane branch; rewrites Rocq comments only (also run by the start-up layer's writers, provenance/startup-gen/A) |
| `overrides.tsv` | run.sh's `--override` rows (file, donor line, old value, new value), each group with its measured reason |
| `zero-shadow-forallb.patch` | run.sh's `--patch`: the Tfib_zero_shadow case splits become forallb checks (libreac/fuzz_decode's patch, commit 1148f2311f8, re-cut against this run's stage-out) |
| `cell-lookup.patch` | run.sh's `--patch`: the AFim / AFin const-cell lookups by index become cell_lookup_In (libreac/fuzz_decode's patch, re-cut) |
| `ad1q-shape.patch` | run.sh's `--patch`: A/AD1q.v takes fuzz_uci's own plain-side lib_shape instance checksum_shape (lib/ZTraceSpec.v) in place of fuzz_grant's grant_shape |
| `core-files-uci.txt` | run.sh's `--files`: port_core 0e4e065eab9f's core-files.txt minus YI0j, YO08 and the leaf walks A/AE2r, AE6t, AE6u, AE6v, AE2s, AE2z (functions fuzz_uci.asan does not link) |
| `not-relocated-startup-layer.txt` | run.sh's `--no-stage` list: the start-up layer, generated for fuzz_uci's own image (provenance/startup-gen/A) |
| `taken-by-path.txt` | the one file taken by path, not relocated: Reusable/YImgTop.v (IMG_LO 0x10000, IMG_TOP 0x5f4000) |
| `versions.txt` | sha256 of port_core.py, resolve_code.py, gen_traces.py, adapted.patch and the symbol gate of the port_core release run.sh uses |

Inputs of run.sh that are not in this directory: the port_core release (`tools/pg-reloc/0e4e065eab9f` at commit
7f0e4b05267), fuzz_grant's released lib (origin/ossv/recipes 25e3d17bdb50, normalised as run.sh says), the images
fuzz_grant.asan (pin c2c7559b29bd), fuzz_uci.asan (pin 6ea017c24525), its unstripped twin (pin 56822e263d76) and
fuzz_uci.asan-ubsan (pin a1b86e424add), and fuzz_grant.asan's symbol list
`provenance/core-reloc/A/fuzz_grant.asan.syms.txt` (pin b46268790c46, libreac/fuzz_decode's file). run.sh checks
each pin before it runs.

## Tables

| file | role |
|---|---|
| `v10-donor-lines.tsv` | v10 global_settings 439f8e3bd463 over lib/ of a8fc5eedae69: every settings row in a file this core adds, with the identical line of its released donor file and that file's line number |

The one UNMEASURED core line of v10: `lib/Reusable/YG0f.v:89` `Arguments shadow_addr _ : simpl never.` = fuzz_grant's
released `lib/Reusable/YG0f.v:88` at 25e3d17bdb50 (a donor line, unchanged by the relocation).

## Gate records

| file | role |
|---|---|
| `gate-cb0e-flagged.txt` | the symbol gate's summary (port_addr_check cb0e067e3bae `--paired-only --fail-on-flags` on the run's stage / stage-out): `FLAGGED 368 rows in 10 classes`; the last 2 and the first 3 lines of the gate's output, from a run in a directory that holds `stage`, `stage-out`, `bin/`, `unstripped/` and `donors` (the command is its last line) |
| `gate-cb0e-triage-rows.tsv` | one row per flagged row of the gate: its line in the gate's raw.tsv, reason id and measurement |
| `gate-cb0e-TRIAGE.md` | the triage of the 368 flagged rows and the 6 GENERATOR-FILL rows, each with a measured reason; defects: none |
| `gate-e165-flagged.txt` | the symbol gate of record re-run (port_addr_check e165063a0081 `--paired-only --fail-on-flags` on the run of record's stage / stage-out): `FLAGGED 306 rows in 9 classes`, FLAG-CLASSES 575d398c6022, GENERATOR-FILL 6 |
| `gate-e165-TRIAGE.md` | the e165 rows against the cb0e triage: 302 unchanged (earlier reasons by reference), 4 new (two patch lines' granule 8 / remainder 0, no address role), 66 gone (46 patch rows now paired by identical text; 20 SAME-VALUE-DIFFERENT-OBJECT rows from kept Reusable/ files, re-flagged identically in a control run with Reusable/); defects: none |
| `gate-e165-triage-rows.tsv` | one row per e165 flagged row with its reason or its cb0e reference |
| `DECIMAL-VALUES.md` | the by-value check (libreac/fuzz_decode's method): 8519 numerals in 569 relocated files, 0 DONOR-STALE; a planted fuzz_grant value is caught |
| `decval.py` | the by-value check, stage 1 (alignment with the donor text, image bytes, symbol values of both images) |
| `decval_extra.py` | the by-value check, stage 2 (image evidence for every row stage 1 leaves to a look by hand) |
| `MANIFEST.md` | this list |
