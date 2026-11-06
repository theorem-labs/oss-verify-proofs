# Cited paths outside provenance/evidence/

Some files in this directory cite paths that are not in `provenance/evidence/`. This file tells where each
of these paths is. The files that cite them are not changed. Paths are relative to `proofs/libreac/fuzz_boxreg/`.

| Cited as | Cited by | Where it is |
| --- | --- | --- |
| `provenance/startup-notices/` | `README.md` line 20 | prover-only (on the series branch; not shipped): `provenance/startup-notices/`. |
| `startup-notices/gen_ad1k/run.sh` | `README.md` lines 38, 44 | prover-only (on the series branch; not shipped): `provenance/startup-notices/gen_ad1k/run.sh`. |
| `startup-notices/gen_ad2/run.sh` | `README.md` lines 39, 45 | prover-only (on the series branch; not shipped): `provenance/startup-notices/gen_ad2/run.sh`. |
| `startup-notices/universe/run.sh` | `README.md` lines 40, 46 | prover-only (on the series branch; not shipped): `provenance/startup-notices/universe/run.sh`. |
| `startup-notices/hsform/run.sh` | `README.md` lines 41, 47 | prover-only (on the series branch; not shipped): `provenance/startup-notices/hsform/run.sh`. |

## From the former slice MANIFEST.md

This README replaces the slice MANIFEST.md (2026-10-31); the file list and sha256 of every file are in provenance/evidence/MANIFEST.md.

### Start-up inputs read for both images

Files that the start-up scripts under `provenance/startup-notices/` read for image A (fuzz_boxreg.asan) and image B
(fuzz_boxreg.asan-ubsan) alike. Each run.sh checks every file's sha256 against its own `inputs.sha256` before it runs.

`inputs/set/` holds the files of the start-up tool set 2026-10-30d (`tools/startup-set/2026-10-30d/` at f1417943331,
a commit outside the release) that may be committed, under their paths in the set (each is byte-equal to the file of
the same path in 2026-10-30b). The set's other files that the runs read (its tsv, frozen-run.sh, 15 frozen tool
copies and 3 pautrlen modules) carry text that the scanner flags in their comments, so they are not committed; each
run.sh reads them beside SET_TSV and runs frozen-run.sh from one directory assembled from both.

`scrub.py` writes the CLEANED COPIES of the start-up inputs listed in `startup-A/README.md` and
`startup-B/README.md`, and `scrub.sh` is its run for each of them (the originals stay outside git). scrub.py
refuses its output when the scanner of record flags the copy or its record.

The rows of the former table, each without the sha256 of its file (the file list with the sha256 of every file is in
`provenance/evidence/MANIFEST.md`):

- `inputs/set/frozen/ColA.v.frozen-d198e5a14160`, `inputs/set/frozen/tr0.py.frozen-14f49a0b2243`,
  `inputs/set/frozen/wh8.py.frozen-fe8327d6bb7e`: copied beside the tool by the set's frozen-run.sh in
  startup-notices/gen_ad1k/run.sh (regenerates lib/A/AD1k.v, lib/B/AD1k.v); copied beside the tool by the set's
  frozen-run.sh in startup-notices/gen_ad2/run.sh (regenerates lib/A/AD2i.v, lib/A/AD2j.v, lib/A/AWH8.v, lib/B/AD2i.v,
  lib/B/AD2j.v, lib/B/AWH8.v); copied beside the tool by the set's frozen-run.sh in startup-notices/universe/run.sh
  (regenerates lib/A/ACej.v); copied beside the tool by the set's frozen-run.sh in startup-notices/hsform/run.sh
  (regenerates lib/A/AB01.v, lib/A/AB03.v, lib/A/AB05.v, lib/B/AB01.v)
- `inputs/set/pautrlen/absint.py`, `inputs/set/pautrlen/rvdis.py`: linked beside the tool by the set's frozen-run.sh in
  startup-notices/gen_ad1k/run.sh (regenerates lib/A/AD1k.v, lib/B/AD1k.v); linked beside the tool by the set's
  frozen-run.sh in startup-notices/gen_ad2/run.sh (regenerates lib/A/AD2i.v, lib/A/AD2j.v, lib/A/AWH8.v, lib/B/AD2i.v,
  lib/B/AD2j.v, lib/B/AWH8.v); linked beside the tool by the set's frozen-run.sh in startup-notices/universe/run.sh
  (regenerates lib/A/ACej.v); linked beside the tool by the set's frozen-run.sh in startup-notices/hsform/run.sh
  (regenerates lib/A/AB01.v, lib/A/AB03.v, lib/A/AB05.v, lib/B/AB01.v)
- `scrub.py`: writes a cleaned copy and its record (startup-A/scrub/, startup-B/scrub/); run by scrub.sh
- `scrub.sh`: the scrub.py run for each cleaned copy, with the original's sha256
