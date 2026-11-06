# Cited paths outside provenance/evidence/

Some files in this directory cite paths that are not in `provenance/evidence/`. This file tells where each
of these paths is. The files that cite them are not changed. Paths are relative to `proofs/libreac/fuzz_boxreg/`.

| Cited as | Cited by | Where it is |
| --- | --- | --- |
| `provenance/startup-notices/` | `README.md` line 19 | prover-only (on the series branch; not shipped): `provenance/startup-notices/`. |
| `startup-notices/hsform/run.sh` | `README.md` lines 34, 36 | prover-only (on the series branch; not shipped): `provenance/startup-notices/hsform/run.sh`. |
| `startup-notices/ae3i/run.sh` | `README.md` line 40 | prover-only (on the series branch; not shipped): `provenance/startup-notices/ae3i/run.sh`. |
| `startup-notices/gen_ad1k/run.sh` | `README.md` line 47 | prover-only (on the series branch; not shipped): `provenance/startup-notices/gen_ad1k/run.sh`. |

## From the former slice MANIFEST.md

This README replaces the slice MANIFEST.md (2026-10-31); the file list and sha256 of every file are in provenance/evidence/MANIFEST.md.

### Start-up inputs, image B (fuzz_boxreg.asan-ubsan)

Byte copies of the files outside git that the start-up scripts under `provenance/startup-notices/` read for image B,
under the names the runs of record read them by. Each run.sh reads them here (repository-relative paths) and checks
every file's sha256 against its own `inputs.sha256` before it runs. The pinned images and their twins are not copied:
`harness.yaml` pins them by sha256.

A row marked CLEANED COPY is not a byte copy. The scanner flags some bytes of the original in a part that the tool
reading it does not read, so `evidence/startup-AB/scrub.py` (run by `evidence/startup-AB/scrub.sh`) wrote the copy
from the original whose sha256 the row gives, and changed only the span that the copy's record `scrub/<file>.diff`
shows (the removed text is shown there only as `<redacted>`). The row names the run.sh that was run once on the
original and once on the copy, with byte-identical outputs.

The rows of the former table, each without the sha256 of its file (the file list with the sha256 of every file is in
`provenance/evidence/MANIFEST.md`):

- `inputs/box-cgif-b-rbuild.log`: build log of the collector's pass 2 with the probe-completed tail (50 hand-off
  states): log of the image-B hs run of startup-notices/hsform/run.sh (regenerates lib/B/AB01.v)
- `inputs/fuzz_boxreg.nm.txt`: `nm` of fuzz_boxreg.asan-ubsan's unstripped twin: --names of the image-B hs run of
  startup-notices/hsform/run.sh (regenerates lib/B/AB01.v)
- `inputs/YF0m.v.prev`: CLEANED COPY of the original with sha256
  6a8225b73169fdc6bdf9fcaa956389a097c7537f8d90a71cf42f808f1c05e7e4: line 5, the notice comment of the af0m run that
  wrote it, is `(* <redacted> *)` (record scrub/YF0m.v.prev.diff). The image-B YF0m.v whose Tfib_owned_static the
  image-B ae3i run read: --owned (image B) of startup-notices/ae3i/run.sh (regenerates lib/B/AE3i.v), which reads it
  only from `Definition Tfib_owned_static` to the next `].`. Identity: ae3i/run.sh on the originals and on the copies
  wrote byte-identical outputs (lib/A/AE3i.v c7494322fd415be269ac05aa7b66d11733889c20ea834b3e27550d715b45bf57,
  lib/B/AE3i.v d3d7ad727ec0747ffaa0d9e3579a6792cd7683277dd8664d21456073710c82cc)
- `inputs/YF0m.v1base.prev`: CLEANED COPY of the original with sha256
  ded187c73ca93ef17c68975874c28b01f4edceaf36c8087463aaa0f8efe9dee6: line 5, the notice comment of the af0m run that
  wrote it, is `(* <redacted> *)` (record scrub/YF0m.v1base.prev.diff). The image-B owned-static file (YF0m.v): --owned
  (image B) of startup-notices/gen_ad1k/run.sh (regenerates lib/B/AD1k.v), which reads it only through its owned_static
  and zero_shadow definitions. Identity: gen_ad1k/run.sh on the originals and on the copies wrote byte-identical outputs
  (lib/A/AD1k.v 515715d6f528fa45125841a2676018520938c7c7608d1699c5d5e8c155e1382c, lib/B/AD1k.v
  a04e7dad9f4a4e4e7e289079603f449c3837a74fdf6e5c4c14b897a4e605819e, and both sites files)
