# Cited paths outside provenance/evidence/

Some files in this directory cite paths that are not in `provenance/evidence/`. This file tells where each
of these paths is. The files that cite them are not changed. Paths are relative to `proofs/libreac/fuzz_boxreg/`.

| Cited as | Cited by | Where it is |
| --- | --- | --- |
| `provenance/startup-notices/` | `README.md` line 20 | prover-only (on the series branch; not shipped): `provenance/startup-notices/`. |
| `startup-notices/hsform/run.sh` | `README.md` lines 35, 58, 61, 63 | prover-only (on the series branch; not shipped): `provenance/startup-notices/hsform/run.sh`. |
| `startup-notices/gen_ad1k/run.sh` | `README.md` line 40 | prover-only (on the series branch; not shipped): `provenance/startup-notices/gen_ad1k/run.sh`. |
| `startup-notices/ae3i/run.sh` | `README.md` line 41 | prover-only (on the series branch; not shipped): `provenance/startup-notices/ae3i/run.sh`. |
| `startup-notices/universe/run.sh` | `README.md` lines 49, 53, 57 | prover-only (on the series branch; not shipped): `provenance/startup-notices/universe/run.sh`. |

## From the former slice MANIFEST.md

This README replaces the slice MANIFEST.md (2026-10-31); the file list and sha256 of every file are in provenance/evidence/MANIFEST.md.

### Start-up inputs, image A (fuzz_boxreg.asan)

Byte copies of the files outside git that the start-up scripts under `provenance/startup-notices/` read for image A,
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

- `inputs/AB05.v`: image A's plan with startup_plan_tfib relocated and startup_plan_tfib_ranges re-derived, before the
  tail insert: the plan that plantail.py and ab05.py complete in startup-notices/hsform/run.sh (regenerates
  lib/A/AB05.v)
- `inputs/AF0m.v.prev`: CLEANED COPY of the original with sha256
  f2a61027cb7496dfe51f2ba64433b825ed6b4cd08a4abf1276a22ec2b22bcac4: line 5, the notice comment of the af0m run that
  wrote it, is `(* <redacted> *)` (record scrub/AF0m.v.prev.diff). The image-A owned-static file (AF0m.v, base v5):
  --owned (image A) of startup-notices/gen_ad1k/run.sh (regenerates lib/A/AD1k.v), which reads it only through its
  owned_static and zero_shadow definitions; --owned (image A) of startup-notices/ae3i/run.sh (regenerates lib/A/AE3i.v),
  which reads it only from `Definition Tfib_owned_static` to the next `].`. Identity: gen_ad1k/run.sh on the originals
  and on the copies wrote byte-identical outputs (lib/A/AD1k.v
  515715d6f528fa45125841a2676018520938c7c7608d1699c5d5e8c155e1382c, lib/B/AD1k.v
  a04e7dad9f4a4e4e7e289079603f449c3837a74fdf6e5c4c14b897a4e605819e, and both sites files); so did ae3i/run.sh
  (lib/A/AE3i.v c7494322fd415be269ac05aa7b66d11733889c20ea834b3e27550d715b45bf57, lib/B/AE3i.v
  d3d7ad727ec0747ffaa0d9e3579a6792cd7683277dd8664d21456073710c82cc)
- `inputs/decisions.fuzz_boxreg.asan.json`: the hand decision of the WILD site 0x8139c: --decide of
  startup-notices/universe/run.sh (regenerates lib/A/ACej.v)
- `inputs/fuzz_boxreg.asan.compose.json`: CLEANED COPY of the original with sha256
  d6e2a5d74f39a33e1eedfab696767b1002169c20d7d5a71087f93b4dd55fc5a3: the value of its "img" member, the image's host path
  when the composer ran, is "<redacted>" (record scrub/fuzz_boxreg.asan.compose.json.diff). pautrlen/compose.py's
  CTXALL=1 output over fuzz_boxreg.asan: the compose input of startup-notices/universe/run.sh (regenerates
  lib/A/ACej.v), which reads only its "results", "ipc" and "ctxs" members. Identity: universe/run.sh on the original and
  on the copy wrote byte-identical outputs (lib/A/ACej.v
  61f53f59050b3d31abe3ab5af68fd7006f465dd367099624eb023949dca4fcc5)
- `inputs/fuzz_boxreg.nm.txt`: `nm -S` of fuzz_boxreg.asan's unstripped twin: --names of startup-notices/universe/run.sh
  (regenerates lib/A/ACej.v); --names of the image-A hs and js runs of startup-notices/hsform/run.sh (regenerates
  lib/A/AB01.v, lib/A/AB03.v)
- `inputs/pass1.rerun.partial.log`: build log of the collector's pass 1 (the join state): log of the js run of
  startup-notices/hsform/run.sh (regenerates lib/A/AB03.v)
- `inputs/pass2.real.build.log`: build log of the collector's pass 2 with the probe-completed tail (50 hand-off states):
  log of the image-A hs run of startup-notices/hsform/run.sh (regenerates lib/A/AB01.v)
