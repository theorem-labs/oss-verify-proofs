# Cited paths outside provenance/evidence/

Some files in this directory cite paths that are not in `provenance/evidence/`. This file tells where each
of these paths is. The files that cite them are not changed. Paths are relative to `proofs/libreac/fuzz_boxreg/`.

| Cited as | Cited by | Where it is |
| --- | --- | --- |
| `provenance/OBLIGATIONS.md` | `deps-gate.py` line 2 | prover-only (on the series branch; not shipped): `provenance/OBLIGATIONS.md`. |
| `provenance/evidence/yh03/check-e5d7cbda4e27.after.plain.rows` | `yh03-rows/check-rows-vs-*.diff` line 1 | deleted in this series; the file's content was `check-e5d7cbda4e27.after.plain.rows` (sha256 ae832469f4cc; internal record). |
| `provenance/evidence/yh03/check-e5d7cbda4e27.after.ubsan.rows` | `yh03-rows/check-rows-vs-*.diff` line 6 | deleted in this series; the file's content was `check-e5d7cbda4e27.after.ubsan.rows` (sha256 3337638faf2a; internal record). |
| `OBLIGATIONS.md` | `build/README.md` line 33 | prover-only (on the series branch; not shipped): `provenance/OBLIGATIONS.md`. |
