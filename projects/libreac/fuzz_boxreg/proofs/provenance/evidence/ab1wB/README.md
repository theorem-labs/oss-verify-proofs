# Cited paths outside provenance/evidence/

Some files in this directory cite paths that are not in `provenance/evidence/`. This file tells where each
of these paths is. The files that cite them are not changed. Paths are relative to `proofs/libreac/fuzz_boxreg/`.

| Cited as | Cited by | Where it is |
| --- | --- | --- |
| `proofs/libreac/fuzz_boxreg/provenance/core-reloc/ab1wB` | `NOTES.md` line 292 | prover-only (on the series branch; not shipped): `provenance/core-reloc/ab1wB/`. It holds the same files as this directory, byte for byte (this file excepted). |

The sysconf +0xe8 row of RERUN-cmpkit-4bbd3a74be89.md writes the toolchain image's musl sysroot path as a description (scanner rule, 2026-10-31), its line 77 names the toolchain's source repository by its role, not by its name (private-data lint rule, 2026-10-31), and its lines 354, 355 and 377 name that repository by its role, without its name or its commit (private-data owner ruling, 2026-10-31); every other byte is as copied.
