# Library files copied byte for byte

Written by hand; not generated from `PROVENANCE.yaml`. Each file below is in this tree exactly as its donor has it
(same git blob), so its text, including any global settings it makes, is the donor's. It is recorded here, not in
the file, so that the file stays the donor's blob and nothing that Requires it recompiles for a comment. All six come
from one donor commit of the frame relocation for fuzz_command; on 2026-10-29, `git hash-object` of each of our files
matched the donor's blob id. Each cell of the table is the sha256 of our file's bytes, and the released plugin-hostd/fuzz_command holds the same bytes at the same path (checked 2026-10-31).

| our path (proofs/plugin-hostd/fuzz_command/) | file sha256 (12) | note |
|---|---|---|
| lib/A/Bz/Lib/LiaTuning.v | file sha256 6c7c90225363 (released) | byte for byte; its global settings are the donor's text (from the shared ASan runtime proofs) |
| lib/A/Bz/Lib/StepFast.v | file sha256 2578eb4954d4 (released) | byte for byte; its global settings are the donor's text (from the shared ASan runtime proofs) |
| lib/A/Bz/Lib/Tac.v | file sha256 10af2be4c516 (released) | byte for byte; its global settings are the donor's text (from the shared ASan runtime proofs) |
| lib/B/Bz/Lib/LiaTuning.v | file sha256 50327f41ddc7 (released) | byte for byte; its global settings are the donor's text (from the shared ASan runtime proofs) |
| lib/B/Bz/Lib/StepFast.v | file sha256 f143cb5935d1 (released) | byte for byte; its global settings are the donor's text (from the shared ASan runtime proofs) |
| lib/B/Bz/Lib/Tac.v | file sha256 cfe8d0c189f5 (released) | byte for byte; its global settings are the donor's text (from the shared ASan runtime proofs) |

The shared ASan runtime proofs also hold the same six blobs. The settings these files make (found by the
global-settings check v8): LiaTuning.v `#[global] Set Default Proof Mode`, `#[global] Unset Lia/Nia/Nra Cache`, two
Zify cleanup redefinitions and `Ltac lia ::=`; StepFast.v two lines at the end; Tac.v seven lines. No lib/A/Prog file
and not ACfn.v Requires LiaTuning.
