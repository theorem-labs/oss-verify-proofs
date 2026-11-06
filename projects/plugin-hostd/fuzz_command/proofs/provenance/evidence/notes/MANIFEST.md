# provenance/evidence/notes: two provenance notes written by hand for plugin-hostd/fuzz_command

Each file below records a fact about this unit's proof tree that its .v files do not carry in a comment.

| file | sha256 | role |
|---|---|---|
| copied-byte-for-byte.md | 250fecd76a32d5cee88b172919b980b0aad9aa2c7dc69c8cfbd7a7c3a580c1eb | the six library files (lib/A/Bz/Lib and lib/B/Bz/Lib LiaTuning.v, StepFast.v, Tac.v) that are in this tree byte for byte as their donor has them (same git blob), and the global settings that the donor text makes |
| self-jumps.md | 29bd0fe229e0e20a5ef93666b4c7d36104eaf77665ea9c4c48c43806a6b73714 | the self-jumps of the two ASan images (fuzz_command.asan and fuzz_command.asan-ubsan) and the stops_more lists of lib/A/AB12.v and lib/B/YB12.v: the decision, the measurement (25 sites per image, six methods) and the gates run on the 12-entry tables |
