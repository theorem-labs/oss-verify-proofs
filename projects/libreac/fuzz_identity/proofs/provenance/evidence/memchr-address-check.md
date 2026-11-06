# MemchrDef.v address-check tables, removed from the proof files

Lane-added comment blocks removed under a lane's 19:18Z ruling (a comment line absent from the donor
file is lane-added and is removed in the comment-only commit before BASE). Donor evidence: cgif's
proofs/cgif/cgif_file_fuzzer/lib/YG0d.v at 6d085644782c carries NO address-check block in its header,
and cgif has no lib/A/Rt/MemchrDef.v at all. Nothing in the removed text is disputed.

# the removed lane-added comment blocks: index only (a lane 21:31Z).
# The verbatim text lives in an internal record, named in the PR body, and is checked by the sha256 below.

| file | lines | sha256 of the removed text |
| --- | --- | --- |
| `projects/libreac/fuzz_identity/proofs/lib/A/Rt/MemchrDef.v` | 4 | `175e88b1fcb66aed` |
| `projects/libreac/fuzz_identity/proofs/lib/B/Rt/MemchrDef.v` | 4 | `6f7d6661be2a6889` |

The verbatim text is in this series' internal record, at path `lane-comments-removed.tsv`
(sha256 `4215e54662c92263`); the attributions are at `attributions.tsv` (sha256 `94cfdfe88d7e4fc3`).
The record's ref is named in the PR body, so a reader with access checks each block by its hash.
