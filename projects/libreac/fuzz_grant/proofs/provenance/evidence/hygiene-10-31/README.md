# What this folder holds

The records of one series of changes to this unit's proofs, made on 2026-10-31. The series changes no statement and
proves no new function: it corrects values that were wrong of this unit's images, removes cells and text nothing
reads, and takes internal working names out of the comments.

| file | what it records |
|---|---|
| `listing-recipe.md` | how image B's three generated listing files are made, and the checks on the regeneration |
| `model-labels.md` | the allocator model's 14 labels, why they are tags and not addresses, and why no statement reads them |
| `yh03-nosym.md` | the YH03 address cells of both copies, read against each copy's own pinned image |
| `relocated-values.md` | the values carried from the donor as if they were addresses, and the ones checked and kept |
| `untimed-build.md` | the whole-unit build with no cache and no timed tactic, and its peak memory |
| `hypothesis-values.md` | the hypothesis positions whose values were audited against the images |

The tools that rewrote text also write their own records: `lane-comments-removed.tsv` and `licence-removed.tsv` here,
and `untime-removed.tsv` beside this folder, at `provenance/evidence/`, which is the path that tool reads back when it
checks its own commit.

Each record names the files and the images it was measured against. An image is named by its sha256, which is the same
hash the build's `harness.yaml` pins. A tool is named by the sha256 of the file that ran.

Some records also cite a hash of a working commit that is kept only in this project's internal records, not in this
repository; the bytes behind every such citation are preserved there, so a reader who has that record can check any
figure quoted here.
