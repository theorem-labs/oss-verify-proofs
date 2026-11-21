# The .v tree the CACHE=none --fresh build compiled

(1) There is no `git status --porcelain` taken at the 04:02Z build start.

(2) Every .v that cb synced for the 04:02Z build equals's blob. The build ran in the build VM's workspace
clone of this worktree (cb's CACHE=none route, `1635 files, jobs 32, targets: all`); cb's sync check at the start
says that clone held the worktree by content (`rsync -c --dry-run after the sync: no difference`). Measured in that
clone after the build: the sha256 of the bytes of each of its 1,635 .v files under proofs/reac-repacer/fuzz_wire equals
the sha256 of the same path's file (1,635 of 1,635 equal, 0 missing, 0 extra;
fresh-build-v-files.tsv, written by fresh_build_file_sha.py beside it: `hash` in the clone, then `table`).
The copy was not touched after the sync: the newest .v mtime is the sync (04:02:34Z), no
.v is newer than 04:02:40Z, all 1,635 .vo were written between 04:02:54Z and 04:38:55Z, and no .vo is older than its
.v. So the tree the build compiled is's .v tree; the clean-clone rebuild of step (3) is not needed.

Supporting fact, measured at 04:50Z in the local worktree, HEAD: `git status --porcelain` empty, 0 tracked
.v differing, 0 untracked .v.

Print Assumptions against the build's own .vo files: the 22 probe files (the 21 composition files and A/AE37.v) compiled
against that clone, 227 theorems, 0 without output, equal row for row to pa-wire.tsv (0 differ). (The earlier
re-check ran against the build directory of the cached route, whose composition files are the same blobs.)

Review of record: REVIEW5.md, section `FINAL (04:5xZ): APPROVE (head)`, verdict
"APPROVE fuzz_wire image A core (head, evidence-only above it)".

From now on, every build of this unit records `git status --porcelain` at the build start.
