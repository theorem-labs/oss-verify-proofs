# A/AF0w.v: no E7 line (named-exception condition (i) fails) — STOP, back to the ruling

The fuzz_grant release re-probe (zify-flag-grant-release.tsv) reads AF0w's Zify flag as `true` at the
release and `false` in this unit's closure (zify-flag-before.tsv), which made AF0w an E7 candidate. AF0w is a composition
file (#21 of composition-files.txt), so an E7 line there is a named exception to grown-class condition (a), allowed
(ruling 00:31Z) only if five conditions hold. Condition (i) requires the line to be byte-equal to a line in fuzz_grant's
RELEASED A/AF0w.v at 4f87de75d677, so that it restores the release value rather than inventing one.

Measured: fuzz_grant's released A/AF0w.v (4f87de75d677, 49 lines) has NO Zify flag line at all; its `true` comes from its
Require closure, not from a line of its own. So (i) cannot hold literally, and per the ruling this is a STOP: the line
is NOT in this commit, and the fact goes back to the ruling.

The build does not need the line: build #31 (cb-cache restored, rc 0) compiled A/AF0w.v without it, and the
CACHE=none --fresh build of this commit (see the commit message) compiles it without it. AF0w's text in this commit is
byte-identical to 4483a8de6e6f. The E7 set of record is therefore 14 files (zify-flag-record.tsv), not 15.

Why no line is needed (ruling 04:01Z, accepted): the Zify flag changes only how `lia` searches for a proof (whether it
first rewrites Z.div / Z.modulo into Euclidean equations); it never changes a statement or what the kernel checks, so it
cannot change what a file proves, only whether a proof script finds its proof. A/AF0w.v has exactly two `lia` goals
(A/AF0w.v:35 and :36, in amalloc_realizes_of: `ltac:(lia)` for the size split of n, from `Z_le_gt_dec n 64512` and the
premise `64513 <= n < MALLOC_MAX`); both are linear and hold no Z.div or Z.modulo, so the flag cannot affect them.
AF0w compiles without a line (the CACHE=none --fresh build of 78d6988b23aa), and its Print Assumptions rows (4
theorems) are equal to grant's release rows in pa-wire.tsv / pa-grant-release.tsv.

