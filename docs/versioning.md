# Versions

Releases are numbered `vYYYY.M.N` by the month they are published in, for
example `v2026.10.0`; M is the month without a leading zero (`v2027.1.0`, not
`v2027.01.0`), and N counts that month's releases from 0. A release
candidate adds `-rc.K`, where K counts that release's candidates;
[release.yaml](../release.yaml) gives this one's number. A release
`v<release>` may have a source release `v<release>-src` beside it, for the
projects' source archives, their MANIFESTs and the build recipe, for example
`v2026.10.0-src`. The source release that holds the GPL and LGPL sources,
`sources-v1`, is named on its own.

A changelog marks a patch in its section heading, after the release number and
date: `## 2026.10.1 (2026-10-26), a patch release`. Keep the heading's
`## <release> ` prefix, because the release workflow finds the release notes by
it. A patch changes no statement's meaning: it is for proofs, documents,
statuses, analyses and new statements. A release that changes a statement's
meaning says in its changelog which statements' meanings changed and why, by
harness or by kind, with the count: the rows that `./oft revisions PREVIOUS`
reports as changed, re-rendered or model-changed. Each of them is at its new
revision in `index/statements.tsv`.

Tags and their assets are never moved or deleted.

A statement's identifier `project/harness/statement` is never reused. Its
**fingerprint** is a SHA-256 over what fixes its meaning, and nothing else: the
identifier, the statement's definition, the SHA-256 of each binary it names, the
SHA-256 of the code of `theories/Shapes.v` and `theories/Images.v`, the LPS
version string (`semantics.version` in release.yaml) and, for a bound, the
distribution's definitions. The code of a Rocq file is its text with each
comment, and each run of white space outside a string literal, taken as one
space. So a docstring edit in a statement file does not change a fingerprint,
and neither does an edit to a comment or to the layout of `Shapes.v` or
`Images.v`; an edit to their definitions or to a string literal in them does.
A withheld statement has no fingerprint.

While LPS is unreleased, its version string is `unreleased`. So a change of
LPS commit does not change a fingerprint, and every fingerprint of a release
candidate changes when LPS is released. Treat the revisions of a release
candidate as provisional. The LPS commit itself is in release.yaml
(`semantics.commit`), and the checker image is built from it. The fingerprint
does not hash the LPS commit or the Rocq version; `./oft revisions` compares
them (below).

A maintainer increases a statement's **revision** by one whenever its meaning
changes: after a rebuild of its binaries, a change to the code of
the shapes, a new LPS version, a new distribution, a change to its
definition (its reading or exit set), or, for an agreement statement, a
change to its project's own budget pair (project.yaml `budgets`, which its
term carries). Cite a statement as
`project/harness/statement@r<revision>`.

A fingerprint starts from the version of the way it is computed: version 2,
`oss-fuzz-theorems/statement/2`, hashes the code of `Shapes.v` and `Images.v`;
version 1, which release 2026.10.0 and its candidates used, hashed their whole
bytes. A new version changes every fingerprint and no statement's meaning, so a
release is compared with the previous one under one version:
`./oft revisions PREVIOUS`, where PREVIOUS is a checkout of the previous
release, fingerprints both trees with the same tools. Those tools would also
render PREVIOUS's statements their way, so it reads what PREVIOUS's own tools
wrote: a statement whose code in PREVIOUS's `Statements.v`, `Images.v` or
`Distribution.v` is not what the same tools render from the same facts was
re-rendered, and its meaning changed. When the name, version or commit of LPS,
or the Rocq package or version, differs between the two trees, every statement
is model-changed: its meaning may have changed though its fingerprint did not.
A statement withheld in either tree has no fingerprint, so no revision is
expected of it. A release leaves out what is held back from it, so a statement
can be absent from the previous release and present again in this one. Its
identifier is never reused, so the releases before it are named too, newest
first (by date, and on one date by release: a candidate `-rc.N` by N, and
before the release it is a candidate of; any other order compares nothing):
`./oft revisions PREVIOUS --earlier OLDER...` compares such a statement
with the newest of them that has it, and it keeps that release's revision, or
takes the next one if its meaning changed since. For each statement it says whether its meaning is the same,
changed, re-rendered or model-changed, which revision it must have, and
whether its proof carries forward, is re-checked, is retired or is new, and it
fails when a revision is not the one it must be.

Every release re-checks every proof. A proof whose statement kept its meaning
carries forward; when the fingerprint's version changed,
`./oft revisions PREVIOUS --write-pins` sets its pin to the statement's new
fingerprint, changing only the value of `fingerprint:` in `proof.yaml`. One
whose statement changed but still checks has its fingerprint
updated; any other is retired, stays in the old tag, and its statement is open
again. The changelog lists each case.
