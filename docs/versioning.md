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

The third number counts the releases of that month. It says nothing about what
a release holds. A release that adds a library, a proof, a document, a status
or an analysis, and a release that changes a statement's meaning, are numbered
the same way. A changelog section uses the release number and its date:
`## 2026.10.1 (2026-10-26)`. Keep the heading's `## <release> ` prefix, because
the release workflow finds the release notes by it. A release that changes no
published statement's meaning says so in its section. A release that changes a
statement's meaning says in its changelog which statements' meanings changed
and why, by harness or by kind: the rows that `./oft revisions PREVIOUS`
reports as changed, re-rendered or model-changed. Each statement is at its new
revision in `index/statements.tsv`.

Each publication from the internal repository is one public commit and one
release. A project publication carries the projects that changed since the
previous public commit, so there can be several releases a day, each for one
or a few projects, rather than one release of everything.

A full release `v<release>` becomes the repository's Latest release unless a
newer full release is already published. A `-src` release and a release
candidate never become Latest. When GitHub publishes a release, it notifies
people who watch releases. During a platform release, the workflow retires a
held proof that fails its new checks. The changelog lists each proof it retires.

Tags and their assets are never moved. A release can be withdrawn, which
deletes its GitHub release and its tag. Release 2026.10.2 is withdrawn, as the
changelog section of 2026.11.0 says.

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
The two theories are hashed with the release's Rocq namespace (`namespace` in
release.yaml, `OssFuzzTheorems` while it names none) read as `OssFuzzTheorems`
wherever it starts a dotted path, so a release that renames the namespace
states the same statements and every proof's pin holds. A withheld statement
has no fingerprint.

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
fails when a revision is not the one it must be. With `--write-revisions` it
writes the revision each statement must have into `harness.yaml` instead (a
`revision:` line after `status:`, and no line for revision 1), and names the
render to run next: `index/statements.tsv` lists each revision. PREVIOUS and
each OLDER must then be checkouts of releases: against any other commit, the
revision it writes is wrong. A release is a tree that `./oft release-tree`
cut, and the cut removes `approvals.yaml`, `review.md` and the other files
only this repository has. So with `--write-revisions` the tool compares
nothing when PREVIOUS or an OLDER holds one of them. It also writes nothing
when a new statement's revision is above 1: such a statement can be one that
the previous release held back, and naming with `--earlier` the release that
has it gives its revision. If no release has it, remove its `revision:` line.

A publication checks each part whose content key differs from the previous
public commit. The key of each proof's check holds the checker, `theories/`,
the allowed axioms and the checker image, so a release that changes one of them
checks every proof. The weekly workflow (`weekly.yml`, every Monday at 03:17
UTC) checks every proof again, including the proofs that no publication
changed. A proof whose statement kept its meaning carries forward; when the
fingerprint's version changed,
`./oft revisions PREVIOUS --write-pins` sets its pin to the statement's new
fingerprint, changing only the value of `fingerprint:` in `proof.yaml`. One
whose statement changed but still checks has its fingerprint updated; any other
is retired, stays in the old tag, and its statement is open again. The
changelog lists each case.

A change to the code of `Shapes.v` moves every fingerprint, and, since
`theories/` is part of the key of every proof's check, the next corpus run
re-checks every proof. After such a change,
`./oft revisions PREVIOUS --repin-changed` also sets the pin of each re-checked
or new proof that holds its statement's fingerprint in PREVIOUS. Never use it
to hide a proof that failed. PREVIOUS may then be a commit that is not a
release, such as a proof branch's base before the change. Only the pins count
in that run: its revision errors and its exit status compare with that commit,
not with a release, so ignore them and do not add `--write-revisions`.
