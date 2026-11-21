# Failure handlers

`failure_handlers.tsv` has one row per harness whose `failure_handlers` fact is
`none` ([docs/facts.md](../../docs/facts.md), "Failure handlers"): the reading
that found no code linked into its binaries that can take over a failed check.
`facts.py` writes an enrollment's rows from its judgement and the scan; it never
removes a row. A `none` row must name the library commit (or archive sha256) it
was read at ([review.md](../../review.md), check B): `facts.py` writes
`Read at <host>/<owner>/<repo>@<commit>: ` before the judgement's evidence. It
writes a row when the harness has none here, or when its row says another value.
A `none` row that names the enrollment's library commit stays as it is, because
model text never replaces checked evidence; one that names no commit gets that
pin before its evidence when the base's `library.commit` is the enrollment's,
since it was read at that commit. A `none` row read at another pin (it names
another commit, or it names none and the base's `library.commit` is not the
enrollment's) is written again from the new judgement, because old evidence
cannot stand for a new commit. `facts.py --from-tree` (a refresh, or a
hold-state run) adds the pin to a carried `none` row that names no commit when
the carried facts pin the library commit of the tree they are written onto: for
a refresh, the base's tip; for a hold-state run, which writes a tree's facts
back onto itself, whenever the project pins one. The scan is
`tools/enroll/ci/handler-scan`, which reads each fuzz target's binaries in the
build job; the judgement's `failure_handlers_evidence` names it as
`handlers/<harness>.txt` ([tools/enroll/JUDGEMENT.md](../../tools/enroll/JUDGEMENT.md)).
The rows before the enrollment workflow were written by hand, from the survey
that set the fact.

`tools/enroll/ci/ledger-pins analyses/failure-handlers/failure_handlers.tsv`,
run from the repository's root, prints each `none` row and the pin it names,
and exits 1 for a row that does not name its project's `library.commit` (or
`archive_sha256`), or, for a project with no `library` block, any commit. No CI
job runs it: a facts pull request written before `facts.py` named the pin holds
rows that would fail it.

| column | meaning |
|---|---|
| project, harness | the harness |
| value | the `failure_handlers` value the reading supports |
| evidence | what was read: the source copy and the library at its pinned commit (the release's source archive, submodules and vendored code included), the patches, the libraries of the builder image the build links, and the toolchain runtimes, with the search run over each, what it found, and why each match is not a handler that takes over a failed check; for an enrollment, `Read at <pin>: `, then the scan `handlers/<harness>.txt` and the source files read |

A row can say none while the harness's `failure_handlers` in `harness.yaml` says
another value. Then a later judgement gave that value, and `facts.py` kept the
row for review: the facts pull request lists it, and its reviewer keeps the row
(with a revise run that gives the reason) or removes it in a reviewed commit. No
checker reads this file. A row of a harness that is no longer a fuzz target of
its enrollment stays too, and the facts pull request lists it the same way.

A pull request by hand that sets `failure_handlers: none` on a harness adds its
row here; only a reviewed commit removes a row.

A release carries no row of a fuzz target the tree holds back: `oft
release-tree` rewrites this file without the rows of the tree's fuzz targets it
does not carry, and without every row of a project held back whole
(`release: private`, a library whose repository is not public among them),
whether the tree still has that fuzz target or not (`cut_handler_rows` in
[tools/oft/release_tree.py](../../tools/oft/release_tree.py)). A row of a fuzz
target the tree no longer has, of a project that ships, stays. The publication
gate (`tools/publish/verify`) refuses a release whose copy keeps a row of a
project held back whole, and both refuse a table that is not this header and
LF-separated rows whose first column is a project name. A row of a private
library may name its repository, which `oft lint` refuses in every other row.
