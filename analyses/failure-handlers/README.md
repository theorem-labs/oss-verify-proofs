# Failure handlers

`failure_handlers.tsv` has one row per harness whose `failure_handlers` fact is
`none` ([docs/facts.md](../../docs/facts.md), "Failure handlers"): the reading
that found no code linked into its binaries that can take over a failed check.
`facts.py` writes an enrollment's rows from its judgement and the scan; it never
removes a row. It writes a row only when the harness has none here, or when its
row says another value; a row that already says none stays as it is, because
model text never replaces checked evidence. The scan is
`tools/enroll/ci/handler-scan`, which reads each fuzz target's binaries in the
build job; the judgement's `failure_handlers_evidence` names it as
`handlers/<harness>.txt` ([tools/enroll/JUDGEMENT.md](../../tools/enroll/JUDGEMENT.md)).
The rows before the enrollment workflow were written by hand, from the survey
that set the fact.

| column | meaning |
|---|---|
| project, harness | the harness |
| value | the `failure_handlers` value the reading supports |
| evidence | what was read: the source copy and the library at its pinned commit (the release's source archive, submodules and vendored code included), the patches, the libraries of the builder image the build links, and the toolchain runtimes, with the search run over each, what it found, and why each match is not a handler that takes over a failed check; for an enrollment, the scan `handlers/<harness>.txt` and the source files read |

A row can say none while the harness's `failure_handlers` in `harness.yaml` says
another value. Then a later judgement gave that value, and `facts.py` kept the
row for review: the facts pull request lists it, and its reviewer keeps the row
(with a revise run that gives the reason) or removes it in a reviewed commit. No
checker reads this file. A row of a harness that is no longer a fuzz target of
its enrollment stays too, and the facts pull request lists it the same way.

A pull request by hand that sets `failure_handlers: none` on a harness adds its
row here; only a reviewed commit removes a row.
