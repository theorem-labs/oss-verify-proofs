# Failure handlers

`failure_handlers.tsv` has one row per harness whose `failure_handlers` fact is
`none` ([docs/facts.md](../../docs/facts.md), "Failure handlers"): the reading
that found no code linked into its binaries that can take over a failed check.
It is written by hand, from the survey that set the fact.

| column | meaning |
|---|---|
| project, harness | the harness |
| value | the `failure_handlers` value the reading supports |
| evidence | what was read: the source copy and the library at its pinned commit (the release's source archive, submodules and vendored code included), the patches, the libraries of the builder image the build links, and the toolchain runtimes, with the search run over each, what it found, and why each match is not a handler that takes over a failed check |

A change that sets `failure_handlers: none` on a harness adds its row here; one
that sets another value removes it.
