# Analyses

- [index/PROOFS.md](../index/PROOFS.md): every entry point that has a proof,
  with the statements proved, the system-call failures they allow, the build
  record and the proof. `index/proofs.tsv` has one row for each proved
  statement.
- [analyses/harness-checks/checks.tsv](../analyses/harness-checks/checks.tsv):
  every check recorded for a harness beyond not crashing, one row each
  ([README](../analyses/harness-checks/README.md)). The record is not complete
  yet: it does not list the length checks of coturn or the nesting checks of
  yajl-ruby, which [exploring.md](exploring.md) describes.
- [analyses/failure-handlers/failure_handlers.tsv](../analyses/failure-handlers/failure_handlers.tsv):
  for each harness whose `failure_handlers` is `none`, what was read to find
  that no linked code can take over a failed check
  ([README](../analyses/failure-handlers/README.md)).
- [analyses/known-issues.md](../analyses/known-issues.md): every statement that
  is not open or proved, with the reason.
- [index/](../index/): `projects.tsv`, `harnesses.tsv`, `statements.tsv` and
  `binaries.tsv`, the same data as the pages, for scripts.
