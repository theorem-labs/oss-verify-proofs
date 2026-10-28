# Where the proofs come from

The proofs were written by automated proving systems: language-model agents
that write Rocq proof scripts. The agents worked against a checker, which this
page describes. For this release, `oft check` checks every proof again, in the
checker image ([checking.md](checking.md)). A proof is accepted because the
Rocq kernel checks it, not because of who or what wrote it.

## The proving task

The proofs were written for a proving task that we set up. For each library,
the task fixes:

- a commit of the library's upstream repository;
- one or more entry points, each one an OSS-Fuzz fuzz target of the project;
- for each entry point, a plain build and up to three sanitizer builds, all
  static riscv64 Linux programs;
- a statement file that states every theorem the task asks for, each one
  ending in `Admitted.` (the *skeleton*);
- a checker. It compiles a submission against LPS and the statement file. It
  accepts a theorem only at the type that the statement file gives it. It
  refuses every assumption outside an allowed list.

A *submission* is a directory of Rocq files (the task calls it
`AgentSubmission`) whose `Proof.v` replaces some `Admitted.` with proofs. The
agreement statement for the ASan build has the theorem name
`strong_universal_error_free_<name>_asan`, and likewise `_ubsan` and `_both`
for the other builds. `<name>` is the task's name for the entry point. It is
not always the fuzz target's name: for boost-beast `http_request` it is
`boost_beast`.

## How a proof enters this repository

This repository has the same parts, in its own layout:

| in the task | in this repository |
|---|---|
| the statement file | `projects/<project>/<harness>/Statements.v`, rendered from the facts by `oft generate` ([statements.md](statements.md)) |
| a submission | `proofs/<project>/<harness>/lib/`, and one directory for each statement, `proofs/<project>/<harness>/<statement>/` |
| the task's checker | `oft check`, with the wrapper that it writes and its audit of `Print Assumptions` ([checking.md](checking.md)) |
| the task's binaries and tools | the binaries attached to the release, and the checker image |

To enter, a proof must prove this repository's statement about this
repository's binaries, in the LPS version that [release.yaml](../release.yaml)
names. Many proofs were first written against earlier builds of the same
programs. We adapted them to the binaries and the LPS version of this release,
and checked them again. The adapted proof keeps the task's theorem names in
`lib/`, for example `strong_universal_error_free_fuzzstunclient_asan`. The short
`Proof.v` in each statement's directory proves the statement from that theorem.
Then `oft check` gives the result the statement's type and audits its
assumptions.

Each proof also gets a build record of its binaries, in
`proofs/<project>/<harness>/provenance/` ([building.md](building.md#where-a-binary-comes-from)).
The record says where the proofs of the fuzz target came from (`proofs.origin`
in `PROVENANCE.yaml`). A fuzz target that came from a package may also hold
proofs written in this repository: `proofs.written_here` names their
statements, one line per source, as `approvals.yaml` lists them.
[adding-a-proof.md](adding-a-proof.md) lists every requirement that a proof
meets before it enters.

## Licences of the proof files

We wrote some proofs ourselves. We made others from proofs that Anthropic
wrote for the same task and licensed under the Apache License 2.0 or the MIT
licence, at the recipient's option. A file of such a proof keeps its licence
header, and a file that we changed has one more line under the header that
says so ([licensing.md](licensing.md)).
