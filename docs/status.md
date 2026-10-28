# What the statuses mean

Every project has exactly one project status, every fuzz target of an available
project has a harness status, and every statement has a statement
status. The lists are closed: `oft lint` refuses any other value, and each
reason sentence on a project page comes from [tools/oft/phrasebook.yaml](../tools/oft/phrasebook.yaml),
filled in only from the project's typed facts.

## Project statuses

## available
Built, and listed in this release with its harnesses and their statements. The
binaries are attached to the release unless they are withheld: a project whose
every build is withheld is still available, its statements are listed by name,
and [index/STATUS.md](../index/STATUS.md) shows its binaries as withheld. The
project page lists every fuzz target OSS-Fuzz runs and every one OSS Verify
builds, and says for each one that has no statements why not.

## language-pending
The fuzz targets are in a language this release does not cover yet (Python,
Java and other JVM languages, Go, Rust, JavaScript, Ruby). This release covers
C and C++, and Rust and Python only for the projects whose fuzz targets OSS
Verify builds ([building.md](building.md#rust-fuzz-targets),
[building.md](building.md#python-fuzz-targets)).


## not-yet-built
A C or C++ project with no binaries in this release. The reason is recorded
where it is known: a build system, a harness framework, a dependency or a
compiler that the toolchain does not have yet, a fuzz target that reads
standard input or takes its target from an environment variable, or a harness
whose set-up fails in this build. "Not built yet." means that nobody has
recorded one.

## needs-model
No binaries were built for this release because the harness uses
operating-system features that LPS does not cover yet, such as threads or
`epoll`. Compare "blocked by the model" below: there the binaries were built
and published, and their statements are listed, but their halts and agreement
statements are false in LPS for the same kind of reason.

## no-compiler
There is no compiler for the project's language that targets riscv64 Linux.

## no-harness
There is no fuzz target to build: OSS-Fuzz lists no fuzz target for the project
at the pinned commit, or the repository that holds its harness can no longer be
cloned.

## excluded
Left out on purpose: the fuzz target duplicates another project's, is an empty
stub, replaces `malloc` itself, debugs a second process, or is only copies of
other projects' fuzz targets.

## withdrawn
Had statements in an earlier release. Its identifiers are never reused.

## held
Held from this release. The page gives the reason where it is recorded. For
example, a project is held when its build compiles code that carries no licence
grant at the commit used, because its binaries could not be published.

## Harness statuses

A fuzz target of an available project is either **included** (it has a
directory with statements) or **not included**, with a reason: not built yet,
built but not included yet, built but too many binaries for the project's one
binary archive in this release, held from this release, needs model support, or
written in a language this release does not cover.

A project's API driver (`api-driver/`) is a program written for this repository
that runs its input as a sequence of calls into the library. It is not one of
OSS-Fuzz's fuzz targets, and its statements say nothing about them except
through the library code they share. Its source is not in this release yet.

## Statement statuses

| status | meaning |
|---|---|
| open | nobody has proved or refuted it |
| proved | a proof under `proofs/` that CI checked against this revision of the statement |
| refuted | a Rocq proof of the statement's negation, checked the same way |
| counterexample | a failing run of the real binary, re-run by CI under the pinned runner, next to a control input that exits with a status the statement allows |
| false (witnessed) | a recorded run of the published binary, in an environment the statement allows, that ends in a way the statement forbids; the page describes the run (the input file, which memory request was refused, how the build ended, and what ran it); not yet re-run by CI |
| suspected false | an argument from reading the source, not yet a run or a proof |
| blocked by the model | the binary does something on the inputs the statement covers that this release's LPS does not cover. A halts or agreement statement is then false in LPS for that reason alone. A bound or decidability statement says nothing useful until LPS covers the feature |
| withheld | not in this release: its binary waits for its complete corresponding source (a GPL or LGPL licence), or it is not published yet |
| withdrawn | kept in the index; its identifier is never reused |

`proved`, `refuted` and `counterexample` are never written by hand: `oft
generate` derives them from `proofs/` and `counterexamples/`.

A counterexample can also refute agreement statements. Take a counterexample in
which a build dies by a signal (an abort, a crash or a trap) with nothing
refused. That run reaches an error, so it also refutes every agreement
statement of the same harness that names that build, unless that statement is
withheld or blocked by the model. Those statements are marked counterexample
too, and point at the same run.

A counterexample, or a witnessed run, shows a statement false only as far as
qemu agrees with LPS; a refutation shows it in Rocq.

Every known-false status says what refutes the statement. A witnessed run is
one of two kinds. In the first, the environment refuses one memory request (the
page says which), and the run then ends in an abort or a crash. Such a run
refutes every agreement statement that names the build and lets the
environment refuse any request, and the build's `_halts_may_fail` statement
where it has one: those statements allow that refusal and forbid the abort or
crash. In the second, the run refuses nothing: given one input file, the build
exits with a status that its halts statement does not allow, or a UBSan check
traps.

Withheld statements and builds carry their reason. **Waits for its source
bundle**: the binary links a library under a GPL or LGPL licence, and is
attached only together with its complete corresponding source, which this
release does not have yet ([licensing.md](licensing.md)). **Not in this release
yet**: anything else that is held back. A withheld build shows no size or
SHA-256, and a withheld statement has no fingerprint.

"Blocked by the model" is a lower bound. A harness is marked when its binaries
were seen to leave LPS on sample inputs. Sample inputs cannot reach every path,
so some open statements may be blocked in the same way. Where only some
statements of a harness are blocked, each blocked statement carries its own
`gap`, the feature that LPS does not cover, and the others stay as they are. A
harness whose libraries run
vector instructions when the processor advertises the vector extension instead
has its pair statements stated only for inputs whose machine is RV64GC
(`machine: rv64gc`).
