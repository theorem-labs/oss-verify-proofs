# What the statements say

This page explains the statements under `projects/`. The proofs under
`proofs/` prove some of them; [index/PROOFS.md](../index/PROOFS.md) lists
which.

Every statement under `projects/` is a definition in a harness's
`Statements.v`. Most have the form `Definition <name> : Prop`. A bound
statement takes its bound first: `Definition <name> (b : Q) : Prop`. Each
definition applies one of the shapes in [theories/Shapes.v](../theories/Shapes.v)
to the memory images of that harness's binaries. Each agreement shape and each
halting shape is proved equal, by `reflexivity`, to the LPS definition that it
stands for. So what `Shapes.v` says is exactly what LPS means. The other shapes
are built from LPS definitions only. A statement file admits nothing and adds
no axiom. Whether a statement is open, proved or false is recorded in the
harness README, never in the `.v` file.

Each harness has up to four builds: `plain`, `ubsan` (UndefinedBehaviorSanitizer;
a failed check traps), `asan` (AddressSanitizer; a report aborts) and
`asan-ubsan` (both; its statements and image are named `asan_ubsan`). A few
harnesses have only `plain` and one sanitizer build. In a Rust harness, `ubsan`
means rustc's UB checks, whose failure exits with status 79 after naming its
source location on standard error, with UndefinedBehaviorSanitizer only in the
C code its crates build. In a Python harness, the sanitizers instrument the C
code: CPython, which runs the Python code as bytecode, the port's interpreter
host and the driver. There an uncaught Python exception other than a
`SystemExit` or a `MemoryError`, a failed check of the harness included, exits
with status 79 after naming its source line on standard error.
[building.md](building.md) gives the flags of each build and the checks it makes.

Statements quantify over every valid process input (the arguments, the
environment, the file system, standard input, the identities and the limits)
and over every valid launch of the binary ("Vocabulary" at the top of
`Shapes.v`, and [semantics.md](semantics.md)). The fuzz bytes are the payload
of the input file, after the driver's header. The header is six bytes when it
carries no configuration ([running.md](running.md)). The driver refuses some
inputs and exits with status 2 without calling the fuzz target: a wrong
argument count, a missing or unreadable file, a file shorter than its header,
or a file of 64 MiB or more. Every halts statement allows status 2, so these
inputs are covered too.

## Which statements a harness has

A fuzz target has a halts statement for each of its builds, a
`_halts_may_fail` statement for the plain and UBSan builds where one was
stated, and an agreement statement for each sanitizer build. Where the harness
has an input distribution (`Distribution.v`), each sanitizer pair also has a
bound statement and a decidability statement. So a harness has between 5 and
15 statements. No harness in this release is an API driver.

## Halting: `<build>_halts`, `<build>_halts_may_fail`

`plain_halts` (shape `halts_within_budget`) has two premises. The build is
never refused memory for exceeding 16 GiB, and the environment refuses nothing
that the process's state does not force. On every input that meets them, every
execution exits with an allowed status: status 0 or 2 for most harnesses, and
any status for espeak-ng's `ssml-fuzzer`. So no execution of a covered input
runs forever, crashes, fails an assertion or a sanitizer check, or leaves LPS.
Nothing is said about output.

Status 78 means that a call of the fuzz target returned a value other than 0
or -1. libFuzzer's documentation reserves those values, and a libFuzzer built
without assertions treats them as -1: the input is turned away, and nothing is
reported. Some fuzz targets return 1 to turn away an input they do not take,
for example one outside a size range. Where a harness.yaml lists those places
(`rejects`), its halts statements with a finite exit set allow 78 too: status
0, 2 or 78. The
status does not say which line returned, so in such a harness every return of
a value other than 0 or -1 is allowed, including one from a check that reports
a failure by returning (`stops_with: return-only`). Such a check binds no halts
statement in any harness (`binds_checks`), and the harness's page names it
beside the inputs turned away. A fuzz target that returns a value other than 0
or -1 only to report a failure lists no `rejects`, and its halts statements
with a finite exit set do not allow 78.

In this release no harness lists `rejects` yet. So a fuzz target that returns
1 to turn an input away still has halts statements that do not allow 78, and
those statements are false on such an input. A later release lists their
`rejects` and restates those statements.

Status 77, a call of `exit()` from the fuzz target, is allowed by no halts
statement with a finite set. libFuzzer's documentation says that a fuzz target
must not call `exit()` on any input, and libFuzzer reports such a call as a
crash ("fuzz target exited").

The 16 GiB is a premise. An input on which the build needs more memory is not
covered, and the statement says nothing about it. It is not a claim that the
build uses at most 16 GiB.

Where the harness checks a property, the check is in the binary, and a failed
check ends the process, a proof of its halts statement proves that property for
every input that the statement covers. The harness README names the checks
this covers: those seen in the binary, that no linked code can end with a status
of its own, and, where the check fails by calling `exit()`, whose `exit()`
reaches the driver's guard ([facts.md](facts.md), "A check" and "Failure
handlers").

`plain_halts_may_fail` (shape `halts_may_fail`) is stronger in one way. Every
execution exits, with any status, even when the environment may refuse any
request at any time, and there is no memory premise. It is stated only for the
plain and UBSan builds. The AddressSanitizer runtime spins forever when its
start-up reservation is refused, so such a statement about an ASan build would
be false for a reason that has nothing to do with the harness. Many harnesses
abort on purpose when an allocation fails. Their agreement statements use the
alloc-forced-only variant below, and most of them have no `_halts_may_fail`
statement.
So does every Python harness: CPython ends with `abort()` (a fatal error) when
some allocations it makes while it starts are refused.

## Agreement: `<build>_agrees`

`asan_agrees` (shape `agrees`) has one premise: the plain build is never
refused memory for exceeding its budget. On every input that meets it, and
whatever the environment refuses in either build:

- no execution of either build faults, aborts or leaves LPS; and
- the two builds have the same set of finite traces. A trace is the bytes read
  and written on the standard streams and on connections, in order, ending with
  the exit status and the final contents of the files if the run ends. A write
  to a regular file is compared through the final file contents.

A sanitizer report ends the process, so a proof rules out every error that the
sanitizer build detects ([building.md](building.md)). The plain build's budget
is 2 GiB in a statement about an ASan build, and 16 GiB in a statement about
the UBSan build. The sanitizer build may use 512 GiB and has no premise. A
project may set its own pair for a sanitizer instead (project.yaml `budgets`,
[facts.md](facts.md)): the statement's term then carries the two sizes, and its
text names both. Two agrees statements with different budgets claim different
things: compare the budgets before you compare the statements.

The statement does not say two things. It compares sets of behaviours, not two
runs in lockstep. And a trace is finite, so a run that never ends shows only
the output that it wrote so far. Agreement does not rule out a hang, in either
build. Only a halts statement does.

Some harnesses are stated in a variant. The statement's docstring names it.

| variant | shape | LPS definition | what changes |
|---|---|---|---|
| none | `agrees` | `strong_universal_error_free_T_budgets` | The environment may refuse every kind of call that LPS lets fail, at any time ([semantics.md](semantics.md#vocabulary)). |
| alloc-forced-only | `agrees_in Env.alloc_forced_only` | `strong_universal_error_free_T_scfg_budgets` | The same, except that a memory request is refused only when the budget is spent or no address range is free. Without it, a harness whose own code aborts when an allocation fails would make the statement false, for a reason that has nothing to do with the sanitizer. It is also used for a Python fuzz target, whose interpreter can abort the same way while it starts, and for the AddressSanitizer pairs of a Rust fuzz target: the port's allocation-failure hook writes the failed allocation's size and exits with status 2, and ASan's allocator asks the kernel for memory at other allocations than musl's does, so the two builds, refused at will, could write different lines. |
| abort read as SIGABRT | `agrees_abort_modelled`, `agrees_in_abort_modelled` | the `_abort` variants | LPS reads `abort()` as death by a signal, not as a step that LPS does not cover. The statement still forbids it. It is used for harnesses (most of them C++) where an uncaught exception reaches `abort()` through the C++ runtime. |
| RV64GC | the `_rv64gc` shapes (this release uses `agrees_abort_modelled_rv64gc`) | the `_hwcap_rv64gc` variants, for the agreement and classifier shapes | The process is told that its machine has no vector unit. It is used for binaries that take vector code paths when the processor advertises the vector extension. |

## How often the builds disagree: `<build>_disagrees_at_most b`

Draw an input from the harness's distribution, `Distribution.v`. The
probability that the plain and sanitizer builds are not both error-free with
equal traces is at most `b`.

Read `b` with care. In most distributions, nine tenths of the weight (22/25
where a component varies the environment) is on the driver's header, sometimes
a fixed payload prefix, and then a payload of random bytes (or random symbols
of a fixed alphabet) whose length is geometric. For a harness that expects
structured input (JSON, TLS records, images), almost all of that weight is on
inputs that the parser rejects early. So `b` is a statement about this
distribution, mostly about how the builds treat malformed input. It is not an
estimate of risk on real inputs.

A smaller `b` is stronger. A proof at `b` implies every larger `b`, and
`b = 1` holds trivially. Agreement here is judged at 16 GiB and 512 GiB, with
no budget premise, so `asan_agrees` alone does not give
`asan_disagrees_at_most 0`. Each input core (the arguments, the environment,
the files and standard input) is counted once. It counts as a disagreement if
the builds disagree for some choice of the rest of the input (the identities,
the network peers, the limits and the advertised machine) or for some launch
of either build.

`Distribution.v` is written out in full. Its header says in words how an input
is drawn. `oft lint` checks the fields that the header is rendered from
against the definitions under it, and `oft generate --check` checks that the
header is their rendering.

## Deciding where they agree: `<build>_agreement_decidable`

Some well-formed riscv64 program decides exactly the finite inputs on which the
two builds agree. `Characterise.v` states the problem for a given program `C`:
`<build>_classifies C` (C exits 0 exactly on the agreeing inputs and 1 on the
others) and `<build>_classifier_rejects_at_most C b`. These two are not claims.
Together with a proof that `C` is well formed, they prove the decidability
statement and, through `Shapes.disagrees_at_most_of_classifier`, a bound.

Why decidability is worth a statement: agreement over all inputs is a property
of infinitely many runs, but a classifier is one program that can be run, and
reasoned about, on its own. A proof that a specific program classifies the
inputs turns the question "how often do the builds disagree?" into "how often
does this program reject an input from the distribution?". That is the route to
a bound, and a decidability proof that exhibits such a program is its first
step.

## A Go fuzz target's one statement

A Go fuzz target is the exception to the build and statement counts above: it
has the plain build only, so its one statement is `plain_halts`, with the exit
set {0, 2} and no `_halts_may_fail`, agreement, bound or decidability
statement; `oft lint` refuses any other
([building.md](building.md#go-fuzz-targets)).

## Names, identifiers and revisions

A statement's identifier is `project/harness/statement`, for example
`zlib/checksum_fuzzer/plain_halts`. Its fingerprint (in
[index/statements.tsv](../index/statements.tsv)) is a SHA-256 over what fixes
its meaning: its identifier, its definition, the SHA-256 of each binary it
names, the code of `theories/Shapes.v` and `theories/Images.v` (not their
comments or layout), the LPS version string from release.yaml (`unreleased` in
this release; the commit is not hashed) and, for a bound, its distribution.
Cite a statement with its revision, `project/harness/statement@r1`; the
revision changes whenever its meaning does ([versioning.md](versioning.md)). A
withheld statement has no fingerprint.
