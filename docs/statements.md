# What the statements say

This page explains the statements under `projects/`. The proofs in each
harness's `proofs/` folder prove some of them;
[index/PROOFS.md](../index/PROOFS.md) lists which.

Every statement under `projects/` is a definition in a harness's
`Statements.v`. Most have the form `Definition <name> : Prop`. A bound
statement takes its bound first: `Definition <name> (b : Q) : Prop`. Each
definition applies one of the shapes in [theories/Shapes.v](../theories/Shapes.v)
or, for a classifier statement, one in
[theories/ClassifierShapes.v](../theories/ClassifierShapes.v), to the memory
images of that harness's binaries. Each agreement shape and each
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
15 statements, up to eight more for each sanitizer pair whose classifiers it
publishes (six without an input distribution; classifier statements, below),
and one more for each twin (Twins, below). An API driver (harness
`api-driver`, origin `this-repository`) is a harness this repository wrote:
a program that drives the library through its API from the input, in place of
an OSS-Fuzz fuzz target, with statements of the same kinds. zlib's
`api-driver` is one.

## Halting: `<build>_halts`, `<build>_halts_may_fail`

`plain_halts` (shape `halts_within_budget`) has two premises. The build is
never refused memory for exceeding 16 GiB, and the environment refuses nothing
that the process's state does not force. On every input that meets them, every
execution exits with an allowed status: status 0 or 2 for most harnesses,
status 0, 2 or 78 for a harness that lists `rejects` (below), and any status
for espeak-ng's `ssml-fuzzer`. So no execution of a covered input runs forever,
crashes, fails an assertion or a sanitizer check, or leaves LPS. Nothing is
said about output. In a Rust, Python or Go fuzz target a failed assertion ends
the process with an exit status rather than an abort, so there only a
statement whose exit set leaves out that status rules it out; one that allows
any status does not. The status is 79 for a Rust panic; for a Python exception
that nothing catches in a call of the harness, other than `MemoryError`
(status 2) and `SystemExit` (status 77); and for a Go panic on the fuzz
target's goroutine or `t.Fatal`, `t.Error` or `t.Fail` in a Go fuzz test. A Go
panic on another goroutine exits with status 80, and so does a Python failure
while the interpreter starts or the harness module runs before the first call
(status 2 when that failure is an uncaught `MemoryError`)
([building.md](building.md)).

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

Not every fuzz target that returns 1 to turn an input away lists its `rejects`
yet. Where one lists none, its halts statements with a finite exit set do not
allow 78, and a covered input on which the run then ends with status 78 makes
them false. Not every such input does: in counting mode (bit 15 of the config
word) the driver exits with the count instead of 78 (`theories/Driver.v`).

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
execution exits, with a status its exit set allows (`any`, or a finite set as
above), even when the environment may refuse any request at any time, and there
is no memory premise. It is stated only for the
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

**One reading for a pair.** This is the rule the facts review holds a
harness's facts to. The agreement, bound and decidability
statements of one pair (`plain` and one sanitizer build) share one reading:
`alloc-forced-only`, whether or not the fuzz target aborts when an allocation
fails. A pair is read `may-fail` only when a statement of the pair is proved
in that form, or when its agreement has no `alloc-forced-only` shape (`abort:
signal` with `machine: rv64gc`). A twin is the one exception: a pair may hold
an agreement statement read `may-fail` and, beside it, its twin read
`alloc-forced-only` (`twin: alloc-forced-only`, "Twins", below). Each of the
two is read as its own fields say, and the pair's other statements share one
reading. A pair with two readings and no twin is a finding.

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
header is their rendering and that the body, in the one form
`tools/oft/claims.py` reads, defines the weights `harness.yaml` gives, each
above 0.

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

## Classifier statements: `_ca_total`, `_cb_total`, `_ca_sound`, `_cb_sound`, `_maybe_good`, `_maybe_diff`, `_bound_good`, `_bound_diff`

A harness can publish classifier programs for a sanitizer pair (`classifiers`
in harness.yaml, [facts.md](facts.md#classifiers)). A classifier is a static
riscv64 program that reads the same input file as the builds and answers: it
exits 0 for yes, 1 for no and 2 for maybe. A crash, a hang or another exit
code is not an answer. A classifier statement names ONE such program by its
image, `Images.classifier_<a or b>_<build>`, and makes a claim about it. The
decidability statement above says only that SOME program exists; a classifier
statement says what THIS one does. Classifier A is about where the two
originals of the pair agree, classifier B about where each build agrees with
its original. This is the yes / no / maybe form of the classifier statements.

| statement | kind | classifier | shape (theories/ClassifierShapes.v, or Shapes.v) | LPS definition (a model release that is not public yet) | claim |
|---|---|---|---|---|---|
| `<build>_ca_total`, `<build>_cb_total` | `classifier-total` | a, b | `classifier_total3` | `Classifier.classifier_total3_T_fo` | On every valid finite input, from every valid entry, every run exits 0, every run exits 1, or every run exits 2. |
| `<build>_ca_sound` | `classifier-sound` | a | `classifies_good_inputs_sound` | `Classifier.classifies_good_inputs_sound_T_s` | When A answers yes, the two originals agree on the input; where they agree, A never answers no. |
| `<build>_cb_sound` | `classifier-sound` | b | `classifies_patch_diff_sound` | `Classifier.classifies_patch_diff_sound_T_s` | When B answers yes, each build agrees with its original on the input; where they do, B never answers no. |
| `<build>_maybe_good`, `<build>_maybe_diff` | `classifier-maybe` | a, b | `maybe_at_most`, or `maybe_empty` without a distribution | `Measure.maybe_bound_T_fo`, `Classifier.maybe_empty_T_fo` | For an input drawn from `Distribution.v`, the classifier gives no firm answer (neither yes from every valid entry nor no from every valid entry) with probability at most `b`; with no `Distribution.v`, on no valid input. |
| `<build>_bound_good`, `<build>_bound_diff` | `classifier-bound` | a, b | `Shapes.classifier_rejects_at_most` | `Measure.weight_bound_T_fo` | For an input drawn from `Distribution.v`, the classifier does not answer yes (it answers no or maybe, or gives no answer) with probability at most `b`. |

**The shapes are copies.** The LPS definitions in the table come from a model
release that is not public yet. The LPS that release.yaml pins does not have
these names yet; the public model carries them from a later release.
theories/ClassifierShapes.v writes each shape out in the text of that release,
carries that text verbatim at the end of the file and proves each shape equal to
it by `reflexivity`; `oft lint` pins the copied bytes
(`rules.LPS_CLASSIFIER_NAMES_COPY`). Until that release is public, only a
reader with access to it can compare the copy with it.
When the pinned LPS has the names, each shape gets its `_is_lps` lemma, as
the shapes of Shapes.v have ([trust.md](trust.md)). That file's code enters
the fingerprints of the classifier statements alone, so it moves no other
statement's fingerprint.

How to read them:

- The classifier's own runs are judged with the environment refusing only what
  it is forced to (`Env.forced_only`): a program that answers must be able to
  read its input. Only `_ca_sound` and `_cb_sound` name the builds, so only
  they have a `reading` (`Env.may_fail` or `Env.alloc_forced_only`): the
  environment of the property they are sound for, at 16 GiB for the plain
  build and 512 GiB for the sanitizer build, with no budget premise. The
  other kinds take no `reading`, and `oft lint` refuses one, so that no two
  spellings state one statement.
- Both sound statements name the originals. An original is built by the same
  recipe as its published build, with the same driver and the same
  modifications (harness.yaml `modifications`), but with none of the patches:
  none of the library patches the project applies (project.yaml `patches`,
  counted by `library.patch_count`), and from the upstream harness source
  (`source.from`) where the published one is modified. The statement's
  `originals` field says which images they are. `unpatched` names the builds
  of harness.yaml's `originals` (`Images.<build>_original`). `published` names
  the published builds themselves, and `oft lint` allows it only for a
  harness built with no patch at all: project.yaml gives
  `library.patch_count` 0 and lists no patches, and the harness source is
  unmodified. Then the published builds ARE the originals, so the choice
  cannot weaken the claim.
- `_ca_sound` is about where the two originals agree: both error-free with
  equal traces at every pair of valid entries.
- `_cb_sound` is about where each published build agrees with its original:
  at every pair of valid entries, the same finite traces, and an error, an
  all-error behaviour or an unmodelled step reachable in one exactly when in
  the other. For a harness without patches, that is each build behaving the
  same at every pair of valid entries.
- A sound statement alone says nothing of how often the classifier
  answers: a classifier that answers maybe on every input meets it, and its
  total statement too. Read `_ca_sound` with `_maybe_good`, and `_cb_sound`
  with `_maybe_diff`. With no distribution, the `_maybe_*` statement is
  `maybe_empty`: the classifier gives a firm answer on every valid input, so
  with the sound statement it is exact (the exact statement, below). With a
  distribution, `maybe_at_most` bounds how often it gives none.
- A crash, a hang and mixed answers count as maybe in `_maybe_*`, and as not
  yes in `_bound_*`. So `_bound_*` counts no and maybe together, and
  `_maybe_*` counts maybe alone.
- A smaller `b` is stronger, a proof at `b` implies every larger `b`, and
  `b = 1` holds trivially, as for `_disagrees_at_most`.
- A proof of the exact statement, which says that the classifier answers only
  yes or no and is right on every input (Shapes.v `classifies`, or
  ClassifierShapes.v `classifies_patch_diff`), proves the matching sound,
  total and maybe statements, with a maybe bound of 0, by the bridges at the
  end of ClassifierShapes.v. No statement of the exact form is stated.

Classifier statements have the machine `rv64g` only, and take no `machine`
field.

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
A classifier statement's fingerprint also hashes the SHA-256 of its classifier
and of each original it names, and the code of `theories/ClassifierShapes.v`.
The two theories are hashed with the release's Rocq namespace (`namespace` in
release.yaml, `OssFuzzTheorems` while it names none) read as `OssFuzzTheorems`
wherever it starts a dotted path, so renaming the namespace moves no
fingerprint. Cite a statement with its revision,
`project/harness/statement@r1`; the revision changes whenever its meaning does
([versioning.md](versioning.md)). A withheld statement has no fingerprint.

## Twins: `<build>_halts_any_exit`, `<build>_agrees_alloc_forced_only`

A harness may carry a second statement beside one it has, when a proof proves
a statement that differs from it in one way. The second statement is a twin
(harness.yaml `twin`), and the one it sits beside is its first. A twin never
replaces its first: both stay, each with its own status and proof.

| `twin` | kind | the twin | its first | name |
|---|---|---|---|---|
| `any-exit` | halts | `exits: any` | the same kind, build and reading, with a finite exit set | `plain_halts_any_exit` beside `plain_halts` |
| `alloc-forced-only` | agreement | read `alloc-forced-only` | the same pair, read `may-fail` | `asan_agrees_alloc_forced_only` beside `asan_agrees` |

The twin's term is the one its fields give, as for any statement; only its
name says that it is a twin. `oft lint` refuses a twin whose first the harness
does not list, and a twin that does not differ from its first in the way its
`twin` names.
