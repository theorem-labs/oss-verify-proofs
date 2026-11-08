# How a proof is checked

The verdict on a proof is one command, `oft check`, run in the checker image
that [release.yaml](../release.yaml) names (`images.checker`). This page says
what that command does, which Rocq it uses, how it audits axioms, and what CI
runs.

## Rocq

The checker image holds the official Rocq 9.2.0 (opam packages `rocq-runtime`,
`rocq-core` and `rocq-stdlib` at 9.2.0), LPS at the commit that release.yaml
names (`semantics.commit`) with its `elf-snapshot` tool, and the libraries that
LPS and the proofs use: stdpp 1.13.0, Flocq 4.2.2 and rocq-read-file 0.0.2. It
also holds dune and Python 3. It holds no proof automation
([toolchain/checker.Dockerfile](../toolchain/checker.Dockerfile)). The base
image is pinned by digest, the Rocq opam repository by commit, every opam
package by version and checksum, and the LPS files by a hash over them. The
Ubuntu packages that the image installs (libgmp-dev, pkg-config, m4, python3
and time) are not pinned.

The proofs load their libraries with plain `Require`. The kernel checks every
term as `rocq compile` builds it.

## What `oft check` does

For each harness that it checks, `oft check`:

1. checks every binary against its SHA-256 in `harness.yaml`;
2. builds the memory images from the ELF files, then `Images.v`,
   `Statements.v` and `Characterise.v`;
3. builds the harness's proof library,
   `projects/<project>/<harness>/proofs/lib/`, if it has one (once), with dune
   from the `lib/dune` file that `oft generate` writes, and refuses a library
   with any other build file. Then it compiles each proof afresh with
   `rocq compile`. In CI this runs under
   `docker run --network none`, so it has no network;
4. compiles, with every warning off (`rocq compile -w -all`), a wrapper that it
   writes itself. The wrapper gives the proof's theorem the type of the
   statement, and has `Print Assumptions` write what the result assumes into
   a file of its own, `assumptions.out`:

       (* written by oft check; never supplied by a pull request *)
       From Stdlib Require Import QArith.
       Require OSSVerify.zlib.checksum_fuzzer.Statements.
       Require OSSVerify.Proofs.zlib.checksum_fuzzer.plain_halts.Proof.
       Definition certified : OSSVerify.zlib.checksum_fuzzer.Statements.plain_halts
         := OSSVerify.Proofs.zlib.checksum_fuzzer.plain_halts.Proof.plain_halts_holds.
       Set Printing Fully Qualified.
       Redirect "assumptions" Print Assumptions certified.

   A proof of any other statement does not type-check. The proof and its
   library are compiled from their `.v` files only, against the statements
   that `oft check` built, so a proof written against an edited statement does
   not type-check either;
5. audits `assumptions.out` (below). It never reads what the compile printed,
   so a note that a proof makes Rocq print while the wrapper compiles cannot
   reach the audit. Turning the warnings off only keeps the compile's log
   quiet; a proof can turn them on again, and the audit does not depend on it.

By default, `oft check` also runs each counterexample under qemu-riscv64. The
checker image has no qemu, so CI runs `--parts statements,proofs` in the
checker image and `--parts counterexamples` in the runner image.

In CI, `oft lint`, `oft plan` and `oft check` always run from the base branch
of a pull request, never from the pull request. The statements also come from
the base branch, except in a release pull request, which changes the facts on
purpose ([pr.yml](../.github/workflows/pr.yml)).

## Axioms

[toolchain/allowed-axioms.txt](../toolchain/allowed-axioms.txt) lists every
axiom that a proof may use:

- the primitive 63-bit integers, arrays and strings of Rocq, and the axioms
  that specify them (`Corelib.Numbers.Cyclic.Int63.*`, `Corelib.Array.*`,
  `Corelib.Strings.*`);
- six axioms of the standard library: `Classical_Prop.classic`,
  `FunctionalExtensionality.functional_extensionality_dep`,
  `IndefiniteDescription.constructive_indefinite_description`,
  `PropExtensionality.propositional_extensionality`, and
  `ClassicalDedekindReals.sig_forall_dec` and `sig_not_dec`.

The audit is the function `wrapper_assumptions` in
[tools/oft/check.py](../tools/oft/check.py), about 30 lines of Python. It reads
what `Print Assumptions` wrote for the wrapper, and nothing else:

- Nothing is assumed only when that is exactly the one line "Closed under the
  global context". An axiom's printed type can hold that line too.
- Otherwise it must be a list of assumptions from its first line on, and each
  entry under "Axioms:" must be a name in the allowed list.
- Everything else is refused: an inductive type assumed positive, a fixpoint
  assumed guarded, an unsafe universe hierarchy, definitional UIP, a change to
  the logic, and output that it cannot read.

A proof may not declare an `Axiom` or a `Parameter` or end in `Admitted`, nor
declare an axiom another way: `Declare Instance`, `Declare Module`, or a
`Variable`, `Hypothesis` or `Context` outside a Section. It may not carry a
`deprecated` or `warn` attribute, whose note Rocq prints wherever the theorem
is used, or go back in the file with `Reset`. `oft lint` refuses these on
sight. An `Admitted` lemma is an axiom, so the audit would refuse a proof that
uses one in any case, and it refuses every one of these axioms too.

## `rocqchk`

`rocqchk` is not part of the verdict, and CI does not run it. `oft check
--rocqchk` adds it as an independent second check of the compiled libraries:
`rocqchk -o -bytecode-compiler no`, once per harness over its statements and
once per harness over the wrappers of all its proofs and their closure, with
every axiom that it reports checked against the allowed list. Without its
bytecode machine, `rocqchk` checks every `vm_compute` by reduction, which can
take hours for the proofs of one harness. With the bytecode machine on,
`rocqchk` 9.2.0 refuses every library that holds a
primitive string, and it runs the bytecode stored in each compiled file instead
of compiling it from the checked terms. Both problems are fixed upstream after
9.2.0 ([rocq-prover/rocq#22361](https://github.com/rocq-prover/rocq/pull/22361),
[#22353](https://github.com/rocq-prover/rocq/pull/22353)).

## Stack size

Rocq recurses on the system stack, and large proof terms overflow the usual
8 MiB. So before the `statements` and `proofs` parts, `oft check` sets the
stack's soft limit, which every `rocq`, `rocqchk` and `dune` it starts
inherits, to the smaller of the hard limit and 2 GiB. An unlimited hard limit
counts as infinite, so the soft limit is always finite: glibc gives each new
thread a stack of the soft limit's size, and a soft limit far above the
memory stops `dune` and `zstd` from starting their threads. This changes where
the kernel runs, not what it checks.

`oft check` refuses no hard limit. Below 2 GiB it runs with soft = hard. A
runtime can also give less stack than the limit says: gVisor, the build
pool's runtime, gives 8 MiB when the limit reads unlimited, and about 128 MiB
under a limit of 1 GiB or more. So `oft check` measures the stack it got, with a small
C program (`tools/oft/stackprobe.c`, compiled with `cc`, which the checker
image has), and prints it before it checks anything:

    stack: 127 MiB usable (soft 2147483648, hard unlimited; started with soft 8388608, hard unlimited; runtime gvisor)

The limits are in bytes. "runtime" is `gvisor` when the kernel's release name
holds `gvisor`, the gate's own test, and `linux` otherwise; it only labels the
line, and the measured stack is what counts. Without `cc` the line says
`not measured (no cc on PATH)` in place of the size.

A step that runs out of stack (Rocq's `Error: Stack overflow.`, or a crash
with SIGSEGV) fails with the stack it had, apart from a proof that does not
compile:

    FAIL projects/zlib/checksum_fuzzer/proofs/plain_halts: projects/zlib/checksum_fuzzer/proofs/plain_halts: stack exhausted at 7 MiB (see .../compile.log)

Such a failure is about the machine, not the proof: check it again where the
stack is larger.

Without `--ulimit`, a container gets its stack limit from the Docker services
that start it. On a host with systemd, these services usually get it from
systemd's `DefaultLimitSTACK`. `docker run --ulimit stack=-1:-1` gives the
container an unlimited hard limit, whatever the host sets, so the check gets
its 2 GiB. The commands in
[proving.md](proving.md#checking-a-proof-locally) and
[adding-a-proof.md](adding-a-proof.md#steps) pass it.

Outside a container, `ulimit -Hs` shows the hard limit in KiB (2 GiB is
2097152). Only root can raise it.
[tests/check.sh](../tests/check.sh) sets its own limit for the controls,
which it compiles with `rocq compile` and not through `oft check`
(`ulimit -s unlimited`).

## What CI runs

| workflow | when | what |
|---|---|---|
| [release-check](../.github/workflows/release-check.yml) | each push to `main`, and on request | what the push changes. `oft plan` checks each part of each harness (its statements and proofs, its counterexamples, its findings) whose content key ([tools/oft/keys.py](../tools/oft/keys.py)), the hash of what that part's check reads, differs from its key at the commit before the push; every part when the push changes what no key holds (`toolchain/`, the checker (every file of `tools/` but those `keys.NOT_THE_CHECKER` names), `tools/oft/keys.py`, `.github/actions/`, a `.gitattributes`, or a path git quotes), or when the checker's id cannot be computed; no part when pr.yml's merge queue already checked every commit of the push with the tools it has. Every committed proof and finding on request. `oft check`, in the checker image; the badge on the README shows its result |
| [pr](../.github/workflows/pr.yml) | each pull request, each merge queue group, and each push to `main` | `oft lint`, `oft generate --check`, the tests of `tools/oft`, the controls in `tests/`, and `oft check` on each part of each harness that the change affects. With base tools that have content keys, a part is checked when its key differs from its key at the base; the key holds the statements the run checks, the change's proofs, counterexamples and findings (each harness's `proofs/`, `counterexamples/` and `findings/` folders), and the base's tools, which the check jobs run, so a change to the tools or the workflows checks no part here. A pull request that is not a release is checked on the base's facts and tools with its harnesses' `proofs/` and `counterexamples/` folders, whose generated files, `dune-project` among them, the base's tools render again. A merge queue group runs no check job when four things hold: every path of its diff from the group's base is a file of a unit's own `proofs/` folder in either layout, which only that unit's build reads and whose id that unit's build key holds, `CHANGELOG.md`, a file of `tools/` that `keys.not_the_checker` names, which no check opens, or a fuzz target's or a project's generated `README.md`, which no key holds; every pull request of the group carries merge-pr.sh's `<!-- vm-evidence head=<its head> mode=... -->` comment for its own head now, edited by nobody but the app; every part the plan marks for checking is a unit's `build` whose content key here, by the base's tools, equals the build key that comment recorded for the unit at its check of record (`<!-- vm-evidence-key unit=<p>/<h> key=<64 hex> -->`), so nothing that part's check reads — its proofs folder included — moved between the two trees; and every comment names the checker its check of record ran under on its own line (`<!-- vm-evidence-checker id=<64 hex> -->`), the `keys.checker` of the tree this run checks, since a key says nothing about the tools that computed it. The equal keys, not the paths, are what makes the skip safe. Then `required` passes naming each comment. A planned `counterexamples` or `findings` part, which no evidence line records, leaves the group its checks, and so does a comment with no checker line, with more than one, or with another checker's id. A key that differs from the one the group's last entry recorded leaves it nothing: the plan job fails, naming that pull request, the unit and the two keys, so the queue takes that entry out instead of holding every entry behind it for a check of a tree its owner never measured, and its owner measures it again at its new head and queues it again. A failing group takes out the entry its branch names and no other, so an earlier entry's key that differs leaves this group its checks and is taken out by the group that entry's own branch names. A pull request's own run that is not a draft runs no check job by the same four rules, with the pull request as the one entry: its own comments for the head its merge commit merges, and the plan's keys over that merge commit; a key that differs there leaves it its checks, and the run does not fail, since no queue entry is there to take out |
| [weekly](../.github/workflows/weekly.yml) | every Monday at 03:17 UTC, after a release that attaches files, and on request | A scheduled run, or a run on request with no unit list, checks every statement and every proof, with no cache. After a release, the release workflow runs it on the fuzz targets of the projects whose files that release attached. Every run compares ELF snapshots made on two kinds of machine, and downloads and hashes every release asset that the facts pin by SHA-256. |

Every `oft check` first loads the facts of the whole tree and checks the rules
between them. `--facts-to DIR` does only that, then writes the facts each
harness's check reads to `DIR/<project>/<harness>.yaml` with the SHA-256 of
each file they came from, and the release's namespace and opam stem, which a
view holds no `release.yaml` to give; it builds and runs nothing.
`--facts-from DIR` then checks each harness as a plain check would, from its
facts file alone, so it can run in a view that holds only that harness's
files. Facts it cannot use are VOID, not a failed harness: a facts file that is
missing, of another format version or of another harness, or whose namespace
does not give `harness.yaml`'s `rocq`, or, for a part it checks, whose facts
came from a file that differs in the view, or whose view has other proof,
counterexample or finding directories, stops the run at once with one
`VOID: <reason>` line and exit 7. Nothing was checked, so nothing failed.
It compares nothing else. The rules read more, in the harness (`source/`,
`Distribution.v`, the build record under `provenance/`) and in the rest of the
tree (`theories/Shapes.v`), so it cannot show that the facts and the view come
from one tree. Write the facts from the same checkout as the view, mount
`DIR` read-only, and give each check only its own file. The format is part of
the checker ([tools/oft/keys.py](../tools/oft/keys.py)), so a change to it
checks every harness again.

CI's check jobs ([tools/oft/ci/check-units.sh](../tools/oft/ci/check-units.sh))
run the two phases this way. `--facts-to` runs once per job, on the whole tree
mounted read-only. Then each part of each harness (its build, its
counterexamples, its findings) is checked in a container of its own. That
container's `/work` is a view that holds the paths of the part's content key
([tools/oft/unitpaths.py](../tools/oft/unitpaths.py)) and the harness's
binaries, each mounted read-only, and no other file of the tree. So a proof
cannot read another harness's files. A change that the key does not see also
cannot change the result. Nothing that one check compiles is shared with
another: dune's cache is off, and the view's directory is removed after each
check.

Two parts of a harness's build record are in neither its key nor its view: its
prose, `provenance/PROVENANCE.md`, and its licence evidence,
`provenance/evidence/licence/`. No rule a check runs and no build opens
either, so a change to them leaves every recorded pass standing
([tools/oft/unitpaths.py](../tools/oft/unitpaths.py) `PROOFS_DROP`). The
record itself, `provenance/PROVENANCE.yaml`, which the rules read, is keyed as
before, and so are its build recipe, its port copy, its licence texts and its
other evidence.

The checker and runner images are built from
[toolchain/checker.Dockerfile](../toolchain/checker.Dockerfile) and
[toolchain/runner.Dockerfile](../toolchain/runner.Dockerfile) by the workflow
[images.yml](../.github/workflows/images.yml). The runner carries a copy of
tools/oft: the one a release has already published. The workflow also records a
build provenance attestation for each image it pushes, for the maintainers'
own checks; it is not published with the image. Each build verifies the
attestation it has just stored, and the workflow's verify-pins job verifies the
attestations of the two digests release.yaml pins, every day and on a run by
hand that builds nothing. An image pinned before that workflow existed was
built by hand and has none, so verify-pins fails until its pin is replaced.
release.yaml pins each image by digest (`images.checker`, `images.runner`), and
nothing else pins them. A new image is used only after a pull request changes
its pin, and that pull request re-checks what runs in that image.

No proof check restores dune's cache: release-check and pr compile every
library and statement that a check reads on every run, and weekly's sweep reads
no cache. A valid compiled `Statements.vo` of other statements, put in a filled
cache under the same key, made doctored proofs pass: dune restores a cached file
without hashing its bytes again, and the kernel does not check a compiled file
again when a proof loads it. Each proof and its wrapper are also compiled afresh.
`oft check` builds a proof library only from the `lib/dune` that `oft generate`
renders (it writes that file itself; in CI, check-units.sh writes it with the
same tools before the view is made, since the view's copy of the library is
read-only), and refuses a library that holds a symbolic link or any other build
file, or a build file in a directory above it.

Every counterexample and its control input are run again in the runner image,
and a counterexample that stops reproducing fails CI.

A checker image built from `toolchain/checker.Dockerfile` trusts no root of
eMudhra's emSign CAs or of Comodo's AAA Certificate Services: the Dockerfile
disables them in the system store and fails the build if one remains. A
checker image built before that step, such as the one v2026.10.1 pins, still
trusts them. No check uses TLS in any checker image: they run with no
network. The build fetches the Rocq opam repository with git, which checks the
pinned commit's hash. The runner image has no store of trusted roots.


[tests/check.sh](../tests/check.sh) runs the same check on the toy controls in
`tests/`. It fails if a control that must be refused is accepted, or if it is
refused for the wrong reason.
