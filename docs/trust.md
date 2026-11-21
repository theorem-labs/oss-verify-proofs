# What you have to trust

A proof that `oft check` accepts shows that a statement holds, if you trust
these things:

- **The kernel of Rocq 9.2.0**, as `rocq compile` runs it in the checker image,
  with its bytecode machine (`vm_compute`).
- **The axioms** in [toolchain/allowed-axioms.txt](../toolchain/allowed-axioms.txt):
  the primitive 63-bit integer, array and string types of Rocq, their
  operations and their specifications, and six axioms of the standard library
  (`classic`, `functional_extensionality_dep`,
  `constructive_indefinite_description`, `propositional_extensionality`, and
  `sig_forall_dec` and `sig_not_dec` of `ClassicalDedekindReals`). A proof whose
  `Print Assumptions` lists anything else is refused. `rocqchk` is an optional
  second check, not part of the verdict ([checking.md](checking.md)).
- **LPS**, at the commit that [release.yaml](../release.yaml) names
  (`semantics.commit`); the checker image is built from it. You trust its
  instruction semantics, its rules for system calls and for process start-up,
  its definition of a run, and the definitions that the statements use
  ([semantics.md](semantics.md)). The `_is_lps` lemmas in `Shapes.v` prove that
  the agreement, halts and classifier definitions here are the definitions of
  LPS. They do not prove that LPS is right about Linux.
- **The two definitions that `Shapes.v` makes itself**, `disagrees_at_most` and
  `agreement_decidable`. They are built from LPS definitions, but no lemma says
  that they equal one. You trust them as written, for the bound and
  decidability statements.
- **The classifier shapes of `ClassifierShapes.v`, which are COPIES.** They
  are the yes / no / maybe definitions of an LPS release that is not public
  yet, which the LPS pinned in release.yaml does not have; the public model
  carries these names from a later release. The file carries that LPS text
  verbatim at its end and proves each shape equal to it by
  `reflexivity`; `oft lint` pins the copied bytes
  (`rules.LPS_CLASSIFIER_NAMES_COPY`). So you trust that the copy is the LPS
  text. Until that release is public, only a reader with access to it can
  compare the copy with it. The pin fixes the text of this yes / no / maybe
  layer only: the model under it comes from the pinned LPS, as for every
  shape. When release.yaml pins an LPS that has these names, each shape gets
  its `_is_lps` lemma and the copy goes (the follow-up named in the file's
  header). The classifier statements are stated with these shapes.
- **The tools that turn an ELF file into a memory image**: LPS's
  `elf-snapshot`, and `rocq-read-file` 0.0.2, an OCaml plugin that reads the
  image's bytes at compile time. They are outside the kernel. `Images.v`
  checks by computation that each image is well formed. This rules out an image
  so malformed that every statement about it holds for no reason:
  `theories/Premises.v` proves that for every well-formed image the entry and
  input premises of each statement shape hold together, so a `halts_may_fail`
  statement, which has no other premise, is never vacuous. The budget premise
  of the other halts and agreement statements reads the run, and is shown
  satisfiable only on toy images (`tests/proofs/toy/ebreak/`), not for any
  real build.
- **`oft check`** ([tools/oft/check.py](../tools/oft/check.py)): the wrapper
  that it writes to give a proof the type of its statement, and its reading of
  `Print Assumptions`. A wrong wrapper or a wrong reading could accept a proof
  of something else.
- **The statement text.** `oft generate` renders it from the facts with the
  templates in `tools/oft`, so anyone can render it again and compare.

These are not in the trusted base, and nothing is claimed about them: the
compiler, the build, and any relation between a binary and its source code. A
statement is about the bytes that its SHA-256 names.

Before a release, a gate rebuilds each build that a recipe built
from the published recipe and source archives, and compares its SHA-256 with
its pin. It rebuilds each original (harness.yaml `originals`) in the same way,
with the recipe's patches (`patches/series.tsv`) left out, and compares it
with its pin. That rebuild gives an original only where the recipe lays out
the harness from the source archive: for a modified harness of which the
recipe holds its own copy, no rebuild gives the upstream harness source, and
the gate fails the original. It fails an original too for a modified harness
whose harness.yaml does not record how the recipe lays out the harness
(`deviation.harness_origin`). A classifier (`classifiers`) is not rebuilt,
because no recipe builds one yet. The gate checks it as a pinned file, its
bytes and SHA-256 in the release archive against its pin, so you trust its
bytes as they were built. When a recipe that builds the classifiers exists,
the change that adds it adds their rebuild. For a project that the OSS Verify
port builds, the gate rebuilds each original from the published port archive
with every patch left out (the `patch` lines of the project's `sources`, its
`series` and its `.patch` files), and compares it with its pin. It checks each
classifier as a pinned file of the release archive, as for a recipe-built one.
An original whose harness has no upstream form (a modified `vendored` or
`extended` harness, or one with no `deviation.harness_origin`) fails, as for
a recipe-built unit. For a unit that the unpublished internal recipe built (a
build record with `fallback`), no job checks its originals and classifiers,
and the gate fails them. A harness with no build record has no build of
record to rebuild, so the gate does not rebuild its builds: you trust their
bytes as they were built, in the release archive whose digest the gate checks
against its pin. It still checks what such a harness publishes beside them:
each classifier as a pinned file of the release archive, and, for a project
that the OSS Verify port builds, each original rebuilt from the project's port
archive with every patch left out. For any other project no rebuild gives such
a harness's originals, and the gate fails a harness with no build record that
publishes one, naming the missing `PROVENANCE.yaml`.

A release takes one of two routes, and the gate of each makes these checks:
the gate of a project's publication, and the release gate of a platform
release, which publishes the binary archive of each project too. In Theorem
Labs' internal repository the first is `tools/publish/plan.py` with
`tools/publish/gate-job`, and the second is `dev/stream/bin/ossv-gate` with
`dev/stream/bin/ossv-gate-job`.
