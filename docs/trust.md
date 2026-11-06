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
