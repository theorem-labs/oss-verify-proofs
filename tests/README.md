# tests: the controls

Everything here is ours (MIT) and small.  `dune build` compiles the positive
controls; `./tests/check.sh` then runs, on every control, the same check CI
runs on a proof (docs/checking.md), and fails unless each positive control
passes and each negative control is refused for the reason it states.
`./tests/check.sh --rocqchk` also re-checks this repository's libraries and
the candidate's with rocqchk, loading the installed toolchain by digest;
`./tests/check.sh --full` also re-checks, in one more rocqchk run, everything
the positive controls depend on, which for these controls includes
linux-process-semantics' own test library: about 15 minutes and 2 GB of
memory in the checker image.

## The toy binaries (`toy/`)

`toy/make_elf.py` writes three static riscv64 Linux programs of 132 or 136
bytes, one PT_LOAD segment each.  They are not stored: dune writes them into
`_build/` and refuses each unless its SHA-256 is the one recorded beside it
(`toy/<name>/*.sha256`).  They run under `qemu-riscv64` 10 with the exit
status the statements predict.

| directory | builds | what the program does |
|---|---|---|
| `toy/exit0/` | `plain` (exit0), `padded` (exit0_nop) | exit_group(0); the second after a no-op |
| `toy/exit1/` | `plain` (exit1) | exit_group(1) |
| `toy/ebreak/` | `plain`, `exit0`: lps's own toy images, no ELF file | `plain` faults on its first instruction (ebreak); `exit0` calls exit_group(0) |

Each directory has an `Images.v` and a `Statements.v` of the same form the
generated files of every harness have, using the shapes of
`theories/Shapes.v`.  `toy/ebreak/Images.v` names two images of
linux-process-semantics' test library (`Checks.Omni.ebreak_image`,
`Checks.Examples.exit0_image`), on which lps refutes its own agreement
statements.

## Positive controls (`proofs/`), which must pass

| statement | shape | result |
|---|---|---|
| `toy/exit0/plain_halts` | `halts_within_budget` | proved (`Proof.v`) |
| `toy/exit0/plain_halts_may_fail` | `halts_may_fail` | proved |
| `toy/exit0/padded_agrees` | `agrees` | proved: two different binaries with equal traces |
| `toy/exit1/plain_halts` | `halts_within_budget` | refuted (`Refutation.v`): exit status 1 is not allowed |
| `toy/ebreak/*` (28) | `halts_within_budget`, `halts_may_fail` and the seven agreement shapes; `disagrees_at_most` and `disagrees_at_most_rv64gc` at every bound below 1 (`*_below_1`); the classifier problem `classifies` and `classifies_rv64gc` for a classifier that accepts everything (`*_accept_all`) | refuted: the plain run is never refused memory and reaches an error |

The `toy/ebreak` refutations are the falsifiability controls: one statement
of each kind at each budget (`Budgets.Standard`, `Budgets.Asan`),
environment (`Env.may_fail`, `Env.alloc_forced_only`), abort reading,
machine and exit set the generator writes, each proved false (the bound and
classifier statements through their `_below_1` and `_accept_all` controls).
`tools/oft/tests/test_toy_controls.py` requires each statement in
`toy/ebreak/Statements.v` to be the generator's rendering, every choice of the
generator to have one, and every control to have its `Refutation.v`.  Each
refutation applies the statement to a valid input and valid entries, and
discharges the budget premise where the shape has one, so it also shows that
premise satisfiable together with the others on a toy image.  The bound
statements use a toy distribution (`toy/ebreak/Distribution.v`) in which one
input weighs the whole mass; they do not show that a harness's weights are
not zero everywhere.  `agreement_decidable` is not refuted: it says some
well-formed program decides the agreeing inputs.  The code proves only that the
pair disagrees on one input (`ebreak_exit0_disagree_fin`); that no input agrees,
so that the program that always exits 1 decides the agreeing inputs, is
believed true, not proved here, so it is not a control.
`toy/Controls.v` pins its body (`agreement_decidable_is`: a classifier with
`image_wf`, solving `classifies`), and the `_accept_all` refutations show
`classifies` fails for a wrong classifier.

`proofs/lib/Exit0Run.v` and `proofs/lib/EbreakRun.v` hold what they share.
They use lps's executable checker and test library
(`LinuxProcessSemantics.LinuxProcessSem.Checks`), and `EbreakRun.v` also
`theories/Premises.v`; nothing else.

## Negative controls (`negative/`), which must be refused

Each directory holds a candidate `Proof.v` and a `claim.yaml` naming the
statement it claims, the step at which the check must refuse it, and a string
the refusal must contain.

| control | refused at | because |
|---|---|---|
| `admitted` | axioms | the theorem is `Admitted`, so it is an axiom |
| `extra_axiom` | axioms | it declares `Axiom cheat : False` |
| `admit_axiom` | axioms | it uses `Stdlib.Compat.AdmitAxiom.proof_admitted`, an axiom of the standard library that is `False` |
| `wrong_statement` | wrapper | it proves `plain_halts_may_fail` under the name `plain_halts` expects |
| `doctored_statement` | wrapper | it was compiled against a `Statements.v` in which `plain_halts` is `True` |
| `hidden_axiom_note` | axioms | it rests on `Hypothesis cheat : False` outside a Section, and its theorem's deprecation note prints "Closed under the global context" in the wrapper's compile |
| `hidden_axiom_string` | axioms | it rests on a `Hypothesis` outside a Section whose printed type holds the line "Closed under the global context" |

`toy/Controls.v` holds the controls that live inside Rocq: images that are not
well formed are refused by `check_image_wf`; a shape stated with another
reading, budget or exit set is not equal to lps's definition; the body of
`agreement_decidable` is pinned; and each per-shape `_not_vacuous` lemma of
`theories/Premises.v` (14) applies to the exit0 toy's images.

## Mutation controls (`mutate.py`), which must be caught

`./tests/check.sh` ends by running `tests/mutate.py`.  For each statement kind
of `theories/Shapes.v` it makes the kind vacuous, or true of every program, in
a scratch copy, and requires `dune build --root . theories tests` of the copy
to fail at a file other than `Shapes.v`; an unmutated copy must build.  The
mutations: for each halting and agreement shape, a premise that contradicts
its input predicate (for `halts_may_fail`, `valid_input_abort inp`); for the
bound shapes, a conclusion that holds at every `b > 0`; for the decidability
shapes, the `image_wf C` conjunct dropped.  In each copy the proofs of
`Shapes.v`'s own lemmas are `Admitted`, since a mutation breaks some of them
(an admitted lemma can only let a file compile, never fail it).  A mutation
that is not caught, or that no longer applies to `Shapes.v`, fails
`check.sh`.  So what these controls catch is a change to `Shapes.v` of these
thirteen forms; a change that edits a control together with the shape, in
the same pull request, is for review to catch.

## The axiom allowlist

`toolchain/allowed-axioms.txt` is the list of axioms a proof may use: the
primitive-type axioms of Rocq's core library (63-bit integers, strings,
arrays) and six axioms of the standard library: `Classical_Prop.classic`,
`FunctionalExtensionality.functional_extensionality_dep`,
`IndefiniteDescription.constructive_indefinite_description`,
`PropExtensionality.propositional_extensionality`, and
`ClassicalDedekindReals.sig_forall_dec` and `sig_not_dec`.  It is NOT every
axiom of every installed library: that set contains
`Stdlib.Compat.AdmitAxiom.proof_admitted`, which is `False`, and the
`admit_axiom` control is there to keep it out.
