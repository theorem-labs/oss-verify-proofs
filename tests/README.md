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
| `toy/ebreak/` | `plain`, `exit0`: lps's own toy images, no ELF file | `plain` faults on its first instruction (ebreak); `exit0` calls exit_group(0); the classifier images are lps's ebreak, exit0 and exit1 images |

Each directory has an `Images.v` and a `Statements.v` of the same form the
generated files of every harness have, using the shapes of
`theories/Shapes.v` (and, in `toy/ebreak/`, of `theories/ClassifierShapes.v`).
`toy/ebreak/Images.v` names three images of linux-process-semantics' test
library: `Checks.Omni.ebreak_image` and `Checks.Examples.exit0_image`, on
which lps refutes its own agreement statements, and
`Checks.GatedSize.exit1_image` (below).  It also names the images of the
classifier statements, in the roles the generator names: the classifiers
`classifier_a_asan` and `classifier_b_asan` are the ebreak image, a
classifier that gives no answer, and the originals `plain_original` and
`asan_original` are the builds' own images, as for a harness without
patches.  Two more images control the soundness statements: `always_yes` is
the exit0 image, which answers yes on every input, and `always_no` is
`Checks.GatedSize.exit1_image`, which answers no.

## Positive controls (`proofs/`), which must pass

| statement | shape | result |
|---|---|---|
| `toy/exit0/plain_halts` | `halts_within_budget` | proved (`Proof.v`) |
| `toy/exit0/plain_halts_may_fail` | `halts_may_fail` | proved |
| `toy/exit0/padded_agrees` | `agrees` | proved: two different binaries with equal traces |
| `toy/exit1/plain_halts` | `halts_within_budget` | refuted (`Refutation.v`): exit status 1 is not allowed |
| `toy/ebreak/*`, the other 28 | `halts_within_budget`, `halts_may_fail` and the seven agreement shapes; `disagrees_at_most` and `disagrees_at_most_rv64gc` at every bound below 1 (`asan_disagrees_at_most_*_below_1`); the classifier problem `classifies` and `classifies_rv64gc` for a classifier that accepts everything (`asan_classifies_*_accept_all`) | refuted: the plain run is never refused memory and reaches an error |
| `toy/ebreak/asan_c*_total`, `asan_maybe_*_no_distribution` (4) | `classifier_total3`, `maybe_empty`, for classifiers A and B | refuted: the classifier (lps's ebreak image) faults, so it gives no answer on lps's finite input |
| `toy/ebreak/asan_maybe_*_below_1`, `asan_bound_*_below_1` (4) | `maybe_at_most`, `classifier_rejects_at_most` at every bound below 1, for A and B | refuted: that input, which the classifier gives no firm answer and does not accept, weighs the whole mass |
| `toy/ebreak/asan_ca_sound_*_accept_all` (4) | `classifies_good_inputs_sound`, in each reading and with each originals, for a classifier that always answers yes (`Images.always_yes`) | refuted: it answers yes on lps's finite input, on which the builds disagree |
| `toy/ebreak/asan_cb_sound_*_reject_all` (4) | `classifies_patch_diff_sound`, in each reading and with each originals, for a classifier that always answers no (`Images.always_no`) | refuted: it answers no on lps's finite input, on which each build agrees with itself, its original |

The `toy/ebreak` refutations are the falsifiability controls: one statement
of each kind at each budget (`Budgets.Standard`, `Budgets.Asan`),
environment (`Env.may_fail`, `Env.alloc_forced_only`), abort reading,
machine and exit set the generator writes, and one classifier statement of
each kind for each classifier, reading and originals, with the toy
distribution and, for `classifier-maybe`, without one, each proved false (the
bound and classifier statements through their `_below_1`, `_accept_all` and
`_reject_all` controls).  A classifier-sound statement is written with its
classifier a parameter `C`, where the generator names the pair's classifier
image: the toy's classifiers give no answer, so they are sound for every
property.
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

`proofs/lib/Exit0Run.v`, `proofs/lib/EbreakRun.v` and
`proofs/lib/ClassifierRun.v` hold what they share.
They use lps's executable checker and test library
(`LinuxProcessSemantics.LinuxProcessSem.Checks`), and `EbreakRun.v` and
`ClassifierRun.v` also `theories/Premises.v`, `ClassifierRun.v` also
`theories/ClassifierShapes.v`; nothing else.  `proofs/lib/Exit0Instance.v` and
`proofs/lib/EbreakInstance.v` hold what the instance controls share (below).

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

## Instance controls (`instances/`)

An instance is one input file on which every premise of a statement holds
together (harness.yaml `statements.<s>.instance`).  `oft check` checks its
lemma, `<s>_instance` in `lib/Instances/<s>.v` of the proof library, with a
wrapper.  The wrapper defines the input from the bytes of the instance file and
gives the lemma the type that the shape of the statement makes
(`tools/oft/check.py`, `check_instance`).  It defines the input and the type
before it loads the proof library, so a file of the library cannot change the
meaning of a name in them.  The toys have no `harness.yaml`.
Thus each directory here holds an `instance.yaml` with the statement, its
fields, `argv0` and `input_file`, the instance record, a `project`, and a
`required` list that stands in for `REQUIRED` in `tools/oft/shapes.py`.  The
directory also holds the instance file and the lemma, `Instances/<s>.v`, or no
lemma.  It can also hold other `.v` files of the proof library that the lemma
loads: `Images.v` in the directory `<d>` is the module
`Control.<d>.Images`.  `./tests/check.sh` checks each directory with
`python3 -m oft.check --instance-control DIR`, which runs the same check.  A
directory with no `claim.yaml` must pass.  A directory with a `claim.yaml` must
be refused at the step that it names, and the output must contain its
`because`.

There is one passing control for each form of the type that the wrapper gives
(`shapes.instance_type`): the two halting shapes on the exit0 toy, and, on the
ebreak toy, whose `Images.v` names a plain and an ASan build, each of the
seven agreement shapes, and the bound and the decidability shape on each
machine.  Each form also has a `wrong_type` or `wrong_type_<form>` control: a
lemma of the type of a neighbouring form, on the same input, which the wrapper
refuses.  The bound and the decidability shapes give the same form of type,
but each has its own controls.  Most of the ebreak toy's statements are
refuted (above), but an instance shows only that the premises of a statement
hold together on one input, and here they do: lps's ebreak image faults at
its first instruction, so its run is never refused memory
(`proofs/lib/EbreakInstance.v`).

| control | statement | result |
|---|---|---|
| `plain_halts` | `toy/exit0/plain_halts` | passes: a `Qed` lemma on a 7-byte file, path `reaches-harness` |
| `plain_halts_may_fail` | `toy/exit0/plain_halts_may_fail` | passes: a `Qed` lemma on an empty file, path `refused-by-driver` |
| `asan_agrees_asan` | `toy/ebreak/asan_agrees_asan` | passes: a `Qed` lemma of the form of `agrees`, on a 7-byte file, path `reaches-harness` |
| `asan_agrees_abort_modelled_standard` | `toy/ebreak/asan_agrees_abort_modelled_standard` | passes: `agrees_abort_modelled`, on an empty file, path `refused-by-driver` |
| `asan_agrees_in_asan` | `toy/ebreak/asan_agrees_in_asan` | passes: `agrees_in`, on a 7-byte file, path `reaches-harness` |
| `asan_agrees_in_abort_modelled_standard` | `toy/ebreak/asan_agrees_in_abort_modelled_standard` | passes: `agrees_in_abort_modelled`, on an empty file, path `refused-by-driver` |
| `asan_agrees_rv64gc_asan` | `toy/ebreak/asan_agrees_rv64gc_asan` | passes: `agrees_rv64gc`, on a 7-byte file, path `reaches-harness` |
| `asan_agrees_abort_modelled_rv64gc_standard` | `toy/ebreak/asan_agrees_abort_modelled_rv64gc_standard` | passes: `agrees_abort_modelled_rv64gc`, on an empty file, path `refused-by-driver` |
| `asan_agrees_in_rv64gc_asan` | `toy/ebreak/asan_agrees_in_rv64gc_asan` | passes: `agrees_in_rv64gc`, on a 7-byte file, path `reaches-harness` |
| `asan_disagrees_at_most_may_fail` | `toy/ebreak/asan_disagrees_at_most_may_fail` | passes: `disagrees_at_most`, a finite input with a 7-byte file, path `reaches-harness` |
| `asan_disagrees_at_most_rv64gc_alloc_forced_only` | `toy/ebreak/asan_disagrees_at_most_rv64gc_alloc_forced_only` | passes: `disagrees_at_most_rv64gc`, a finite input with an empty file, path `refused-by-driver` |
| `asan_agreement_decidable_alloc_forced_only` | `toy/ebreak/asan_agreement_decidable_alloc_forced_only` | passes: `agreement_decidable`, a finite input with an empty file, path `refused-by-driver` |
| `asan_agreement_decidable_rv64gc_may_fail` | `toy/ebreak/asan_agreement_decidable_rv64gc_may_fail` | passes: `agreement_decidable_rv64gc`, a finite input with a 7-byte file, path `reaches-harness` |
| `no_lemma` | `toy/exit0/plain_halts` | passes: no lemma, and the project is not in `required` |
| `other_bytes` | `toy/exit0/plain_halts` | refused at wrapper: the lemma is about a file of other bytes |
| `wrong_type` | `toy/exit0/plain_halts` | refused at wrapper: the lemma has the type of `halts_may_fail`, which has no budget premise |
| `wrong_type_may_fail` | `toy/exit0/plain_halts_may_fail` | refused at wrapper: the lemma has the type of `halts_within_budget`, which adds the budget premise |
| `wrong_type_agrees` | `toy/ebreak/asan_agrees_asan` | refused at wrapper: the lemma has the type of `agrees_in`, whose budget premise is over `run_scfg` |
| `wrong_type_agrees_abort_modelled` | `toy/ebreak/asan_agrees_abort_modelled_standard` | refused at wrapper: the lemma has the type of `agrees_in_abort_modelled`, whose budget premise is over `run_scfg` |
| `wrong_type_agrees_in` | `toy/ebreak/asan_agrees_in_asan` | refused at wrapper: the lemma has the type of `agrees`, whose budget premise is over `run` |
| `wrong_type_agrees_in_abort_modelled` | `toy/ebreak/asan_agrees_in_abort_modelled_standard` | refused at wrapper: the lemma has the type of `agrees_abort_modelled`, whose budget premise is over `run` |
| `wrong_type_agrees_rv64gc` | `toy/ebreak/asan_agrees_rv64gc_asan` | refused at wrapper: the lemma has the type of `agrees`, whose input predicate `valid_input` allows either AT_HWCAP word |
| `wrong_type_agrees_abort_modelled_rv64gc` | `toy/ebreak/asan_agrees_abort_modelled_rv64gc_standard` | refused at wrapper: the lemma has the type of `agrees_abort_modelled`, whose input predicate `valid_input_abort` allows either AT_HWCAP word |
| `wrong_type_agrees_in_rv64gc` | `toy/ebreak/asan_agrees_in_rv64gc_asan` | refused at wrapper: the lemma has the type of `agrees_in`, whose input predicate `valid_input` allows either AT_HWCAP word |
| `wrong_type_bound` | `toy/ebreak/asan_disagrees_at_most_may_fail` | refused at wrapper: the lemma has the type of `disagrees_at_most_rv64gc`, which adds the RV64GC word |
| `wrong_type_bound_rv64gc` | `toy/ebreak/asan_disagrees_at_most_rv64gc_alloc_forced_only` | refused at wrapper: the lemma has the type of `disagrees_at_most`, which leaves out the RV64GC word |
| `wrong_type_decidable` | `toy/ebreak/asan_agreement_decidable_alloc_forced_only` | refused at wrapper: the lemma has the type of `agreement_decidable_rv64gc`, which adds the RV64GC word |
| `wrong_type_decidable_rv64gc` | `toy/ebreak/asan_agreement_decidable_rv64gc_may_fail` | refused at wrapper: the lemma has the type of `agreement_decidable`, which leaves out the RV64GC word |
| `admitted` | `toy/exit0/plain_halts` | refused at axioms: the lemma is `Admitted`, so it is an axiom |
| `shadowed_images` | `toy/exit0/plain_halts` | refused at wrapper: the library's own `Images.v` names the plain image of the exit1 toy `plain`, and the lemma is about that image |
| `no_lemma_required` | `toy/exit0/plain_halts` | refused at missing: no lemma, and the project is in `required` |

## Mutation controls (`mutate.py`), which must be caught

`./tests/check.sh` ends by running `tests/mutate.py`.  For each statement kind
of `theories/Shapes.v`, and each shape of `theories/ClassifierShapes.v`, it
makes the kind vacuous, or true of every program, in a scratch copy, and
requires `dune build --root . theories tests` of the copy to fail at a file
other than the mutated one; an unmutated copy must build.  The mutations: for
each halting and agreement shape, a premise that contradicts its input
predicate (for `halts_may_fail`, `valid_input_abort inp`); for the bound
shapes (`disagrees_at_most`, `disagrees_at_most_rv64gc`,
`classifier_rejects_at_most`, `maybe_at_most`), a conclusion that holds at
every `b > 0`; for the decidability shapes, the `image_wf C` conjunct
dropped; for `classifier_total3`, a premise that contradicts
`valid_fin_input f`; for `classifies_good_inputs_sound`,
`classifies_patch_diff_sound` and `maybe_empty`, a premise that no valid
finite input meets.  In each copy the proofs of the own lemmas of `Shapes.v`
and `ClassifierShapes.v` (its `_is_copy` lemmas and bridges included) are
`Admitted`, since a mutation breaks some of them (an admitted lemma can only
let a file compile, never fail it).  A mutation that is not caught, or that no
longer applies to its file, fails `check.sh`.  So what these controls catch is
a change to `Shapes.v` or `ClassifierShapes.v` of these nineteen forms; a
change that edits a control together with the shape, in the same pull
request, is for review to catch.

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
