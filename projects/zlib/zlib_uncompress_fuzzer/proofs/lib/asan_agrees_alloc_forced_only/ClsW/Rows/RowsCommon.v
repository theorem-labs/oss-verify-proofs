(** a worker (JOB 1 PART B), RowsCommon: the bound rows of an accept-all classifier, at any bound [b]
    with [0 <= b * M].  The proof is the one of AcceptAllGeneric.rejects_at_most_zero_of_accepts_all with the last
    step generalised: an accept-all classifier rejects no input, so the only rejected list is the empty one, whose
    weight is 0.  No axiom, no parameter, no unfinished proof. *)
From Stdlib Require Import ZArith QArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier Measure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.OSSV Require Import Images Shapes ClassifierShapes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls Require Import AcceptAllGeneric.
Import ListNotations.

Lemma weight_bound_of_accepts_all : forall C w M b,
  accepts_all C ->
  (0 <= b * M)%Q ->
  LinuxProcessSemantics.EquivalenceDefinition.Measure.weight_bound_T_fo C w M b.
Proof.
  intros C w M b H Hb l _ Hall.
  destruct l as [| f l].
  - rewrite sum_weights_nil. exact Hb.
  - exfalso. exact (accepts_all_not_rejects C f H (Hall f (or_introl eq_refl))).
Qed.
