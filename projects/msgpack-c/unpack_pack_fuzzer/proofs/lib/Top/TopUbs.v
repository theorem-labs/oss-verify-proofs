(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeEF ShapeEFA.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.

Module TopUbs.

Definition SRC_SEGS := Plain.M.loaded_segments.
Definition SRC_PC := Plain.M.init_pc.
Definition SRC_PH := Plain.M.phdrs.
Definition SRC : Image := mkImage SRC_SEGS SRC_PC SRC_PH.
Definition UBS_SEGS := Ubsan.M.loaded_segments.
Definition UBS_PC := Ubsan.M.init_pc.
Definition UBS_PH := Ubsan.M.phdrs.
Definition UBS : Image := mkImage UBS_SEGS UBS_PC UBS_PH.

Definition valid_core (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ valid_creds inp /\ valid_nofile (in_nofile inp) /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_va_size inp = Sv48.
Lemma valid_core_of_input : forall inp, valid_input inp -> valid_core inp.
Proof. intros inp H. unfold valid_input in H. unfold valid_core. tauto. Qed.
Lemma valid_core_of_abort : forall inp, valid_input_abort inp -> valid_core inp.
Proof. intros inp H. unfold valid_input_abort in H. unfold valid_core. tauto. Qed.

Section TOP.
  Variable K : ProcInput -> TSet.
  Hypothesis K_kill_free : forall inp, valid_core inp -> kill_free (K inp).
  Hypothesis RZ_SRC : forall sp brk0 mb rnd inp,
    valid_core inp -> valid_entry SRC (mkEntry sp brk0 mb rnd) inp ->
    realizes SRC_SEGS (init_config SRC_SEGS SRC_PC SRC_PH sp brk0 mb rnd source_alloc_limit inp) (K inp).
  Hypothesis RZ_UBS : forall sp brk0 mb rnd inp,
    valid_core inp -> valid_entry UBS (mkEntry sp brk0 mb rnd) inp ->
    realizes UBS_SEGS (init_config UBS_SEGS UBS_PC UBS_PH sp brk0 mb rnd target_alloc_limit inp) (K inp).

  Theorem base_ubsan :
    strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
      ShippedBudgets.lim_source ShippedBudgets.lim_target SRC UBS.
  Proof.
    intros [sp1 b1 m1 r1] [sp2 b2 m2 r2] inp Hs Ht Hv _.
    pose proof (valid_core_of_abort inp Hv) as Hc.
    unfold strong_equiv_error_free_budgets_scfg_abort, ShippedBudgets.lim_source, ShippedBudgets.lim_target.
    exact (shape_strong_equiv_efa SRC_SEGS SRC_PC SRC_PH sp1 b1 m1 r1 source_alloc_limit
             UBS_SEGS UBS_PC UBS_PH sp2 b2 m2 r2 target_alloc_limit (K inp) inp
             (RZ_SRC sp1 b1 m1 r1 inp Hc Hs) (RZ_UBS sp2 b2 m2 r2 inp Hc Ht) (K_kill_free inp Hc)).
  Qed.
End TOP.

End TopUbs.
