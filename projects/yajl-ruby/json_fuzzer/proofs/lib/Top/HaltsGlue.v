(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import LiaTuning.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState RegsEquiv RegsEquivCfg RunInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import HaltsGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

Section WithCfg.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

Lemma must_exit_in_at_cfg_eqv : forall S c,
  must_exit_in_at_cfg cfg segs S c ->
  forall c', cfg_eqv c c' -> must_exit_in_at_cfg cfg segs S c'.
Proof.
  intros S c H.
  induction H as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH]; intros c' Heqv.
  - destruct Heqv as [_ Hmo].
    apply (must_exit_in_at_cfg_halted cfg segs S c' code); [rewrite <- Hmo; exact Hh | exact Hin | rewrite <- Hmo; exact Hk].
  - apply must_exit_in_at_cfg_running.
    + destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hnone.
    + destruct Hprog as (evs & st & Hss).
      destruct (sstep_scfg_eqv segs cfg c c' evs st Heqv Hss) as (X' & Hss' & _).
      exists evs, X'. exact Hss'.
    + intros evs Hss'.
      destruct (sstep_scfg_eqv segs cfg c' c evs SError (cfg_eqv_sym _ _ Heqv) Hss') as (X & Hss & HX).
      destruct X as [c2 |]; cbn in HX; [contradiction |]. exact (Hnoerr evs Hss).
    + intros evs c2' Hss'.
      destruct (sstep_scfg_eqv segs cfg c' c evs (SNext c2') (cfg_eqv_sym _ _ Heqv) Hss') as (X & Hss & HX).
      destruct X as [c2 |]; cbn in HX; [| contradiction].
      apply (IH evs c2 Hss). apply cfg_eqv_sym. exact HX.
Qed.

End WithCfg.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma must_exit_in_scfg_of_ms0 : forall cfg segs pc ph lim S en inp,
  must_exit_in_at_cfg cfg segs S (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)) ->
  must_exit_in_scfg cfg S (mkImage segs pc ph) lim en inp.
Proof.
  intros cfg segs pc ph lim S [sp brk mb dr] inp H.
  cbn [must_exit_in_scfg].
  change (init_config segs pc ph sp brk mb dr lim inp)
    with (init_config segs pc ph (en_sp (mkEntry sp brk mb dr)) (en_brk (mkEntry sp brk mb dr))
                      (en_mmap_base (mkEntry sp brk mb dr)) (en_draw (mkEntry sp brk mb dr)) lim inp).
  rewrite init_config_eq.
  apply (must_exit_in_at_cfg_eqv cfg segs S _ H).
  split; [| reflexivity]. cbn [cfg_ms]. apply ms_eqv_sym. apply init_machine_state_eqv.
Qed.

(* [comment removed for export] *)
Lemma must_exit_in_scfg_fo_of_realizes_ms0 : forall cfg segs pc ph lim S en inp T,
  realizes_cfg cfg segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)) T ->
  exits_in S T ->
  must_exit_in_scfg forced_only_cfg S (mkImage segs pc ph) lim en inp.
Proof.
  intros cfg segs pc ph lim S en inp T HR HS.
  apply must_exit_in_scfg_of_ms0.
  apply (realizes_cfg_must_exit_in_fo cfg segs S _ T HR); [| exact HS].
  cbn [cfg_model]. apply mo0_not_halted.
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_of_realizes_ms0_premise :
  forall cfg segs pc ph lim S (T : ExecEntry -> ProcInput -> TSet),
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     source_within_budget_scfg forced_only_cfg lim (mkImage segs pc ph) en inp ->
     realizes_cfg cfg segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)) (T en inp)
     /\ exits_in S (T en inp)) ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lim S T H en inp HE HI HB.
  destruct (H en inp HE HI HB) as [HR HS].
  exact (must_exit_in_scfg_fo_of_realizes_ms0 cfg segs pc ph lim S en inp _ HR HS).
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_of_realizes_ms0 :
  forall cfg segs pc ph lim S (T : ProcInput -> TSet),
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     realizes_cfg cfg segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)) (T inp)) ->
  (forall inp, valid_input inp -> exits_in S (T inp)) ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lim S T HR HS.
  apply (halts_allowed_of_realizes_ms0_premise cfg segs pc ph lim S (fun _ inp => T inp)).
  intros en inp HE HI _. split; [exact (HR en inp HE HI) | exact (HS inp HI)].
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_of_realizes_init :
  forall cfg segs pc ph lim S (T : ProcInput -> TSet),
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     realizes_cfg cfg segs
       (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp)
       (T inp)) ->
  (forall inp, valid_input inp -> exits_in S (T inp)) ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lim S T HR HS [sp brk mb dr] inp HE HI _.
  cbn [must_exit_in_scfg].
  apply (realizes_cfg_must_exit_in_fo cfg segs S _ (T inp) (HR (mkEntry sp brk mb dr) inp HE HI));
    [reflexivity | exact (HS inp HI)].
Qed.
