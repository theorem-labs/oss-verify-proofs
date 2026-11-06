(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool.
From Stdlib Require Import Logic.Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg RealizesAbort.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m _.
  destruct (classic (exists eff' m' evs',
              syscall_spec i m (Ok eff' m' evs')
              /\ refusal_b i m (eff_ret eff') = false)) as [H | H];
    [left; exact H | right].
  intros eff' m' evs' Hs.
  destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity | exfalso].
  apply H. exists eff', m', evs'. split; [exact Hs | exact E].
Qed.

(* [comment removed for export] *)
Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.

(* [comment removed for export] *)
Lemma must_exit_in_at_cfg_mono_classic : forall cfg1 cfg2 segs S c,
  cfg_le cfg1 cfg2 ->
  must_exit_in_at_cfg cfg2 segs S c ->
  must_exit_in_at_cfg cfg1 segs S c.
Proof.
  intros cfg1 cfg2 segs S c Hle H.
  exact (must_exit_in_at_cfg_mono cfg1 cfg2 segs S c Hle (decided_from_classic cfg1 segs c) H).
Qed.

Lemma must_exit_in_scfg_mono_classic : forall cfg1 cfg2 S img lim en inp,
  cfg_le cfg1 cfg2 ->
  must_exit_in_scfg cfg2 S img lim en inp ->
  must_exit_in_scfg cfg1 S img lim en inp.
Proof.
  intros cfg1 cfg2 S [segs pc ph] lim [sp brk0 mbase rnd] inp Hle H.
  cbn [must_exit_in_scfg] in *.
  exact (must_exit_in_at_cfg_mono_classic _ _ _ _ _ Hle H).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition exits_in (S : list word) (T : TSet) : Prop :=
  forall tr code fs, T (tr ++ [ExitEv code fs]) -> In code S.

Definition kill_free (T : TSet) : Prop :=
  forall tr sig fs, ~ T (tr ++ [KillEv sig fs]).

Lemma exits_in_eq : forall S T T', t_eq T T' -> exits_in S T' -> exits_in S T.
Proof. intros S T T' Heq H tr code fs Htr. apply (H tr code fs). apply Heq. exact Htr. Qed.

Lemma kill_free_eq : forall T T', t_eq T T' -> kill_free T' -> kill_free T.
Proof. intros T T' Heq H tr sig fs Htr. apply (H tr sig fs). apply Heq. exact Htr. Qed.

(* [comment removed for export] *)
Lemma node_shape_cont : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i tr,
  T i tr -> t_alt (fun j => t_emit (evs j) (T j)) (evs i ++ tr).
Proof. intros I evs T i tr Htr. exists i. right. exists tr. split; [reflexivity | exact Htr]. Qed.

Lemma node_shape_self : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  t_alt (fun j => t_emit (evs j) (T j)) (evs i).
Proof. intros I evs T i. exists i. left. apply is_prefix_refl. Qed.

Lemma exits_in_cont : forall S (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  exits_in S (t_alt (fun j => t_emit (evs j) (T j))) -> exits_in S (T i).
Proof.
  intros S I evs T i H tr code fs Htr.
  apply (H (evs i ++ tr) code fs). rewrite <- app_assoc. apply node_shape_cont. exact Htr.
Qed.

Lemma kill_free_cont : forall (I : Type) (evs : I -> list event) (T : I -> TSet) i,
  kill_free (t_alt (fun j => t_emit (evs j) (T j))) -> kill_free (T i).
Proof.
  intros I evs T i H tr sig fs Htr.
  apply (H (evs i ++ tr) sig fs). rewrite <- app_assoc. apply node_shape_cont. exact Htr.
Qed.

Section WithSegsCfg.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable S : list word.

(* [comment removed for export] *)
#[using="Type"] Theorem realizes_cfg_must_exit_in : forall c T,
  realizes_cfg segs cfg c T ->
  m_halted (cfg_model c) = None ->
  exits_in S T ->
  kill_free T ->
  must_exit_in_at_cfg cfg segs S c.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros Hnone HE HK.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running.
    + exact Hnone.
    + exists (evs i0), (SNext (nx i0)). apply Hcomp.
    + intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Hbad). discriminate Hbad.
    + intros e c' Hss.
      destruct (Hsound e (SNext c') Hss) as (i & He & Hc'). injection Hc' as Hc'. subst e c'.
      destruct (m_halted (cfg_model (nx i))) as [code |] eqn:Hh.
      * destruct (sstep_cfg_next_halts_by_exit _ _ _ _ _ Hss)
          as [Hn | [(evs0 & code0 & Hevs & Hcode0 & Hk0) | (evs0 & sig & Hevs & Hsig)]].
        -- exfalso. rewrite Hn in Hh. discriminate Hh.
        -- apply (must_exit_in_at_cfg_halted cfg segs S (nx i) code0 Hcode0); [| exact Hk0].
           apply (HE evs0 code0 (m_fs (cfg_model (nx i)))). rewrite <- Hevs. apply node_shape_self.
        -- exfalso. apply (HK evs0 sig (m_fs (cfg_model (nx i)))). rewrite <- Hevs. apply node_shape_self.
      * apply (IH i Hh).
        -- exact (exits_in_cont S I evs T i HE).
        -- exact (kill_free_cont I evs T i HK).
  - exfalso. exact (Hh Hnone).
  - apply IH; [exact Hnone | exact (exits_in_eq S T T' Heq HE) | exact (kill_free_eq T T' Heq HK)].
Qed.

End WithSegsCfg.

(* [comment removed for export] *)
Theorem realizes_cfg_must_exit_in_le : forall segs cfg1 cfg2 S c T,
  cfg_le cfg1 cfg2 ->
  realizes_cfg segs cfg2 c T ->
  m_halted (cfg_model c) = None ->
  exits_in S T ->
  kill_free T ->
  must_exit_in_at_cfg cfg1 segs S c.
Proof.
  intros segs cfg1 cfg2 S c T Hle HR Hnone HE HK.
  apply (must_exit_in_at_cfg_mono_classic cfg1 cfg2 segs S c Hle).
  exact (realizes_cfg_must_exit_in segs cfg2 S c T HR Hnone HE HK).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition spec_exits_in (S : list word) (Spec : ProcInput -> TSet) : Prop :=
  forall inp, exits_in S (Spec inp).

Lemma no_kill_kill_free : forall Spec inp, no_kill Spec -> kill_free (Spec inp).
Proof.
  intros Spec inp HK tr sig fs Htr.
  apply (HK inp (tr ++ [KillEv sig fs]) sig fs Htr).
  apply in_app_iff. right. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma must_exit_in_scfg_of_realizes : forall cfg1 cfg2 segs pc ph sp brk0 mb rnd lim inp S T,
  cfg_le cfg1 cfg2 ->
  realizes_cfg segs cfg2 (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  exits_in S T ->
  kill_free T ->
  must_exit_in_scfg cfg1 S (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros cfg1 cfg2 segs pc ph sp brk0 mb rnd lim inp S T Hle HR HE HK.
  cbn [must_exit_in_scfg].
  apply (realizes_cfg_must_exit_in_le segs cfg1 cfg2 S _ T Hle HR); [| exact HE | exact HK].
  cbn [init_config cfg_model]. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem halts_allowed_of_realizes : forall cfg1 cfg2 segs pc ph lim S Spec,
  cfg_le cfg1 cfg2 ->
  image_realizes_cfg_e cfg2 segs pc ph lim Spec ->
  spec_exits_in S Spec ->
  no_kill Spec ->
  halts_allowed_T_scfg_budgets cfg1 lim S (mkImage segs pc ph).
Proof.
  intros cfg1 cfg2 segs pc ph lim S Spec Hle HR HE HK [sp brk0 mb rnd] inp Hven Hinp _.
  apply (must_exit_in_scfg_of_realizes cfg1 cfg2 segs pc ph sp brk0 mb rnd lim inp S (Spec inp) Hle).
  - apply HR; [exact Hven | exact (valid_input_either_of_valid_input _ Hinp)].
  - exact (HE inp).
  - exact (no_kill_kill_free Spec inp HK).
Qed.

(* [comment removed for export] *)
Corollary halts_allowed_forced_only_of_realizes : forall cfg segs pc ph lim S Spec,
  image_realizes_cfg_e cfg segs pc ph lim Spec ->
  spec_exits_in S Spec ->
  no_kill Spec ->
  halts_allowed_T_scfg_budgets forced_only_cfg lim S (mkImage segs pc ph).
Proof.
  intros cfg segs pc ph lim S Spec HR HE HK.
  exact (halts_allowed_of_realizes forced_only_cfg cfg segs pc ph lim S Spec
           (forced_only_cfg_least cfg) HR HE HK).
Qed.

(* [comment removed for export] *)
Corollary halts_allowed_scfg_of_realizes : forall cfg1 cfg2 segs pc ph S Spec,
  cfg_le cfg1 cfg2 ->
  image_realizes_cfg_e cfg2 segs pc ph source_alloc_limit Spec ->
  spec_exits_in S Spec ->
  no_kill Spec ->
  halts_allowed_T_scfg cfg1 S (mkImage segs pc ph).
Proof.
  intros cfg1 cfg2 segs pc ph S Spec Hle HR HE HK [sp brk0 mb rnd] inp Hven Hinp.
  apply (must_exit_in_scfg_of_realizes cfg1 cfg2 segs pc ph sp brk0 mb rnd source_alloc_limit inp S (Spec inp) Hle).
  - apply HR; [exact Hven | exact (valid_input_either_of_valid_input _ Hinp)].
  - exact (HE inp).
  - exact (no_kill_kill_free Spec inp HK).
Qed.

(* [comment removed for export] *)
