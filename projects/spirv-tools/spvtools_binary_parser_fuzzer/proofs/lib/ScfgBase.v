(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import SimInv.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Definition CFG : SpuriousCfg := mkSpuriousCfg false true true true true true.

Definition alloc_sysno_b (n : Z) : bool :=
  (n =? 214)%Z || (n =? 216)%Z || (n =? 222)%Z || (n =? 226)%Z.

Lemma injected_family_off_CFG : forall i,
  injected_family_off CFG i = alloc_sysno_b (bv_unsigned (in_sysno i)).
Proof.
  intros i. unfold injected_family_off, injected_arm, alloc_sysno_b.
  set (n := bv_unsigned (in_sysno i)).
  unfold injected_table, lookup_injected.
  cbn [ia_no ia_family].
  repeat match goal with
         | |- context [Z.eqb ?k n] =>
             let E := fresh "E" in
             destruct (Z.eqb k n) eqn:E;
             [ apply Z.eqb_eq in E; rewrite <- E; reflexivity | ]
         end.
  repeat match goal with
         | E : Z.eqb ?k n = false |- _ =>
             apply Z.eqb_neq in E
         end.
  repeat match goal with
         | |- context [Z.eqb n ?k] =>
             let F := fresh "F" in
             destruct (Z.eqb n k) eqn:F;
             [ apply Z.eqb_eq in F; lia | ]
         end.
  reflexivity.
Qed.

Lemma injected_family_off_CFG_nonalloc : forall i,
  alloc_sysno_b (bv_unsigned (in_sysno i)) = false ->
  injected_family_off CFG i = false.
Proof. intros i H. rewrite injected_family_off_CFG. exact H. Qed.

Section WithSegs.
Variable segs : list Segment.

Definition sys_nonalloc (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
             injected_family_off CFG (sys_input segs (cfg_ms c) x8) = false.

Lemma sys_nonalloc_instr : forall ms model,
  ms_svc_pending ms = None -> sys_nonalloc (mkCfg ms model).
Proof. intros ms model H x8 H'. cbn in H'. congruence. Qed.

Lemma sys_nonalloc_sysno : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  alloc_sysno_b (bv_unsigned x8) = false ->
  sys_nonalloc (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hna y Hy. cbn in Hy. rewrite Hsvc in Hy. injection Hy as <-.
  apply injected_family_off_CFG_nonalloc. exact Hna.
Qed.

Lemma sstep_cfg_of_sstep : forall c e st,
  sys_nonalloc c ->
  sstep segs c e st -> sstep_cfg segs CFG c e st.
Proof.
  intros c e st Hna Hss.
  inversion Hss; subst.
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
  - eapply sstep_cfg_syscall; try eassumption.
    apply spurious_refusal_family_on. apply Hna. assumption.
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption.
    apply spurious_refusal_family_on. apply Hna. assumption.
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

Lemma not_spurious_of_not_refusal : forall i m eff,
  refusal_b i m (eff_ret eff) = false -> ~ spurious_refusal_cfg CFG i m eff.
Proof. intros i m eff H. apply spurious_refusal_not_refusal. exact H. Qed.

Lemma spurious_of_refusal : forall i m eff eff' m' evs',
  injected_family_off CFG i = true ->
  refusal_b i m (eff_ret eff) = true ->
  syscall_spec i m (Ok eff' m' evs') ->
  refusal_b i m (eff_ret eff') = false ->
  spurious_refusal_cfg CFG i m eff.
Proof.
  intros i m eff eff' m' evs' Hoff Hr Hs Hnr.
  split; [exact Hoff | split; [exact Hr |]]. exists eff', m', evs'. auto.
Qed.

Lemma not_spurious_forced : forall i m eff,
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true) ->
  ~ spurious_refusal_cfg CFG i m eff.
Proof.
  intros i m eff Hall (_ & _ & (eff' & m' & evs' & Hs & Hnr)).
  rewrite (Hall _ _ _ Hs) in Hnr. discriminate Hnr.
Qed.

Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m _.
  destruct (classic (exists eff' m' evs',
              syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false))
    as [H | H]; [left; exact H | right].
  intros eff' m' evs' Hs. destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity |].
  exfalso. apply H. exists eff', m', evs'. auto.
Qed.

Lemma star_cfg_one : forall c evs c',
  sstep_cfg segs CFG c evs (SNext c') -> star_cfg segs CFG c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs).
  econstructor; [exact H | apply star_cfg_refl].
Qed.

Lemma obs_trace_cfg_nil : forall c0, obs_trace_cfg segs CFG c0 [].
Proof.
  intros c0. exists [], c0. split; [apply star_cfg_refl | apply is_prefix_nil].
Qed.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs CFG c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_inv (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs CFG c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star_cfg segs CFG c tr c' -> Inv c'.
Proof.
  intros c tr c' HInv Hstar. induction Hstar; [exact HInv|].
  apply IHHstar. eapply Hstep; eauto.
Qed.

Lemma inv_no_reaches_error_cfg (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs CFG c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep_cfg segs CFG c evs SError) :
  forall c, Inv c -> ~ reaches_error_cfg segs CFG c.
Proof.
  intros c HInv (tr & c' & evs & Hstar & Hss).
  eapply Hnoerr; [| exact Hss].
  eapply star_cfg_inv; eauto.
Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs CFG c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
Qed.

End WithSegs.

Section SvcInv.
Variable segs : list Segment.

Lemma sstep_cfg_svc_inv : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs CFG (mkCfg ms model) e st ->
  (exists eff model' evs,
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
      /\ ((exists model'', ~ spurious_refusal_cfg CFG (sys_input segs ms x8) model eff
             /\ m_halted model' = None /\ e = evs
             /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
             /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          \/ (~ spurious_refusal_cfg CFG (sys_input segs ms x8) model eff
              /\ m_halted model' = None /\ e = []
              /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
              /\ st = SError)
          \/ (exists code, m_halted model' = Some code
              /\ e = evs ++ [halt_ev model' code]
              /\ st = SNext (mkCfg ms model'))))
  \/ (syscall_spec (sys_input segs ms x8) model Unmodeled /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    left. eexists. repeat split; eauto.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. left. repeat split; auto.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. right. eexists. repeat split; eauto.
    rewrite halt_ev_exit by assumption. reflexivity.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. right.
    match goal with Hk : m_killed ?mm = Some ?s |- _ =>
      exists s; split; [exact (m_halted_of_killed _ _ Hk) |];
      split; [rewrite (halt_ev_killed _ _ Hk); reflexivity | reflexivity]
    end.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. auto.
Qed.

End SvcInv.
