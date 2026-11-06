(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ncfg : SpuriousCfg := mkSpuriousCfg false true true true true true.

Lemma injected_family_off_nonalloc : forall (i : SyscallInput),
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  injected_family_off ncfg i = false.
Proof.
  intros i Hnin. unfold injected_family_off.
  destruct (injected_arm (bv_unsigned (in_sysno i))) as [a |] eqn:E; [| reflexivity].
  destruct (ia_family a) eqn:Ef; cbn [family_may_fail ncfg sc_alloc sc_fs sc_fd sc_net sc_cred sc_intr negb]; try reflexivity.
  exfalso. apply Hnin. exact (alloc_family_dispatched _ a E Ef).
Qed.

Lemma nonspurious_nonalloc : forall i m eff,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> ~ spurious_refusal_cfg ncfg i m eff.
Proof. intros i m eff H. apply spurious_refusal_family_on. apply injected_family_off_nonalloc. exact H. Qed.

Lemma not_alloc_sysno : forall (x8 : word) (z : Z),
  bv_unsigned x8 = z -> negb (existsb (Z.eqb z) alloc_mark_sysnos) = true ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros x8 z Hz Hb Hin. rewrite Hz in Hin. apply negb_true_iff in Hb.
  assert (existsb (Z.eqb z) alloc_mark_sysnos = true)
    by (apply existsb_exists; exists z; split; [exact Hin | apply Z.eqb_refl]).
  congruence.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma sstep_cfg_halted_none : forall cfg c e st,
  sstep_cfg segs cfg c e st -> m_halted (cfg_model c) = None.
Proof. intros cfg c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_halted_nil : forall cfg c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs cfg c tr c' -> tr = [] /\ c' = c.
Proof.
  intros cfg c tr c' Hh Hstar. inversion Hstar; subst; [split; reflexivity|].
  exfalso. apply Hh. eapply sstep_cfg_halted_none; eassumption.
Qed.

Lemma star_cfg_one : forall cfg c e c',
  sstep_cfg segs cfg c e (SNext c') -> star_cfg segs cfg c e c'.
Proof.
  intros cfg c e c' H. rewrite <- (app_nil_r e). eapply star_cfg_step; [exact H | apply star_cfg_refl].
Qed.

Lemma obs_trace_cfg_nil : forall cfg c, obs_trace_cfg segs cfg c [].
Proof. intros cfg c. exists [], c. split; [apply star_cfg_refl | exact I]. Qed.

Definition cfg_transparent (c : config) : Prop :=
  forall e st, sstep segs c e st -> sstep_cfg segs ncfg c e st.

Lemma transparent_instr : forall ms model,
  ms_svc_pending ms = None -> cfg_transparent (mkCfg ms model).
Proof.
  intros ms model Hsvc e st H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H1; discriminate H1 end).
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
Qed.

Lemma transparent_family_on : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  injected_family_off ncfg (sys_input segs ms x8) = false ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hoff e st H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1 end);
    match goal with H1 : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H1; injection H1; intro; subst y end.
  - eapply sstep_cfg_syscall; try eassumption. apply spurious_refusal_family_on. exact Hoff.
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption.
    apply spurious_refusal_family_on. exact Hoff.
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

Lemma transparent_nonalloc : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hnin. apply (transparent_family_on ms model x8 Hsvc).
  apply injected_family_off_nonalloc. exact Hnin.
Qed.

Lemma transparent_no : forall ms model x8 z,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = z ->
  negb (existsb (Z.eqb z) alloc_mark_sysnos) = true ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 z Hsvc Hz Hb. apply (transparent_nonalloc ms model x8 Hsvc).
  exact (not_alloc_sysno x8 z Hz Hb).
Qed.

Definition ret_of (c : config) : word := ms_gpr (cfg_ms c) 0.

End WithSegs.

Ltac not_alloc :=
  let F := fresh "F" in
  intros F; vm_compute in F; repeat (destruct F as [F|F]; [discriminate F|]); exact F.
