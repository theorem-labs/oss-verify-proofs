(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition ncfg : SpuriousCfg := mkSpuriousCfg false true true true true true.

Lemma ncfg_alloc_only : ncfg = alloc_only_cfg false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
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

Lemma star_cfg_trans : forall cfg c1 t1 c2 t2 c3,
  star_cfg segs cfg c1 t1 c2 -> star_cfg segs cfg c2 t2 c3 -> star_cfg segs cfg c1 (t1 ++ t2) c3.
Proof.
  intros cfg c1 t1 c2 t2 c3 H1 H2. induction H1 as [c|ca evs cb tr cc Hss Hst IH]; [exact H2|].
  rewrite <- app_assoc. eapply star_cfg_step; [exact Hss| exact (IH H2)].
Qed.

Lemma obs_trace_cfg_nil : forall cfg c, obs_trace_cfg segs cfg c [].
Proof. intros cfg c. exists [], c. split; [apply star_cfg_refl | exact I]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma transparent_no : forall ms model x8 z,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = z ->
  negb (existsb (Z.eqb z) alloc_mark_sysnos) = true ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 z Hsvc Hz Hb. apply (transparent_nonalloc ms model x8 Hsvc).
  exact (not_alloc_sysno x8 z Hz Hb).
Qed.

(* [comment removed for export] *)
Lemma transparent_sub : forall c e st, cfg_transparent c -> sstep segs c e st <-> sstep_cfg segs ncfg c e st.
Proof. intros c e st Ht. split; [apply Ht | apply sstep_cfg_sub]. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ret_of (c : config) : word := ms_gpr (cfg_ms c) 0.

Lemma ret_of_apply_effect : forall ms eff model,
  ret_of (mkCfg (advance_past_svc (apply_effect ms eff)) model) = eff_ret eff.
Proof.
  intros ms eff model. unfold ret_of, ms_gpr. cbn [cfg_ms advance_past_svc apply_effect ms_regs].
  unfold set_reg.
  destruct (bv_eqb _ _) eqn:E; [vm_compute in E; discriminate E |].
  cbn [ms_regs]. unfold Sem.reg_get.
  replace (Z_to_bv 5 (10 + Z.of_nat 0)) with (10 : reg) by (apply bv_eq; reflexivity).
  rewrite bvmap_get_set_same. reflexivity.
Qed.

Lemma sstep_cfg_svc_inv' : forall cfg ms model x8 e c',
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs cfg (mkCfg ms model) e (SNext c') ->
  (exists eff model' model'',
     syscall_spec (sys_input segs ms x8) model (Ok eff model' e)
     /\ ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff
     /\ m_halted model' = None
     /\ c' = mkCfg (advance_past_svc (apply_effect ms eff)) model'')
  \/ (exists model', m_halted model' <> None /\ c' = mkCfg ms model').
Proof.
  intros cfg ms model x8 e c' Hsvc H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1 end);
    match goal with H1 : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H1; injection H1; intro; subst y end.
  - left. do 3 eexists. split; [eassumption |]. split; [eassumption |]. split; [eassumption | reflexivity].
  - right. eexists. split; [| reflexivity]. match goal with H1 : m_halted ?m = Some _ |- _ => rewrite H1; discriminate end.
  - right. eexists. split; [| reflexivity].
    match goal with H1 : m_killed ?m = Some _ |- _ =>
      intro Hn; rewrite (m_killed_of_m_halted_none _ Hn) in H1; discriminate H1 end.
Qed.

Lemma sstep_svc_inv' : forall ms model x8 e c',
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) e (SNext c') ->
  (exists eff model' model'',
     syscall_spec (sys_input segs ms x8) model (Ok eff model' e)
     /\ m_halted model' = None
     /\ c' = mkCfg (advance_past_svc (apply_effect ms eff)) model'')
  \/ (exists model', m_halted model' <> None /\ c' = mkCfg ms model').
Proof.
  intros ms model x8 e c' Hsvc H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1 end);
    match goal with H1 : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H1; injection H1; intro; subst y end.
  - left. do 3 eexists. split; [eassumption |]. split; [eassumption | reflexivity].
  - right. eexists. split; [| reflexivity]. match goal with H1 : m_halted ?m = Some _ |- _ => rewrite H1; discriminate end.
  - right. eexists. split; [| reflexivity].
    match goal with H1 : m_killed ?m = Some _ |- _ =>
      intro Hn; rewrite (m_killed_of_m_halted_none _ Hn) in H1; discriminate H1 end.
Qed.

End WithSegs.

(* [comment removed for export] *)
Ltac not_alloc :=
  let F := fresh "F" in
  intros F; vm_compute in F; repeat (destruct F as [F|F]; [discriminate F|]); exact F.
