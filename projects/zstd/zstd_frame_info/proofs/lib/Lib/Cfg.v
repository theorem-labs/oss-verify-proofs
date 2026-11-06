(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall Dispatch SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Import ListNotations.
Open Scope bv_scope.

Definition ACFG : SpuriousCfg := alloc_only_cfg false.

Lemma acfg_family_off_in : forall i,
  injected_family_off ACFG i = true -> In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof.
  intros inp Hoff.
  pose proof (alloc_family_dispatched (bv_unsigned (in_sysno inp))) as Hdisp.
  revert Hoff Hdisp. unfold injected_family_off.
  destruct (injected_arm (bv_unsigned (in_sysno inp))) as [arm|]; intros Hoff Hdisp; [|discriminate Hoff].
  apply (Hdisp arm eq_refl).
  destruct (ia_family arm); cbv in Hoff; congruence.
Qed.

Lemma acfg_family_on_notin : forall i,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> injected_family_off ACFG i = false.
Proof.
  intros inp Hout. apply not_true_is_false.
  intro Hon. exact (Hout (acfg_family_off_in inp Hon)).
Qed.

Lemma acfg_nonspurious : forall i m eff,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros inp mdl ef Hout.
  exact (spurious_refusal_family_on ACFG inp mdl ef (acfg_family_on_notin inp Hout)).
Qed.

Definition alloc_no_b (n : Z) : bool :=
  existsb (fun k => Z.eqb n k) alloc_mark_sysnos.

Lemma alloc_no_b_false : forall n, alloc_no_b n = false -> ~ In n alloc_mark_sysnos.
Proof.
  intros n Hb Hin. unfold alloc_no_b in Hb.
  rewrite (proj2 (existsb_exists (fun k => Z.eqb n k) alloc_mark_sysnos)) in Hb; [discriminate Hb|].
  exists n. split; [exact Hin | exact (Z.eqb_refl n)].
Qed.

Lemma acfg_nonspurious_no : forall segs ms x8 n m eff,
  bv_unsigned x8 = n -> alloc_no_b n = false ->
  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) m eff.
Proof.
  intros segs ms x8 n m eff Hno Hb. apply acfg_nonspurious.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. apply alloc_no_b_false. exact Hb.
Qed.

Lemma acfg_family_off_222 : forall i, bv_unsigned (in_sysno i) = 222%Z -> injected_family_off ACFG i = true.
Proof.
  intros inp Hno. unfold injected_family_off.
  replace (bv_unsigned (in_sysno inp)) with 222%Z by (symmetry; exact Hno). reflexivity.
Qed.
Lemma acfg_family_off_226 : forall i, bv_unsigned (in_sysno i) = 226%Z -> injected_family_off ACFG i = true.
Proof.
  intros inp Hno. unfold injected_family_off.
  replace (bv_unsigned (in_sysno inp)) with 226%Z by (symmetry; exact Hno). reflexivity.
Qed.
Lemma acfg_family_off_216 : forall i, bv_unsigned (in_sysno i) = 216%Z -> injected_family_off ACFG i = true.
Proof.
  intros inp Hno. unfold injected_family_off.
  replace (bv_unsigned (in_sysno inp)) with 216%Z by (symmetry; exact Hno). reflexivity.
Qed.
Lemma acfg_family_off_214 : forall i, bv_unsigned (in_sysno i) = 214%Z -> injected_family_off ACFG i = true.
Proof.
  intros inp Hno. unfold injected_family_off.
  replace (bv_unsigned (in_sysno inp)) with 214%Z by (symmetry; exact Hno). reflexivity.
Qed.

Lemma refusal_b_222 : forall i m r, bv_unsigned (in_sysno i) = 222%Z ->
  refusal_b i m r = ret_in_errnos mmap_errnos r.
Proof.
  intros inp mdl ret Hno. unfold refusal_b.
  replace (bv_unsigned (in_sysno inp)) with 222%Z by (symmetry; exact Hno). reflexivity.
Qed.
Lemma refusal_b_226 : forall i m r, bv_unsigned (in_sysno i) = 226%Z ->
  refusal_b i m r = ret_in_errnos mprotect_errnos r.
Proof.
  intros inp mdl ret Hno. unfold refusal_b.
  replace (bv_unsigned (in_sysno inp)) with 226%Z by (symmetry; exact Hno). reflexivity.
Qed.
Lemma refusal_b_216 : forall i m r, bv_unsigned (in_sysno i) = 216%Z ->
  refusal_b i m r = ret_in_errnos mremap_errnos r.
Proof.
  intros inp mdl ret Hno. unfold refusal_b.
  replace (bv_unsigned (in_sysno inp)) with 216%Z by (symmetry; exact Hno). reflexivity.
Qed.
Lemma refusal_b_214 : forall i m r, bv_unsigned (in_sysno i) = 214%Z ->
  refusal_b i m r = brk_refusal_b m (in_arg i 0) r.
Proof.
  intros inp mdl ret Hno. unfold refusal_b.
  replace (bv_unsigned (in_sysno inp)) with 214%Z by (symmetry; exact Hno). reflexivity.
Qed.

Lemma ret_in_errnos_ENOMEM : forall r,
  ret_in_errnos [ENOMEM] r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros w. exact (orb_false_r (bv_eqb w (errno_ret ENOMEM))).
Qed.

Lemma ret_in_errnos_errno : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros es e Hin. unfold ret_in_errnos. apply existsb_exists. exists e. split; [exact Hin|].
  apply bv_eqb_eq. reflexivity.
Qed.

Lemma refusal_spurious_of_grant : forall cfg i m eff eff' m' evs',
  injected_family_off cfg i = true ->
  refusal_b i m (eff_ret eff) = true ->
  syscall_spec i m (Ok eff' m' evs') ->
  refusal_b i m (eff_ret eff') = false ->
  spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg inp mdl ef ef' mdl' evs' Hoff Hrf Hspec Hgrant. unfold spurious_refusal_cfg.
  exact (conj Hoff (conj Hrf (ex_intro _ ef' (ex_intro _ mdl' (ex_intro _ evs' (conj Hspec Hgrant)))))).
Qed.

Lemma nonspurious_not_refusal_of_grant : forall cfg i m eff eff' m' evs',
  injected_family_off cfg i = true ->
  ~ spurious_refusal_cfg cfg i m eff ->
  syscall_spec i m (Ok eff' m' evs') ->
  refusal_b i m (eff_ret eff') = false ->
  refusal_b i m (eff_ret eff) = false.
Proof.
  intros cfg i m eff eff' m' evs' Hoff Hns Hs' Hnr.
  destruct (refusal_b i m (eff_ret eff)) eqn:R; [|reflexivity]. exfalso.
  exact (Hns (refusal_spurious_of_grant cfg i m eff eff' m' evs' Hoff R Hs' Hnr)).
Qed.

Lemma nonspurious_refusal_no_grant : forall cfg i m eff,
  ~ spurious_refusal_cfg cfg i m eff ->
  injected_family_off cfg i = true ->
  refusal_b i m (eff_ret eff) = true ->
  forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true.
Proof.
  intros cfg inp mdl ef Hns Hoff Hrf ef' mdl' evs' Hspec.
  apply not_false_is_true. intro Hgrant.
  exact (Hns (refusal_spurious_of_grant cfg inp mdl ef ef' mdl' evs' Hoff Hrf Hspec Hgrant)).
Qed.

Lemma not_spurious_forced : forall cfg i m eff,
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true) ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff Hall (_ & _ & eff' & m' & evs' & Hspec & Hnr).
  rewrite (Hall eff' m' evs' Hspec) in Hnr. discriminate Hnr.
Qed.

Lemma spurious_refusal_transport : forall cfg i1 i2 m eff,
  in_sysno i1 = in_sysno i2 ->
  in_arg i1 0 = in_arg i2 0 ->
  (forall eff' m' evs', syscall_spec i1 m (Ok eff' m' evs') <-> syscall_spec i2 m (Ok eff' m' evs')) ->
  spurious_refusal_cfg cfg i1 m eff <-> spurious_refusal_cfg cfg i2 m eff.
Proof.
  intros cfg ia ib mdl ef Hsys Harg Hiff.
  unfold spurious_refusal_cfg, injected_family_off, refusal_b. rewrite Hsys, Harg.
  split; intros (Hoff & Hrf & ef' & mdl' & evs' & Hspec & Hgrant);
    refine (conj Hoff (conj Hrf (ex_intro _ ef' (ex_intro _ mdl' (ex_intro _ evs' (conj _ Hgrant))))));
    apply Hiff; exact Hspec.
Qed.

Lemma exists_nonspurious : forall cfg i m eff0 m0 evs0,
  syscall_spec i m (Ok eff0 m0 evs0) ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg inp mdl ef0 mdl0 evs0 Hspec0.
  destruct (classic (spurious_refusal_cfg cfg inp mdl ef0)) as [Hsp|Hns].
  - destruct Hsp as (_ & _ & ef' & mdl' & evs' & Hspec' & Hgrant).
    exists ef', mdl', evs'. split; [exact Hspec'|].
    exact (spurious_refusal_not_refusal cfg inp mdl ef' Hgrant).
  - exists ef0, mdl0, evs0. split; [exact Hspec0 | exact Hns].
Qed.

Section Steps.
Variable segs : list Segment.

Lemma sstep_of_cfg : forall cfg c e st, sstep_cfg segs cfg c e st -> sstep segs c e st.
Proof. intros cfg c e st H. exact (sstep_cfg_sub segs cfg c e st H). Qed.

Lemma star_of_cfg : forall cfg c tr c', star_cfg segs cfg c tr c' -> star segs c tr c'.
Proof. intros cfg c tr c' H. exact (star_cfg_sub segs cfg c tr c' H). Qed.

Definition cfg_transparent (c : config) : Prop :=
  forall (e : list event) (st : step_to),
    sstep segs c e st -> sstep_cfg segs ACFG c e st.

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
  injected_family_off ACFG (sys_input segs ms x8) = false ->
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
  apply acfg_family_on_notin. exact Hnin.
Qed.

Lemma transparent_nonalloc_no : forall ms model x8 n,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n -> alloc_no_b n = false ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 n Hpend Hnum Hb. subst n.
  exact (transparent_nonalloc ms model x8 Hpend (alloc_no_b_false (bv_unsigned x8) Hb)).
Qed.

Lemma sstep_cfg_syscall_nonrefusal : forall cfg ms model x8 eff model' model'' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
  m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) = Some model'' ->
  sstep_cfg segs cfg (mkCfg ms model) evs
            (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')).
Proof.
  intros cfg ms model x8 eff model' model'' evs Hrun Hpend Hspec Hgrant Hrun' Hmat.
  pose proof (spurious_refusal_not_refusal cfg (sys_input segs ms x8) model eff Hgrant) as Hkeep.
  econstructor; eassumption.
Qed.

End Steps.

Section Star.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma star_cfg_one : forall c evs c',
  sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs). eapply star_cfg_step; [exact H | apply star_cfg_refl].
Qed.

Lemma star_cfg_trans : forall c1 tr1 c2 tr2 c3,
  star_cfg segs cfg c1 tr1 c2 -> star_cfg segs cfg c2 tr2 c3 ->
  star_cfg segs cfg c1 (tr1 ++ tr2) c3.
Proof.
  intros c1 tr1 c2 tr2 c3 H12 H23.
  induction H12 as [c | c evs c' tr c'' Hs Hst IH].
  - exact H23.
  - rewrite <- app_assoc. eapply star_cfg_step; [exact Hs | apply IH; exact H23].
Qed.

Lemma obs_trace_cfg_nil : forall c0, obs_trace_cfg segs cfg c0 [].
Proof. intros c0. exists [], c0. split; [apply star_cfg_refl | exact I]. Qed.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs cfg c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs cfg c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none. exact Hss.
Qed.

Lemma reaches_error_cfg_here : forall c evs,
  sstep_cfg segs cfg c evs SError -> reaches_error_cfg segs cfg c.
Proof. intros c evs H. exists [], c, evs. split; [apply star_cfg_refl | exact H]. Qed.

Lemma reaches_error_cfg_step : forall c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  reaches_error_cfg segs cfg c' -> reaches_error_cfg segs cfg c.
Proof.
  intros c evs c' Hs (tr & c2 & evs2 & Hst & He).
  exists (evs ++ tr), c2, evs2. split; [eapply star_cfg_step; eassumption | exact He].
Qed.

End Star.
