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
Local Open Scope bv_scope.
Definition ACFG : SpuriousCfg := alloc_only_cfg false.
Lemma acfg_family_off_in : forall i,
  injected_family_off ACFG i = true -> In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof.
  intros i Hoff. unfold injected_family_off in Hoff.
  set (no := bv_unsigned (in_sysno i)) in *.
  case_eq (injected_arm no).
  - intros a Ha. rewrite Ha in Hoff.
    apply (alloc_family_dispatched no a Ha).
    revert Hoff. case (ia_family a); cbn; congruence.
  - intros Ha. rewrite Ha in Hoff. destruct (diff_false_true Hoff).
Qed.

Lemma acfg_family_on_notin : forall i,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> injected_family_off ACFG i = false.
Proof.
  intros i Hn. apply not_true_is_false. intros Ht.
  exact (Hn (acfg_family_off_in i Ht)).
Qed.
Lemma acfg_nonspurious : forall i m eff,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff Hn (Hoff & _ & _).
  rewrite (acfg_family_on_notin i Hn) in Hoff. discriminate Hoff.
Qed.
Definition alloc_no_b (n : Z) : bool :=
  match List.find (Z.eqb n) alloc_mark_sysnos with Some _ => true | None => false end.
Lemma alloc_no_b_false : forall n, alloc_no_b n = false -> ~ In n alloc_mark_sysnos.
Proof.
  intros n H Hin. unfold alloc_no_b in H.
  destruct (List.find (Z.eqb n) alloc_mark_sysnos) eqn:E; [discriminate H|].
  pose proof (List.find_none _ _ E n Hin) as Hn. rewrite Z.eqb_refl in Hn. discriminate Hn.
Qed.
Lemma acfg_nonspurious_no : forall segs ms x8 n m eff,
  bv_unsigned x8 = n -> alloc_no_b n = false ->
  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) m eff.
Proof.
  intros segs ms x8 n m eff Hno Hb. apply acfg_nonspurious.
  change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. apply alloc_no_b_false. exact Hb.
Qed.
Lemma acfg_family_off_of_in : forall i,
  In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> injected_family_off ACFG i = true.
Proof.
  intros i. unfold injected_family_off.
  generalize (bv_unsigned (in_sysno i)) as no. intros no Hin.
  unfold alloc_mark_sysnos in Hin.
  repeat (apply in_inv in Hin; destruct Hin as [<-|Hin]; [reflexivity|]).
  apply in_nil in Hin. destruct Hin.
Qed.

Lemma acfg_family_off_222 : forall i, bv_unsigned (in_sysno i) = 222%Z -> injected_family_off ACFG i = true.
Proof.
  intros i Hno. apply acfg_family_off_of_in. rewrite Hno.
  unfold alloc_mark_sysnos. simpl. do 2 right. now left.
Qed.
Lemma acfg_family_off_226 : forall i, bv_unsigned (in_sysno i) = 226%Z -> injected_family_off ACFG i = true.
Proof.
  intros i Hno. apply acfg_family_off_of_in. rewrite Hno.
  unfold alloc_mark_sysnos. simpl. do 3 right. now left.
Qed.
Lemma acfg_family_off_216 : forall i, bv_unsigned (in_sysno i) = 216%Z -> injected_family_off ACFG i = true.
Proof.
  intros i Hno. apply acfg_family_off_of_in. rewrite Hno.
  unfold alloc_mark_sysnos. simpl. right. now left.
Qed.
Lemma acfg_family_off_214 : forall i, bv_unsigned (in_sysno i) = 214%Z -> injected_family_off ACFG i = true.
Proof.
  intros i Hno. apply acfg_family_off_of_in. rewrite Hno.
  unfold alloc_mark_sysnos. simpl. now left.
Qed.

Lemma refusal_b_222 : forall i m r, bv_unsigned (in_sysno i) = 222%Z ->
  refusal_b i m r = ret_in_errnos mmap_errnos r.
Proof.
  intros i m r; cbv beta zeta delta [refusal_b].
  generalize (bv_unsigned (in_sysno i)); intros ? ->; exact eq_refl.
Qed.
Lemma refusal_b_226 : forall i m r, bv_unsigned (in_sysno i) = 226%Z ->
  refusal_b i m r = ret_in_errnos mprotect_errnos r.
Proof.
  intros i m r; cbv beta zeta delta [refusal_b].
  generalize (bv_unsigned (in_sysno i)); intros ? ->; exact eq_refl.
Qed.
Lemma refusal_b_216 : forall i m r, bv_unsigned (in_sysno i) = 216%Z ->
  refusal_b i m r = ret_in_errnos mremap_errnos r.
Proof.
  intros i m r; cbv beta zeta delta [refusal_b].
  generalize (bv_unsigned (in_sysno i)); intros ? ->; exact eq_refl.
Qed.
Lemma refusal_b_214 : forall i m r, bv_unsigned (in_sysno i) = 214%Z ->
  refusal_b i m r = brk_refusal_b m (in_arg i 0) r.
Proof.
  intros i m r; cbv beta zeta delta [refusal_b].
  generalize (bv_unsigned (in_sysno i)); intros ? ->; exact eq_refl.
Qed.
Lemma ret_in_errnos_ENOMEM : forall r,
  ret_in_errnos [ENOMEM] r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intro r. unfold ret_in_errnos. cbn [existsb].
  destruct (bv_eqb r (errno_ret ENOMEM)); reflexivity.
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
  intros * Ho Hr Hs Hf.
  unfold spurious_refusal_cfg. refine (conj Ho (conj Hr _)).
  do 3 eexists. split; eassumption.
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
  intros * Hn Ho Hr e1 m1 v1 Hs.
  apply not_false_is_true. intro Hf.
  exact (Hn (conj Ho (conj Hr (ex_intro _ e1 (ex_intro _ m1 (ex_intro _ v1 (conj Hs Hf))))))).
Qed.

Lemma not_spurious_forced : forall cfg i m eff,
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true) ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff Hall (_ & _ & eff' & m' & evs' & Hspec & Hnr).
  rewrite (Hall eff' m' evs' Hspec) in Hnr. discriminate Hnr.
Qed.
Lemma refusal_b_input_eq : forall i1 i2 m r,
  in_sysno i1 = in_sysno i2 -> in_arg i1 0 = in_arg i2 0 ->
  refusal_b i1 m r = refusal_b i2 m r.
Proof.
  intros i1 i2 m r Hno Ha0. unfold refusal_b. rewrite <- Hno, <- Ha0. reflexivity.
Qed.

Lemma spurious_refusal_input_dir : forall cfg i1 i2 m eff,
  in_sysno i1 = in_sysno i2 ->
  in_arg i1 0 = in_arg i2 0 ->
  (forall e m' evs', syscall_spec i1 m (Ok e m' evs') -> syscall_spec i2 m (Ok e m' evs')) ->
  spurious_refusal_cfg cfg i1 m eff -> spurious_refusal_cfg cfg i2 m eff.
Proof.
  intros cfg i1 i2 m eff Hno Ha0 Hsp (Hoff & Hr & e & m1 & evs1 & Hs & Hn).
  assert (Hrb : forall r, refusal_b i2 m r = refusal_b i1 m r)
    by (intros r; symmetry; apply refusal_b_input_eq; assumption).
  unfold spurious_refusal_cfg. split; [|split].
  - unfold injected_family_off. rewrite <- Hno. exact Hoff.
  - rewrite Hrb. exact Hr.
  - exists e, m1, evs1. rewrite Hrb. split; [apply Hsp|]; assumption.
Qed.

Lemma spurious_refusal_transport : forall cfg i1 i2 m eff,
  in_sysno i1 = in_sysno i2 ->
  in_arg i1 0 = in_arg i2 0 ->
  (forall eff' m' evs', syscall_spec i1 m (Ok eff' m' evs') <-> syscall_spec i2 m (Ok eff' m' evs')) ->
  spurious_refusal_cfg cfg i1 m eff <-> spurious_refusal_cfg cfg i2 m eff.
Proof.
  intros cfg i1 i2 m eff Hno Ha0 Hspec. split.
  - apply spurious_refusal_input_dir; [exact Hno|exact Ha0|].
    intros e m1 evs1. exact (proj1 (Hspec e m1 evs1)).
  - apply spurious_refusal_input_dir; [symmetry; exact Hno|symmetry; exact Ha0|].
    intros e m1 evs1. exact (proj2 (Hspec e m1 evs1)).
Qed.
Lemma exists_nonspurious : forall cfg i m eff0 m0 evs0,
  syscall_spec i m (Ok eff0 m0 evs0) ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m e0 m0 l0 Hs0.
  destruct (classic (spurious_refusal_cfg cfg i m e0)) as [Hsp|Hns].
  - destruct Hsp as (_ & _ & eff1 & m1 & evs1 & Hs1 & Hr1).
    exists eff1, m1, evs1. split; [exact Hs1|]. apply spurious_refusal_not_refusal. exact Hr1.
  - exists e0, m0, l0. split; assumption.
Qed.

Lemma nonspurious_of_listing : forall cfg i m (I : Type) (effs : I -> SyscallEffect),
  (forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> exists j, eff = effs j) ->
  (forall j k, refusal_b i m (eff_ret (effs j)) = true -> refusal_b i m (eff_ret (effs k)) = true) ->
  forall j, ~ spurious_refusal_cfg cfg i m (effs j).
Proof.
  intros cfg i m I effs Hall Hu j (_ & Hr & eff' & m' & evs' & Hs & Hnr).
  destruct (Hall _ _ _ Hs) as [k ->]. rewrite (Hu j k Hr) in Hnr. discriminate Hnr.
Qed.
Lemma nonspurious_of_unique : forall cfg i m eff0,
  (forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> eff = eff0) ->
  ~ spurious_refusal_cfg cfg i m eff0.
Proof.
  intros cfg i m eff0 Hu (_ & Hr & eff' & m' & evs' & Hs & Hnr).
  rewrite (Hu _ _ _ Hs) in Hnr. rewrite Hr in Hnr. discriminate Hnr.
Qed.
Section Steps.
Variable segs : list Segment.

Lemma sstep_of_cfg : forall cfg c e st, sstep_cfg segs cfg c e st -> sstep segs c e st.
Proof. intros cfg c e st H. exact (sstep_cfg_sub segs cfg c e st H). Qed.
Lemma star_of_cfg : forall cfg c tr c', star_cfg segs cfg c tr c' -> star segs c tr c'.
Proof. intros cfg c tr c' H. exact (star_cfg_sub segs cfg c tr c' H). Qed.
Definition cfg_transparent (c : config) : Prop :=
  forall (evs : list event) (r : step_to),
    sstep segs c evs r -> sstep_cfg segs ACFG c evs r.
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
Lemma alloc_no_b_In : forall n, alloc_no_b n = true <-> In n alloc_mark_sysnos.
Proof.
  intros n. unfold alloc_no_b.
  destruct (List.find (Z.eqb n) alloc_mark_sysnos) as [k|] eqn:F; cbv beta iota.
  - apply List.find_some in F. destruct F as [Hk Hnk].
    apply Z.eqb_eq in Hnk. subst k.
    split; intros _; [exact Hk | reflexivity].
  - split; [intros Hc; discriminate Hc|]. intros Hn. exfalso.
    pose proof (List.find_none _ _ F n Hn) as C.
    rewrite Z.eqb_refl in C. discriminate C.
Qed.

Lemma transparent_nonalloc_no : forall ms model x8 n,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n -> alloc_no_b n = false ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 n Hp Hn Hfalse.
  subst n.
  apply transparent_nonalloc with (x8 := x8); [exact Hp |].
  intros Hin. apply alloc_no_b_In in Hin. rewrite Hin in Hfalse. discriminate Hfalse.
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
  intros * Ha Hb Hc Hfalse Hd He.
  refine (sstep_cfg_syscall segs cfg ms model x8 eff model' model'' evs Ha Hb Hc _ Hd He).
  unfold spurious_refusal_cfg. intros [_ [Htrue _]]. congruence.
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
Lemma star_cfg_inv (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs cfg c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star_cfg segs cfg c tr c' -> Inv c'.
Proof.
  intros c tr c' HInv Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hs Hst IH]; [exact HInv|].
  apply IH. eapply Hstep; eauto.
Qed.
Lemma inv_no_reaches_error_cfg (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs cfg c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep_cfg segs cfg c evs SError) :
  forall c, Inv c -> ~ reaches_error_cfg segs cfg c.
Proof.
  intros c HInv (tr & c' & evs & Hstar & Hss).
  eapply Hnoerr; [| exact Hss].
  eapply star_cfg_inv; eauto.
Qed.

End Star.