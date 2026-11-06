(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall Dispatch SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition ACFG : SpuriousCfg :=
  {| sc_alloc := false; sc_fs := true; sc_fd := true;
     sc_net := true; sc_cred := true; sc_intr := true |}.

Lemma ACFG_alloc : sc_alloc ACFG = false.
Proof.
  change (sc_alloc ACFG) with false. exact eq_refl.
Qed.
Lemma ACFG_fs : sc_fs ACFG = true.
Proof.
  change (sc_fs ACFG) with true. exact eq_refl.
Qed.
Lemma ACFG_fd : sc_fd ACFG = true.
Proof.
  change (sc_fd ACFG) with true. exact eq_refl.
Qed.
Lemma ACFG_net : sc_net ACFG = true.
Proof.
  change (sc_net ACFG) with true. exact eq_refl.
Qed.
Lemma ACFG_cred : sc_cred ACFG = true.
Proof.
  change (sc_cred ACFG) with true. exact eq_refl.
Qed.
Lemma ACFG_intr : sc_intr ACFG = true.
Proof.
  change (sc_intr ACFG) with true. exact eq_refl.
Qed.

Lemma ACFG_eq_alloc_only : ACFG = alloc_only_cfg false.
Proof.
  cbv delta [ACFG alloc_only_cfg]. exact eq_refl.
Qed.

Lemma forced_only_le_ACFG : cfg_le forced_only_cfg ACFG.
Proof.
  intros fam Hfam. destruct fam; cbn in Hfam |- *; [discriminate Hfam | exact eq_refl ..].
Qed.

Definition alloc_no_b (n : Z) : bool :=
  match List.find (Z.eqb n) alloc_mark_sysnos with Some _ => true | None => false end.

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

Lemma alloc_no_b_false : forall n, alloc_no_b n = false -> ~ In n alloc_mark_sysnos.
Proof.
  intros n Hf Hin.
  pose proof (proj2 (alloc_no_b_In n) Hin) as Ht.
  rewrite Hf in Ht. discriminate Ht.
Qed.

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

Lemma acfg_family_off_of_in : forall i,
  In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> injected_family_off ACFG i = true.
Proof.
  intros i. unfold injected_family_off.
  generalize (bv_unsigned (in_sysno i)) as no. intros no Hin.
  unfold alloc_mark_sysnos in Hin.
  repeat (apply in_inv in Hin; destruct Hin as [<-|Hin]; [reflexivity|]).
  apply in_nil in Hin. destruct Hin.
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

Lemma acfg_nonspurious_b : forall i m eff,
  alloc_no_b (bv_unsigned (in_sysno i)) = false ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros inp mo ef Hb Hsp.
  refine (acfg_nonspurious inp mo ef _ Hsp).
  intros Hin. rewrite (proj2 (alloc_no_b_In _) Hin) in Hb. discriminate Hb.
Qed.

Lemma in_sysno_sys_input : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof.
  intros segs ms x8. exact eq_refl.
Qed.

Lemma in_arg_sys_input : forall segs ms x8 k, (k < 6)%nat ->
  in_arg (sys_input segs ms x8) k = ms_gpr ms k.
Proof.
  intros segs ms x8 k Hk.
  assert (Hcase : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5)%nat) by lia.
  destruct Hcase as [-> | [-> | [-> | [-> | [-> | ->]]]]]; reflexivity.
Qed.

Lemma acfg_nonspurious_no : forall segs ms x8 n m eff,
  bv_unsigned x8 = n -> alloc_no_b n = false ->
  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) m eff.
Proof.
  intros * <- Hb.
  exact (acfg_nonspurious_b (sys_input segs ms x8) m eff Hb).
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

Lemma page_aligned_not_ENOMEM : forall a : word,
  (bv_unsigned a mod page_size = 0)%Z -> bv_eqb a (errno_ret ENOMEM) = false.
Proof.
  intros a Hal. unfold bv_eqb. apply Z.eqb_neq. intro Hu.
  assert (Hv : bv_unsigned (errno_ret ENOMEM) = 18446744073709551604%Z) by reflexivity.
  rewrite Hu, Hv in Hal. unfold page_size in Hal. lia.
Qed.

Lemma ret_in_errnos_ENOMEM_aligned : forall a : word,
  (bv_unsigned a mod page_size = 0)%Z -> ret_in_errnos [ENOMEM] a = false.
Proof.
  intros a Hal. unfold ret_in_errnos. cbn [existsb].
  rewrite (page_aligned_not_ENOMEM a Hal). reflexivity.
Qed.

Lemma ret_in_errnos_ENOMEM_zero : ret_in_errnos [ENOMEM] (Z_to_bv 64 0) = false.
Proof. reflexivity. Qed.

Section Transparent.
Variable segs : list Segment.

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
  intros ms model x8 Hp Hout.
  refine (transparent_family_on ms model x8 Hp _).
  destruct (injected_family_off ACFG (sys_input segs ms x8)) eqn:Eoff; [| reflexivity].
  exfalso. exact (Hout (acfg_family_off_in _ Eoff)).
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

Lemma sstep_of_cfg : forall c e st, sstep_cfg segs ACFG c e st -> sstep segs c e st.
Proof.
  intros cf evs r Hs.
  pose proof (may_fail_cfg_greatest ACFG) as Hle.
  apply sstep_cfg_may_fail.
  eapply sstep_cfg_mono; [exact Hle | exact Hs].
Qed.

Definition ret_of (c : config) : word := ms_gpr (cfg_ms c) 0.

Lemma gpr0_apply_effect : forall ms eff,
  ms_gpr (advance_past_svc (apply_effect ms eff)) 0 = eff_ret eff.
Proof.
  intros ms eff.
  assert (Hregs : ms_regs (advance_past_svc (apply_effect ms eff))
                  = bvmap_set (10 : reg) (eff_ret eff) (ms_regs ms)) by reflexivity.
  unfold ms_gpr. rewrite Hregs.
  unfold Sem.reg_get, bvmap_get, bvmap_set.
  change (bv_key (Z_to_bv 5 (10 + Z.of_nat 0))) with (@bv_key 5 (10 : reg)).
  rewrite tget_tset_same. reflexivity.
Qed.

Lemma ret_of_apply_effect : forall ms eff model,
  ret_of (mkCfg (advance_past_svc (apply_effect ms eff)) model) = eff_ret eff.
Proof.
  intros s f m.
  exact (gpr0_apply_effect s f).
Qed.

Lemma materialize_model_accesses_nil : forall m, materialize_model_accesses m [] = Some m.
Proof. intros m. destruct m as [fd [maps lazy mat] io fs proc lim tm]; reflexivity. Qed.

Section Inv.
Variable cfg : SpuriousCfg.

Lemma sstep_cfg_sys_inv : forall ms model x8 evs st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs cfg (mkCfg ms model) evs st ->
  let i := sys_input segs ms x8 in
  (exists eff model' evs0,
      syscall_spec i model (Ok eff model' evs0)
      /\ ~ spurious_refusal_cfg cfg i model eff
      /\ m_halted model' = None
      /\ match materialize_model_accesses model' (syscall_effect_accesses eff) with
         | Some model'' => evs = evs0 /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')
         | None => evs = [] /\ st = SError
         end)
  \/ (exists eff model' evs0 code',
      syscall_spec i model (Ok eff model' evs0)
      /\ m_halted model' = Some code' /\ m_killed model' = None
      /\ evs = evs0 ++ [ExitEv code' (m_fs model')] /\ st = SNext (mkCfg ms model'))
  \/ (exists eff model' evs0 sig,
      syscall_spec i model (Ok eff model' evs0)
      /\ m_killed model' = Some sig
      /\ evs = evs0 ++ [KillEv sig (m_fs model')] /\ st = SNext (mkCfg ms model'))
  \/ (syscall_spec i model Unmodeled /\ evs = [] /\ st = SError).
Proof.
  intros ms model x8 evs st Hsvc Hss. cbv zeta.
  inversion Hss; subst;
    try match goal with H : ms_svc_pending ms = None |- _ => rewrite Hsvc in H; discriminate H end;
    match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; injection H as <- end.
  - left. eexists _, _, _. repeat (split; [eassumption|]).
    match goal with H : materialize_model_accesses _ _ = Some _ |- _ => rewrite H end. split; reflexivity.
  - left. eexists _, _, _. repeat (split; [eassumption|]).
    match goal with H : materialize_model_accesses _ _ = None |- _ => rewrite H end. split; reflexivity.
  - right; left. eexists _, _, _, _. repeat (split; [eassumption|]). split; reflexivity.
  - right; right; left. eexists _, _, _, _. repeat (split; [eassumption|]). split; reflexivity.
  - right; right; right. split; [assumption|]. split; reflexivity.
Qed.

Lemma sstep_cfg_svc_inv : forall ms model x8 e c',
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs cfg (mkCfg ms model) e (SNext c') ->
  (exists eff model' model'',
     syscall_spec (sys_input segs ms x8) model (Ok eff model' e)
     /\ ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff
     /\ m_halted model' = None
     /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
     /\ c' = mkCfg (advance_past_svc (apply_effect ms eff)) model'')
  \/ (exists eff model' evs0, syscall_spec (sys_input segs ms x8) model (Ok eff model' evs0)
       /\ m_halted model' <> None /\ c' = mkCfg ms model').
Proof.
  intros ms model x8 e c' Hsvc Hstep.
  pose proof (sstep_cfg_sys_inv ms model x8 e (SNext c') Hsvc Hstep) as Hinv.
  cbv zeta in Hinv.
  destruct Hinv as
    [(eff & mo1 & evs1 & Hspec & Hnr & Hnone & Hmat)
    |[(eff & mo1 & evs1 & code & Hspec & Hcode & _ & _ & Hst)
    |[(eff & mo1 & evs1 & sg & Hspec & Hsg & _ & Hst)
    |(_ & _ & Hbad)]]].
  - destruct (materialize_model_accesses mo1 (syscall_effect_accesses eff)) as [mo2|] eqn:Em.
    + destruct Hmat as [Hev Hst]. subst evs1. injection Hst as Hc.
      left. exists eff, mo1, mo2.
      exact (conj Hspec (conj Hnr (conj Hnone (conj Em Hc)))).
    + destruct Hmat as [_ Hst]. inversion Hst.
  - injection Hst as Hc. right. exists eff, mo1, evs1.
    refine (conj Hspec (conj _ Hc)). congruence.
  - injection Hst as Hc. right. exists eff, mo1, evs1.
    refine (conj Hspec (conj _ Hc)). intros Hh.
    pose proof (m_killed_of_m_halted_none mo1 Hh) as Hk. congruence.
  - inversion Hbad.
Qed.

End Inv.

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

Lemma sstep_cfg_syscall_forced : forall cfg ms model x8 eff model' model'' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  (forall eff' m' evs', syscall_spec (sys_input segs ms x8) model (Ok eff' m' evs') ->
                        refusal_b (sys_input segs ms x8) model (eff_ret eff') = true) ->
  m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) = Some model'' ->
  sstep_cfg segs cfg (mkCfg ms model) evs
            (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')).
Proof.
  intros * H0 Hp Hs Hforce H1 Hm.
  assert (Hns : ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff).
  { intros [_ [_ [e [mm [ev [Hspec' Hfalse]]]]]].
    pose proof (Hforce e mm ev Hspec') as Ht. congruence. }
  exact (sstep_cfg_syscall segs cfg ms model x8 eff model' model'' evs H0 Hp Hs Hns H1 Hm).
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

End Transparent.

Definition mmap_errnos_when (forced : bool) : list Z :=
  if forced then mmap_errnos else [].

Definition mmap_destructive_errnos : list Z := [].

Definition vm_base_ok (h : VmMaps) (nZ : Z) (a : word) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z
  && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + nZ <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ).

Definition vm_base_candidates (h : VmMaps) : list word :=
  Z_to_bv 64 page_size
  :: map (fun iv => Z_to_bv 64 (page_round_up_Z
                      (bv_unsigned (fst iv) + bv_unsigned (snd iv))))
         (vm_reserved h ++ vm_maps h).

Definition vm_find_base (h : VmMaps) (nZ : Z) : option word :=
  List.find (vm_base_ok h nZ) (vm_base_candidates h).

Definition vm_gap_available (h : VmMaps) (nZ : Z) : bool :=
  match vm_find_base h nZ with Some _ => true | None => false end.

Lemma vm_base_ok_sound : forall h nZ a,
  vm_base_ok h nZ a = true ->
  (bv_unsigned a mod page_size = 0)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ a H. unfold vm_base_ok in H.
  apply andb_true_iff in H as [H Hfree].
  apply andb_true_iff in H as [H Htop].
  apply andb_true_iff in H as [Halign Hpos].
  apply Z.eqb_eq in Halign. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
  repeat split; assumption.
Qed.

Lemma vm_base_ok_intro : forall h nZ a,
  (bv_unsigned a mod page_size = 0)%Z ->
  (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
  vm_base_ok h nZ a = true.
Proof.
  intros h nZ a Ha Hp Ht Hf. unfold vm_base_ok.
  rewrite Hf, andb_true_r, !andb_true_iff, Z.eqb_eq, Z.ltb_lt, Z.leb_le.
  split; [split|]; assumption.
Qed.

Lemma vm_find_base_sound : forall h nZ a,
  vm_find_base h nZ = Some a ->
  (bv_unsigned a mod page_size = 0)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ a. unfold vm_find_base.
  generalize (vm_base_candidates h) as l.
  induction l as [|c l IH]; cbn [List.find]; intros H; [discriminate H|].
  destruct (vm_base_ok h nZ c) eqn:Hc.
  - injection H as ->. exact (vm_base_ok_sound h nZ a Hc).
  - exact (IH H).
Qed.

Lemma vm_gap_available_find : forall h nZ,
  vm_gap_available h nZ = true -> exists a, vm_find_base h nZ = Some a.
Proof.
  intros h nZ. unfold vm_gap_available.
  case_eq (vm_find_base h nZ).
  - intros a _ _. exists a. reflexivity.
  - intros _ Hf. cbn in Hf. discriminate Hf.
Qed.

Lemma region_free_false_In : forall maps lo n,
  region_free maps lo n = false ->
  exists a sz, In (a, sz) maps /\ iv_overlap lo n a sz = true.
Proof.
  intros maps lo n Hrf. exact (region_free_false maps lo n Hrf).
Qed.

Lemma vm_base_ok_step : forall h nZ a,
  vm_base_ok h nZ a = true ->
  In a (vm_base_candidates h)
  \/ exists a', bv_unsigned a' = (bv_unsigned a - page_size)%Z
                /\ vm_base_ok h nZ a' = true.
Proof.
  intros h nZ a Hok.
  destruct (vm_base_ok_sound h nZ a Hok) as (Hal & Hpos & Htop & Hfree).
  assert (Hps : page_size <> 0%Z) by (unfold page_size; lia).
  apply (proj1 (Z.mod_divide _ _ Hps)) in Hal. destruct Hal as [q Hq].
  pose proof (bv_unsigned_in_range 64 a) as [_ Hlt]. unfold bv_modulus in Hlt.
  destruct (Z.eq_dec q 1) as [->|Hq1].
  { left. unfold vm_base_candidates. left. apply bv_eq.
    rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|unfold bv_modulus, page_size in *; lia]. }
  assert (Hq2 : (2 <= q)%Z) by (unfold page_size in *; lia).
  set (a' := Z_to_bv 64 (bv_unsigned a - page_size)).
  assert (Ua' : bv_unsigned a' = (bv_unsigned a - page_size)%Z).
  { apply Z_to_bv_small. unfold bv_modulus, page_size in *. lia. }
  destruct (region_free (vm_reserved h ++ vm_maps h) a' (Z_to_bv 64 nZ)) eqn:Hrf.
  { right. exists a'. split; [exact Ua'|].
    apply vm_base_ok_intro; [| | |exact Hrf]; rewrite Ua'.
    - apply (proj2 (Z.mod_divide _ _ Hps)). exists (q - 1)%Z. rewrite Hq. ring.
    - unfold page_size in *. lia.
    - unfold page_size in *. lia. }
  left. destruct (region_free_false_In _ _ _ Hrf) as (lo & sz & Hin & Hov).
  pose proof (region_free_In _ _ _ _ _ Hfree Hin) as Hno.
  unfold iv_overlap in Hov, Hno. rewrite Ua' in Hov.
  rewrite andb_true_iff, !Z.ltb_lt in Hov.
  rewrite andb_false_iff, !Z.ltb_ge in Hno.
  assert (Hend : (bv_unsigned a - page_size < bv_unsigned lo + bv_unsigned sz
                  <= bv_unsigned a)%Z).
  { unfold page_size in *. destruct Hov as [O1 O2]. destruct Hno as [N|N]; lia. }
  assert (Hr : page_round_up_Z (bv_unsigned lo + bv_unsigned sz) = bv_unsigned a).
  { unfold page_round_up_Z. rewrite Hq. f_equal.
    unfold page_size in *. apply Z.le_antisymm.
    - apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia.
    - apply Z.div_le_lower_bound; lia. }
  unfold vm_base_candidates. right. apply in_map_iff.
  exists (lo, sz). split; [|exact Hin]. cbn [fst snd].
  apply bv_eq. rewrite Z_to_bv_unsigned, Hr.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma vm_find_base_complete_aux : forall h nZ k a,
  (bv_unsigned a <= Z.of_nat k * page_size)%Z ->
  vm_base_ok h nZ a = true ->
  exists c, In c (vm_base_candidates h) /\ vm_base_ok h nZ c = true.
Proof.
  intros h nZ k.
  enough (Hw : forall z, (0 <= z)%Z -> forall b, bv_unsigned b = z ->
                 vm_base_ok h nZ b = true ->
                 exists c, In c (vm_base_candidates h) /\ vm_base_ok h nZ c = true).
  { intros a _ Hok. exact (Hw _ (proj1 (bv_unsigned_in_range 64 a)) a eq_refl Hok). }
  refine (Z_lt_induction _ _). intros z IHz b <- Hb.
  destruct (vm_base_ok_step h nZ b Hb) as [Hc|(b' & E & Hb')]; [now exists b|].
  refine (IHz (bv_unsigned b') _ b' eq_refl Hb').
  pose proof (bv_unsigned_in_range 64 b') as [L _]. unfold page_size in E. lia.
Qed.

Lemma vm_find_base_complete : forall h nZ a,
  vm_base_ok h nZ a = true -> vm_gap_available h nZ = true.
Proof.
  intros h nZ a Hok.
  destruct (vm_base_ok_sound h nZ a Hok) as (Hal & Hpos & _).
  assert (Hps : page_size <> 0%Z) by (unfold page_size; lia).
  apply (proj1 (Z.mod_divide _ _ Hps)) in Hal. destruct Hal as [q Hq].
  destruct (vm_find_base_complete_aux h nZ (Z.to_nat q) a)
    as (c & Hin & Hc); [|exact Hok|].
  { rewrite Z2Nat.id; unfold page_size in *; lia. }
  unfold vm_gap_available, vm_find_base. revert Hin.
  generalize (vm_base_candidates h) as l.
  induction l as [|x l IH]; intros Hin; [destruct Hin|].
  cbn [List.find]. destruct (vm_base_ok h nZ x) eqn:Ex; [reflexivity|].
  destruct Hin as [<-|Hin]; [congruence|exact (IH Hin)].
Qed.

Lemma vm_gap_available_iff : forall h nZ,
  vm_gap_available h nZ = true <->
  exists a, (bv_unsigned a mod page_size = 0)%Z
            /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top h)%Z
            /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ. split.
  - unfold vm_gap_available, vm_find_base.
    destruct (List.find (vm_base_ok h nZ) (vm_base_candidates h)) as [a|] eqn:Hf;
      intros H; [|discriminate H].
    exists a. apply vm_base_ok_sound. apply List.find_some in Hf. exact (proj2 Hf).
  - intros (a & Hal & Hpos & Htop & Hfree).
    destruct (vm_gap_available h nZ) eqn:E; [reflexivity|exfalso].
    pose proof (vm_find_base_complete h nZ a
                  (vm_base_ok_intro h nZ a Hal Hpos Htop Hfree)) as Hg.
    congruence.
Qed.

Definition mmap_grant_refusable (flags : word) (m : Model) (nZ : Z) : bool :=
  orb (match mmap_noreserve_backed_ok flags m nZ return bool with true => false | false => true end)
      (match vm_gap_available (m_vmmaps m) nZ return bool with false => true | true => false end).

Definition mmap_reserve_refusable (m : Model) (nZ : Z) : bool :=
  match vm_gap_available (m_vmmaps m) nZ with true => false | false => true end.

Definition mmap_fixed_fresh_refusable (flags : word) (m : Model) (nZ : Z)
    : bool :=
  match mmap_noreserve_backed_ok flags m nZ with false => true | true => false end.

Definition mmap_fixed_commit_refusable (flags : word) (m : Model)
    (addr n : word) : bool :=
  match mmap_fixed_rw_budget_ok flags m addr n with true => false | false => true end.

Definition mmap_fixed_span_refusable (flags : word) (m : Model)
    (addr n : word) : bool :=
  match mmap_fixed_rw_span_budget_ok flags m addr n with false => true | true => false end.

Definition mprotect_errnos_when (forced : bool) : list Z :=
  match forced with true => mprotect_errnos | false => [] end.

Definition mprotect_refusable (m : Model) (addr n : word) : bool :=
  match mprotect_budget_ok m addr n with true => false | false => true end.

Lemma mmap_grant_refusable_false_iff : forall flags m nZ,
  mmap_grant_refusable flags m nZ = false <->
  mmap_noreserve_backed_ok flags m nZ = true /\ vm_gap_available (m_vmmaps m) nZ = true.
Proof.
  unfold mmap_grant_refusable; intros fl md k.
  destruct (mmap_noreserve_backed_ok fl md k), (vm_gap_available (m_vmmaps md) k);
    simpl; intuition congruence.
Qed.

Lemma mmap_reserve_refusable_false_iff : forall m nZ,
  mmap_reserve_refusable m nZ = false <-> vm_gap_available (m_vmmaps m) nZ = true.
Proof.
  intros md k. unfold mmap_reserve_refusable.
  destruct (vm_gap_available (m_vmmaps md) k); cbn.
  - split; intros _; reflexivity.
  - split; intros H; inversion H.
Qed.

Lemma mprotect_refusable_false_iff : forall m addr n,
  mprotect_refusable m addr n = false <-> mprotect_budget_ok m addr n = true.
Proof.
  intros md x y. unfold mprotect_refusable.
  case_eq (mprotect_budget_ok md x y); intros E; cbn; split; intros H; congruence.
Qed.

Lemma mmap_errnos_when_false : mmap_errnos_when false = [].
Proof. unfold mmap_errnos_when; simpl; exact (@eq_refl (list Z) []). Qed.
Lemma mmap_errnos_when_true : mmap_errnos_when true = mmap_errnos.
Proof. cbv beta iota delta [mmap_errnos_when]. exact (eq_refl mmap_errnos). Qed.
Lemma mprotect_errnos_when_false : mprotect_errnos_when false = [].
Proof. unfold mprotect_errnos_when. simpl. exact (eq_refl (@nil Z)). Qed.

Lemma grant_conj_not_refusable : forall flags m nZ a,
  (bv_unsigned a mod page_size = 0)%Z ->
  (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_noreserve_backed_ok flags m nZ = true ->
  mmap_grant_refusable flags m nZ = false.
Proof.
  intros flags m nZ a Hal Hpos Htop Hfree Hbk.
  assert (Hg : vm_gap_available (m_vmmaps m) nZ = true).
  { apply vm_gap_available_iff. exists a. repeat split; assumption. }
  unfold mmap_grant_refusable. rewrite Hbk, Hg. reflexivity.
Qed.

Lemma reserve_conj_not_refusable : forall m nZ a,
  (bv_unsigned a mod page_size = 0)%Z ->
  (0 < bv_unsigned a)%Z ->
  (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true ->
  mmap_reserve_refusable m nZ = false.
Proof.
  intros m0 k b Ha Hp Ht Hr.
  assert (G : vm_gap_available (m_vmmaps m0) k = true)
    by (apply vm_gap_available_iff; exists b; tauto).
  unfold mmap_reserve_refusable. now rewrite G.
Qed.

Lemma not_refusable_grant_conj : forall flags m nZ,
  mmap_grant_refusable flags m nZ = false ->
  mmap_noreserve_backed_ok flags m nZ = true /\
  exists a, (bv_unsigned a mod page_size = 0)%Z
            /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z
            /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true.
Proof.
  intros fl md k. unfold mmap_grant_refusable.
  destruct (mmap_noreserve_backed_ok fl md k);
    destruct (vm_gap_available (m_vmmaps md) k) eqn:Eg;
    intros Hr; simpl in Hr; try discriminate Hr.
  exact (conj eq_refl (proj1 (vm_gap_available_iff _ _) Eg)).
Qed.

Lemma not_refusable_reserve_conj : forall m nZ,
  mmap_reserve_refusable m nZ = false ->
  exists a, (bv_unsigned a mod page_size = 0)%Z
            /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z
            /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true.
Proof.
  intros m nZ H. apply vm_gap_available_iff. revert H.
  unfold mmap_reserve_refusable.
  destruct (vm_gap_available (m_vmmaps m) nZ); simpl; intros H; [reflexivity|discriminate H].
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

From Stdlib Require Import Classical_Prop.

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

Definition spec_step_ok (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) : Prop := outcome_rect SyscallEffect
  (fun _ => Prop) (fun e m1 _ => m_halted m1 = None -> not (spurious_refusal_cfg ACFG i m e)) True o.

Definition syscall_spec_acfg : Sys SyscallEffect := fun (inp : SyscallInput) (mdl : Model) (out : outcome SyscallEffect) =>
  and (syscall_spec inp mdl out) (spec_step_ok inp mdl out).

Lemma syscall_spec_acfg_spec : forall i m o, syscall_spec_acfg i m o -> syscall_spec i m o.
Proof.
  exact (fun i m o Hacfg => proj1 Hacfg).
Qed.

Lemma syscall_spec_acfg_unmodeled : forall i m,
  syscall_spec_acfg i m Unmodeled <-> syscall_spec i m Unmodeled.
Proof.
  intros i m. split.
  - exact (syscall_spec_acfg_spec i m Unmodeled).
  - intros Hsu. exact (conj Hsu I).
Qed.

Lemma syscall_spec_acfg_nonalloc : forall i m o,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  syscall_spec_acfg i m o <-> syscall_spec i m o.
Proof.
  intros i m o Hnin. split; [exact (syscall_spec_acfg_spec i m o)|]. intros Hso.
  destruct o as [e m1 v1|].
  - refine (conj Hso _). intros _. apply acfg_nonspurious_b.
    destruct (alloc_no_b (bv_unsigned (in_sysno i))) eqn:Eb; [|reflexivity].
    exfalso. exact (Hnin (proj1 (alloc_no_b_In _) Eb)).
  - exact (proj2 (syscall_spec_acfg_unmodeled i m) Hso).
Qed.

Lemma syscall_spec_acfg_no : forall segs ms x8 n m o,
  bv_unsigned x8 = n -> alloc_no_b n = false ->
  syscall_spec_acfg (sys_input segs ms x8) m o <-> syscall_spec (sys_input segs ms x8) m o.
Proof.
  intros segs ms x8 n m o Hx8 Hnb. split; [exact (syscall_spec_acfg_spec _ m o)|].
  intros Hso. refine (conj Hso _). destruct o as [e m1 v1|]; [|exact I].
  intros _. exact (acfg_nonspurious_no segs ms x8 n m e Hx8 Hnb).
Qed.

Lemma syscall_spec_acfg_nonrefusal : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = false ->
  syscall_spec_acfg i m (Ok eff m' evs).
Proof.
  intros i m eff m' evs Hso Hfalse. refine (conj Hso _).
  intros _ (_ & Htrue & _). congruence.
Qed.

Lemma syscall_spec_acfg_det : forall i m eff m' evs,
  (forall o, syscall_spec i m o <-> o = Ok eff m' evs) ->
  forall o, syscall_spec_acfg i m o <-> o = Ok eff m' evs.
Proof.
  intros i m eff m' evs Hiff o.
  assert (Hs0 : syscall_spec i m (Ok eff m' evs)) by exact (proj2 (Hiff (Ok eff m' evs)) eq_refl).
  split.
  - intros Hacfg. exact (proj1 (Hiff o) (syscall_spec_acfg_spec i m o Hacfg)).
  - intros Eo. subst o. refine (conj Hs0 _). intros _.
    destruct (exists_nonspurious ACFG i m eff m' evs Hs0) as (e1 & m1 & v1 & Hs1 & Hns1).
    assert (Ee : e1 = eff) by (pose proof (proj1 (Hiff _) Hs1); congruence).
    rewrite <- Ee. exact Hns1.
Qed.

Lemma syscall_spec_acfg_uniform : forall i m o,
  syscall_spec i m o ->
  (forall eff m' evs eff' m'' evs', syscall_spec i m (Ok eff m' evs) -> syscall_spec i m (Ok eff' m'' evs') ->
     refusal_b i m (eff_ret eff) = refusal_b i m (eff_ret eff')) ->
  syscall_spec_acfg i m o.
Proof.
  intros i m o Hso Hsame. destruct o as [e m1 v1|].
  - destruct (refusal_b i m (eff_ret e)) eqn:Er.
    + refine (conj Hso _). intros _ (_ & _ & (e2 & m2 & v2 & Hs2 & Hn2)).
      pose proof (Hsame _ _ _ _ _ _ Hso Hs2). congruence.
    + exact (syscall_spec_acfg_nonrefusal i m e m1 v1 Hso Er).
  - exact (proj2 (syscall_spec_acfg_unmodeled i m) Hso).
Qed.

Section AcfgSyscallStepping.
Variable segs : list Segment.

Lemma acfg_outcome_ok_nonspurious : forall i m eff m' evs,
  syscall_spec_acfg i m (Ok eff m' evs) ->
  m_halted m' = None -> ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff m' evs Hacfg. exact (proj2 Hacfg).
Qed.

Lemma acfg_outcome_ok_of_guard : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  (m_halted m' = None -> ~ spurious_refusal_cfg ACFG i m eff) ->
  syscall_spec_acfg i m (Ok eff m' evs).
Proof.
  intros i m eff m' evs Hs Hg. hnf. exact (conj Hs Hg).
Qed.

Lemma acfg_outcome_ok_stopped : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  m_halted m' <> None ->
  syscall_spec_acfg i m (Ok eff m' evs).
Proof.
  intros i m eff m' evs Hs Hstop. apply acfg_outcome_ok_of_guard; [exact Hs|].
  intros Hn. exfalso. exact (Hstop Hn).
Qed.

Lemma sstep_cfg_syscall_acfg : forall ms model x8 eff model' model'' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec_acfg (sys_input segs ms x8) model (Ok eff model' evs) ->
  m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) = Some model'' ->
  sstep_cfg segs ACFG (mkCfg ms model) evs
            (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')).
Proof.
  intros ms model x8 eff model' model'' evs Hh Hsvc Hacfg Hh' Hmat.
  exact (sstep_cfg_syscall segs ACFG ms model x8 eff model' model'' evs Hh Hsvc
           (syscall_spec_acfg_spec _ _ _ Hacfg)
           (acfg_outcome_ok_nonspurious _ _ _ _ _ Hacfg Hh') Hh' Hmat).
Qed.

Lemma sstep_cfg_sys_inv_acfg : forall ms model x8 evs st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs ACFG (mkCfg ms model) evs st ->
  let i := sys_input segs ms x8 in
  (exists eff model' evs0,
      syscall_spec_acfg i model (Ok eff model' evs0)
      /\ m_halted model' = None
      /\ match materialize_model_accesses model' (syscall_effect_accesses eff) with
         | Some model'' => evs = evs0 /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')
         | None => evs = [] /\ st = SError
         end)
  \/ (exists eff model' evs0 code',
      syscall_spec_acfg i model (Ok eff model' evs0)
      /\ m_halted model' = Some code' /\ m_killed model' = None
      /\ evs = evs0 ++ [ExitEv code' (m_fs model')] /\ st = SNext (mkCfg ms model'))
  \/ (exists eff model' evs0 sig,
      syscall_spec_acfg i model (Ok eff model' evs0)
      /\ m_killed model' = Some sig
      /\ evs = evs0 ++ [KillEv sig (m_fs model')] /\ st = SNext (mkCfg ms model'))
  \/ (syscall_spec_acfg i model Unmodeled /\ evs = [] /\ st = SError).
Proof.
  intros ms model x8 evs st Hsvc Hss.
  pose proof (sstep_cfg_sys_inv segs ACFG ms model x8 evs st Hsvc Hss) as Hinv.
  cbv zeta in Hinv |- *.
  destruct Hinv as [Hok | [Hex | [Hkill | Hun]]].
  - left. destruct Hok as (eff & m' & evs0 & Hs & Hns & Hrest).
    exists eff, m', evs0. split; [|exact Hrest].
    apply acfg_outcome_ok_of_guard; [exact Hs|]. intros _. exact Hns.
  - right; left. destruct Hex as (eff & m' & evs0 & code' & Hs & Hh' & Hrest).
    exists eff, m', evs0, code'. split; [|split; [exact Hh'|exact Hrest]].
    apply acfg_outcome_ok_stopped; [exact Hs|]. congruence.
  - right; right; left. destruct Hkill as (eff & m' & evs0 & sig & Hs & Hk & Hrest).
    exists eff, m', evs0, sig. split; [|split; [exact Hk|exact Hrest]].
    apply acfg_outcome_ok_stopped; [exact Hs|].
    intros Hn. apply m_killed_of_m_halted_none in Hn. congruence.
  - right; right; right. destruct Hun as [Hs Hrest].
    split; [exact (proj2 (syscall_spec_acfg_unmodeled _ _) Hs)|exact Hrest].
Qed.

End AcfgSyscallStepping.
