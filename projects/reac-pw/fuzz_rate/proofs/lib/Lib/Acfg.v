(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall Dispatch SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.

Definition ACFG : SpuriousCfg := alloc_only_cfg false.

Definition alloc_no_b (n : Z) : bool := existsb (Z.eqb n) alloc_mark_sysnos.

Lemma alloc_no_b_In : forall n, alloc_no_b n = true <-> In n alloc_mark_sysnos.
Proof.
  intros n. unfold alloc_no_b. rewrite existsb_exists. split.
  - intros (x & Hin & Heq). apply Z.eqb_eq in Heq. subst x. exact Hin.
  - intros Hin. exists n. split; [exact Hin | apply Z.eqb_refl].
Qed.

Lemma alloc_no_b_false : forall n, alloc_no_b n = false -> ~ In n alloc_mark_sysnos.
Proof. intros n H Hin. apply alloc_no_b_In in Hin. congruence. Qed.

Lemma acfg_family_off_in : forall i,
  injected_family_off ACFG i = true -> In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof.
  intros i H. unfold injected_family_off in H.
  destruct (injected_arm (bv_unsigned (in_sysno i))) as [a|] eqn:E; [|discriminate H].
  destruct (ia_family a) eqn:Ef; cbn in H; try discriminate H.
  exact (alloc_family_dispatched _ a E Ef).
Qed.

Lemma acfg_family_on_notin : forall i,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> injected_family_off ACFG i = false.
Proof.
  intros i Hn. destruct (injected_family_off ACFG i) eqn:E; [|reflexivity].
  exfalso. apply Hn. apply acfg_family_off_in. exact E.
Qed.

Lemma acfg_family_off_no : forall i n,
  bv_unsigned (in_sysno i) = n -> In n alloc_mark_sysnos -> injected_family_off ACFG i = true.
Proof.
  intros i n E Hin. unfold injected_family_off. rewrite E. cbn [alloc_mark_sysnos In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; reflexivity.
Qed.

Lemma acfg_nonspurious : forall i m eff,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff Hn. apply spurious_refusal_family_on. apply acfg_family_on_notin. exact Hn.
Qed.

Lemma acfg_nonspurious_b : forall i m eff,
  alloc_no_b (bv_unsigned (in_sysno i)) = false ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof. intros i m eff H. apply acfg_nonspurious. apply alloc_no_b_false. exact H. Qed.

Lemma ret_in_errnos_errno : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros es e Hin. unfold ret_in_errnos. apply existsb_exists. exists e. split; [exact Hin|].
  apply bv_eqb_eq. reflexivity.
Qed.

Lemma ret_in_errnos_ENOMEM : forall r,
  ret_in_errnos [ENOMEM] r = bv_eqb r (errno_ret ENOMEM).
Proof. intros r. cbn. rewrite orb_false_r. reflexivity. Qed.

Lemma page_aligned_not_ENOMEM : forall a : word,
  (bv_unsigned a mod page_size = 0)%Z -> bv_eqb a (errno_ret ENOMEM) = false.
Proof.
  intros a Hal. destruct (bv_eqb a (errno_ret ENOMEM)) eqn:E; [|reflexivity].
  exfalso. apply bv_eqb_eq in E. subst a. vm_compute in Hal. discriminate Hal.
Qed.

Lemma ret_in_errnos_ENOMEM_aligned : forall a : word,
  (bv_unsigned a mod page_size = 0)%Z -> ret_in_errnos [ENOMEM] a = false.
Proof. intros a H. rewrite ret_in_errnos_ENOMEM. apply page_aligned_not_ENOMEM. exact H. Qed.

Lemma refusal_b_222 : forall i m r, bv_unsigned (in_sysno i) = 222%Z ->
  refusal_b i m r = ret_in_errnos mmap_errnos r.
Proof. intros i m r E. unfold refusal_b. rewrite E. reflexivity. Qed.
Lemma refusal_b_226 : forall i m r, bv_unsigned (in_sysno i) = 226%Z ->
  refusal_b i m r = ret_in_errnos mprotect_errnos r.
Proof. intros i m r E. unfold refusal_b. rewrite E. reflexivity. Qed.
Lemma refusal_b_216 : forall i m r, bv_unsigned (in_sysno i) = 216%Z ->
  refusal_b i m r = ret_in_errnos mremap_errnos r.
Proof. intros i m r E. unfold refusal_b. rewrite E. reflexivity. Qed.
Lemma refusal_b_214 : forall i m r, bv_unsigned (in_sysno i) = 214%Z ->
  refusal_b i m r = brk_refusal_b m (in_arg i 0) r.
Proof. intros i m r E. unfold refusal_b. rewrite E. reflexivity. Qed.

Definition spec_step_ok (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) : Prop :=
  match o with
  | Ok eff m' _ => m_halted m' = None -> ~ spurious_refusal_cfg ACFG i m eff
  | Unmodeled => True
  end.

Definition syscall_spec_acfg : Sys SyscallEffect :=
  fun i m o => syscall_spec i m o /\ spec_step_ok i m o.

Lemma syscall_spec_acfg_spec : forall i m o, syscall_spec_acfg i m o -> syscall_spec i m o.
Proof. intros i m o [H _]. exact H. Qed.

Lemma syscall_spec_acfg_unmodeled : forall i m,
  syscall_spec_acfg i m Unmodeled <-> syscall_spec i m Unmodeled.
Proof. intros i m. unfold syscall_spec_acfg. cbn. tauto. Qed.

Lemma syscall_spec_acfg_nonalloc : forall i m o,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  syscall_spec_acfg i m o <-> syscall_spec i m o.
Proof.
  intros i m o Hn. unfold syscall_spec_acfg. split; [tauto|]. intros H. split; [exact H|].
  destruct o as [eff m' evs|]; cbn; [|exact I]. intros _. apply acfg_nonspurious. exact Hn.
Qed.

Lemma syscall_spec_acfg_nonalloc_b : forall i m o,
  alloc_no_b (bv_unsigned (in_sysno i)) = false ->
  syscall_spec_acfg i m o <-> syscall_spec i m o.
Proof. intros i m o H. apply syscall_spec_acfg_nonalloc. apply alloc_no_b_false. exact H. Qed.

Lemma acfg_si_nonalloc : forall segs ms x8 m o,
  alloc_no_b (bv_unsigned x8) = false ->
  syscall_spec_acfg (sys_input segs ms x8) m o <-> syscall_spec (sys_input segs ms x8) m o.
Proof. intros segs ms x8 m o H. apply syscall_spec_acfg_nonalloc_b. exact H. Qed.

Lemma syscall_spec_acfg_nonrefusal : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = false ->
  syscall_spec_acfg i m (Ok eff m' evs).
Proof.
  intros i m eff m' evs Hs Hnr. split; [exact Hs|]. cbn. intros _.
  apply spurious_refusal_not_refusal. exact Hnr.
Qed.

Lemma syscall_spec_acfg_forced : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  (forall eff' m'' evs', syscall_spec i m (Ok eff' m'' evs') -> refusal_b i m (eff_ret eff') = true) ->
  syscall_spec_acfg i m (Ok eff m' evs).
Proof.
  intros i m eff m' evs Hs Hall. split; [exact Hs|]. cbn. intros _ (_ & _ & (eff' & m'' & evs' & Hs' & Hnr)).
  rewrite (Hall _ _ _ Hs') in Hnr. discriminate Hnr.
Qed.

Lemma syscall_spec_acfg_det : forall i m eff m' evs,
  (forall o, syscall_spec i m o <-> o = Ok eff m' evs) ->
  forall o, syscall_spec_acfg i m o <-> o = Ok eff m' evs.
Proof.
  intros i m eff m' evs Hchar o. split.
  - intros [Hs _]. apply Hchar. exact Hs.
  - intros ->. split; [apply Hchar; reflexivity|]. cbn. intros _ (_ & Hr & (eff' & m'' & evs' & Hs' & Hnr)).
    apply Hchar in Hs'. injection Hs' as -> -> ->. rewrite Hr in Hnr. discriminate Hnr.
Qed.

Lemma syscall_spec_acfg_uniform : forall i m o,
  syscall_spec i m o ->
  (forall eff m' evs eff' m'' evs', syscall_spec i m (Ok eff m' evs) -> syscall_spec i m (Ok eff' m'' evs') ->
     refusal_b i m (eff_ret eff) = refusal_b i m (eff_ret eff')) ->
  syscall_spec_acfg i m o.
Proof.
  intros i m o Hs Hu. split; [exact Hs|]. destruct o as [eff m' evs|]; cbn; [|exact I].
  intros _ (_ & Hr & (eff' & m'' & evs' & Hs' & Hnr)).
  rewrite (Hu _ _ _ _ _ _ Hs Hs') in Hr. rewrite Hr in Hnr. discriminate Hnr.
Qed.

Lemma syscall_spec_acfg_halted : forall i m eff m' evs,
  m_halted m' <> None ->
  syscall_spec_acfg i m (Ok eff m' evs) <-> syscall_spec i m (Ok eff m' evs).
Proof.
  intros i m eff m' evs Hh. unfold syscall_spec_acfg. split; [tauto|]. intros H. split; [exact H|].
  cbn. intros Hn. contradiction.
Qed.

Lemma exists_nonspurious : forall cfg i m eff0 m0 evs0,
  syscall_spec i m (Ok eff0 m0 evs0) ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff0 m0 evs0 H0.
  destruct (classic (exists eff' m' evs', syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false))
    as [(eff' & m' & evs' & Hs & Hnr)|Hno].
  - exists eff', m', evs'. split; [exact Hs|]. apply spurious_refusal_not_refusal. exact Hnr.
  - exists eff0, m0, evs0. split; [exact H0|]. intros (_ & _ & Hex). exact (Hno Hex).
Qed.

Lemma exists_acfg : forall i m eff0 m0 evs0,
  syscall_spec i m (Ok eff0 m0 evs0) ->
  exists eff m' evs, syscall_spec_acfg i m (Ok eff m' evs).
Proof.
  intros i m eff0 m0 evs0 H0.
  destruct (exists_nonspurious ACFG i m eff0 m0 evs0 H0) as (eff & m' & evs & Hs & Hn).
  exists eff, m', evs. split; [exact Hs|]. cbn. intros _. exact Hn.
Qed.

Lemma nonspurious_refusal_forced : forall i m eff,
  ~ spurious_refusal_cfg ACFG i m eff ->
  injected_family_off ACFG i = true ->
  refusal_b i m (eff_ret eff) = true ->
  forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true.
Proof.
  intros i m eff Hns Hoff Hr eff' m' evs' Hs'.
  destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity|]. exfalso.
  apply Hns. split; [exact Hoff|]. split; [exact Hr|]. exists eff', m', evs'. split; assumption.
Qed.

Lemma acfg_refusal_forced : forall i m eff m' evs,
  syscall_spec_acfg i m (Ok eff m' evs) -> m_halted m' = None ->
  injected_family_off ACFG i = true ->
  refusal_b i m (eff_ret eff) = true ->
  forall eff' m'' evs', syscall_spec i m (Ok eff' m'' evs') -> refusal_b i m (eff_ret eff') = true.
Proof.
  intros i m eff m' evs [_ Hok] Hh Hoff Hr. exact (nonspurious_refusal_forced i m eff (Hok Hh) Hoff Hr).
Qed.

Lemma acfg_char_split : forall i m (Ref Grant : outcome SyscallEffect -> Prop) (forced : bool),
  injected_family_off ACFG i = true ->
  (forall o, syscall_spec i m o <-> Ref o \/ Grant o) ->
  (forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> m_halted m' = None) ->
  (forall o, Ref o -> exists eff m' evs, o = Ok eff m' evs /\ refusal_b i m (eff_ret eff) = true) ->
  (forall o, Grant o -> exists eff m' evs, o = Ok eff m' evs /\ refusal_b i m (eff_ret eff) = false) ->
  (forall o, Grant o -> forced = false) ->
  (forced = false -> exists o, Grant o) ->
  forall o, syscall_spec_acfg i m o <-> (forced = true /\ Ref o) \/ Grant o.
Proof.
  intros i m Ref Grant forced Hoff Hchar Hhalt HrefR HgrantR Hgf Hfg o. split.
  - intros [Hs Hok]. destruct (proj1 (Hchar o) Hs) as [HR | HG]; [|right; exact HG].
    destruct forced; [left; split; [reflexivity | exact HR]|]. exfalso.
    destruct (HrefR o HR) as (eff & m' & evs & -> & Hr).
    destruct (Hfg eq_refl) as [o' HG'].
    destruct (HgrantR o' HG') as (eff' & m'' & evs' & -> & Hnr).
    apply (Hok (Hhalt _ _ _ Hs)). split; [exact Hoff|]. split; [exact Hr|].
    exists eff', m'', evs'. split; [apply Hchar; right; exact HG' | exact Hnr].
  - intros [[Hf HR] | HG].
    + destruct (HrefR o HR) as (eff & m' & evs & -> & Hr).
      split; [apply Hchar; left; exact HR|]. cbn. intros _ (_ & _ & (eff' & m'' & evs' & Hs' & Hnr)).
      destruct (proj1 (Hchar _) Hs') as [HR' | HG'].
      * destruct (HrefR _ HR') as (? & ? & ? & Heq & Hr'). injection Heq as -> -> ->. congruence.
      * rewrite (Hgf _ HG') in Hf. discriminate Hf.
    + destruct (HgrantR o HG) as (eff & m' & evs & -> & Hnr).
      split; [apply Hchar; right; exact HG|]. cbn. intros _. apply spurious_refusal_not_refusal. exact Hnr.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs ACFG c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs ACFG c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh H. destruct H as [c | c1 evs c2 tr c3 Hss _]; [split; reflexivity|].
  exfalso. apply Hh. exact (sstep_cfg_halted_none _ _ _ Hss).
Qed.

Lemma star_cfg_one : forall c evs c',
  sstep_cfg segs ACFG c evs (SNext c') -> star_cfg segs ACFG c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs).
  econstructor; [exact H | apply star_cfg_refl].
Qed.

Lemma star_cfg_trans : forall c1 t1 c2 t2 c3,
  star_cfg segs ACFG c1 t1 c2 -> star_cfg segs ACFG c2 t2 c3 -> star_cfg segs ACFG c1 (t1 ++ t2) c3.
Proof.
  intros c1 t1 c2 t2 c3 H1; revert t2 c3.
  induction H1 as [c | c1 evs c2 tr c3 Hss Hs IH]; intros t2 c4 H2; [exact H2|].
  rewrite <- app_assoc. econstructor; [exact Hss | apply IH; exact H2].
Qed.

Lemma obs_trace_cfg_nil : forall c, obs_trace_cfg segs ACFG c [].
Proof. intros c. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil]. Qed.

Lemma star_cfg_inv (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs ACFG c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star_cfg segs ACFG c tr c' -> Inv c'.
Proof.
  intros c tr c' HInv Hstar. induction Hstar; [exact HInv|].
  apply IHHstar. eapply Hstep; eauto.
Qed.

Lemma inv_no_reaches_error_cfg (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs ACFG c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep_cfg segs ACFG c evs SError) :
  forall c, Inv c -> ~ reaches_error_cfg segs ACFG c.
Proof.
  intros c HInv (tr & c' & evs & Hstar & Hss).
  eapply Hnoerr; [| exact Hss].
  eapply star_cfg_inv; eauto.
Qed.

Lemma sstep_cfg_of_instr : forall ms model e st,
  ms_svc_pending ms = None -> sstep segs (mkCfg ms model) e st -> sstep_cfg segs ACFG (mkCfg ms model) e st.
Proof.
  intros ms model e st Hsvc H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H1; discriminate H1 end).
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
Qed.

Lemma sstep_cfg_of_nonalloc : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  sstep segs (mkCfg ms model) e st -> sstep_cfg segs ACFG (mkCfg ms model) e st.
Proof.
  intros ms model x8 e st Hsvc Hn H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1 end);
    match goal with H1 : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H1; injection H1; intro; subst y end.
  - eapply sstep_cfg_syscall; try eassumption. apply acfg_nonspurious. exact Hn.
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption. apply acfg_nonspurious. exact Hn.
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

Lemma sstep_cfg_of_acfg : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) e st ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     m_halted m' = None -> syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m' evs)) ->
  sstep_cfg segs ACFG (mkCfg ms model) e st.
Proof.
  intros ms model x8 e st Hsvc H Hacfg. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1 end);
    match goal with H1 : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H1; injection H1; intro; subst y end.
  - eapply sstep_cfg_syscall; try eassumption.
    match goal with Hs : syscall_spec _ _ (Ok ?eff ?m' ?evs), Hh : m_halted ?m' = None |- _ =>
      exact (proj2 (Hacfg _ _ _ Hs Hh) Hh) end.
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption.
    match goal with Hs : syscall_spec _ _ (Ok ?eff ?m' ?evs), Hh : m_halted ?m' = None |- _ =>
      exact (proj2 (Hacfg _ _ _ Hs Hh) Hh) end.
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
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
  intros ms model x8 eff model' model'' evs Hh Hsvc [Hspec Hok] Hh' Hmat.
  eapply sstep_cfg_syscall; try eassumption. exact (Hok Hh').
Qed.

Lemma sstep_cfg_syscall_mf_acfg : forall ms model x8 eff model' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec_acfg (sys_input segs ms x8) model (Ok eff model' evs) ->
  m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) = None ->
  sstep_cfg segs ACFG (mkCfg ms model) [] SError.
Proof.
  intros ms model x8 eff model' evs Hh Hsvc [Hspec Hok] Hh' Hmat.
  eapply sstep_cfg_syscall_materialization_fault; try eassumption. exact (Hok Hh').
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
  intros ms model x8 evs st Hsvc Hss. cbv zeta.
  inversion Hss; subst;
    try match goal with H : ms_svc_pending ms = None |- _ => rewrite Hsvc in H; discriminate H end;
    match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; injection H as <- end.
  - left. eexists _, _, _. split; [split; [eassumption | cbn; intros _; eassumption]|].
    split; [eassumption|].
    match goal with H : materialize_model_accesses _ _ = Some _ |- _ => rewrite H end. split; reflexivity.
  - left. eexists _, _, _. split; [split; [eassumption | cbn; intros _; eassumption]|].
    split; [eassumption|].
    match goal with H : materialize_model_accesses _ _ = None |- _ => rewrite H end. split; reflexivity.
  - right; left. eexists _, _, _, _. split.
    + split; [eassumption|]. cbn.
      match goal with H : m_halted ?m = Some _ |- m_halted ?m = None -> _ => intros Hn; rewrite H in Hn; discriminate Hn end.
    + repeat (split; [eassumption|]). split; reflexivity.
  - right; right; left. eexists _, _, _, _. split.
    + split; [eassumption|]. cbn.
      match goal with H : m_killed ?m = Some _ |- m_halted ?m = None -> _ =>
        intros Hn; rewrite (m_killed_of_m_halted_none _ Hn) in H; discriminate H end.
    + repeat (split; [eassumption|]). split; reflexivity.
  - right; right; right. split; [split; [eassumption | exact I]|]. split; reflexivity.
Qed.

End WithSegs.

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

Lemma vm_find_base_sound : forall h nZ a,
  vm_find_base h nZ = Some a ->
  (bv_unsigned a mod page_size = 0)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ a H. unfold vm_find_base in H.
  apply List.find_some in H as [_ H]. exact (vm_base_ok_sound h nZ a H).
Qed.

Lemma vm_gap_available_find : forall h nZ,
  vm_gap_available h nZ = true -> exists a, vm_find_base h nZ = Some a.
Proof.
  intros h nZ H. unfold vm_gap_available in H.
  destruct (vm_find_base h nZ) as [a|]; [now exists a | discriminate].
Qed.

Lemma region_free_false_In : forall maps lo n,
  region_free maps lo n = false ->
  exists a sz, In (a, sz) maps /\ iv_overlap lo n a sz = true.
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
  cbn in H. destruct (iv_overlap lo n b s) eqn:Ho.
  - exists b, s. split; [now left|exact Ho].
  - cbn in H. destruct (IH lo n H) as (a & sz & Hin & Hov).
    exists a, sz. split; [now right|exact Hov].
Qed.

Lemma vm_base_ok_step : forall h nZ a,
  vm_base_ok h nZ a = true ->
  In a (vm_base_candidates h)
  \/ exists a', bv_unsigned a' = (bv_unsigned a - page_size)%Z
                /\ vm_base_ok h nZ a' = true.
Proof.
  intros h nZ a Hok.
  pose proof (vm_base_ok_sound h nZ a Hok) as (Hal & Hpos & Htop & Hfree).
  pose proof (bv_unsigned_in_range 64 a) as [_ Ha]. unfold bv_modulus in Ha.
  destruct (Z.eq_dec (bv_unsigned a) page_size) as [Heq|Hne].
  { left. left. rewrite <- Heq. apply Z_to_bv_bv_unsigned. }
  assert (Hge : (2 * page_size <= bv_unsigned a)%Z).
  { unfold page_size in *.
    pose proof (Z_div_mod_eq_full (bv_unsigned a) 4096). lia. }
  set (a' := Z_to_bv 64 (bv_unsigned a - page_size)).
  assert (Ua' : bv_unsigned a' = (bv_unsigned a - page_size)%Z).
  { subst a'. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus, page_size in *. lia. }
  destruct (vm_base_ok h nZ a') eqn:Hok'.
  { right. exists a'. split; [exact Ua'|exact Hok']. }
  left. unfold vm_base_ok in Hok'. rewrite Ua' in Hok'.
  assert (H1 : ((bv_unsigned a - page_size) mod page_size =? 0)%Z = true)
    by (apply Z.eqb_eq; rewrite Zminus_mod, Hal, Z_mod_same_full; reflexivity).
  assert (H2 : (0 <? bv_unsigned a - page_size)%Z = true)
    by (apply Z.ltb_lt; unfold page_size in *; lia).
  assert (H3 : (bv_unsigned a - page_size + nZ <=? alloc_top h)%Z = true)
    by (apply Z.leb_le; unfold page_size in *; lia).
  rewrite H1, H2, H3 in Hok'. cbn [andb] in Hok'.
  destruct (region_free_false_In _ _ _ Hok') as (lo & sz & Hin & Hov).
  pose proof (region_free_In _ _ _ _ _ Hfree Hin) as Hnov.
  unfold iv_overlap in Hov, Hnov. rewrite Ua' in Hov.
  apply andb_true_iff in Hov as [O1 O2].
  apply Z.ltb_lt in O1. apply Z.ltb_lt in O2.
  apply andb_false_iff in Hnov as [N|N]; apply Z.ltb_ge in N;
    [|unfold page_size in *; lia].
  right. apply in_map_iff. exists (lo, sz). split; [|exact Hin].
  cbn [fst snd].
  replace (page_round_up_Z (bv_unsigned lo + bv_unsigned sz))
    with (bv_unsigned a); [apply Z_to_bv_bv_unsigned|].
  unfold page_round_up_Z, page_size in *.
  pose proof (Z_div_mod_eq_full (bv_unsigned a) 4096) as Hq.
  rewrite Hal, Z.add_0_r in Hq.
  rewrite <- (Z.div_unique_pos (bv_unsigned lo + bv_unsigned sz + 4096 - 1)
                4096 (bv_unsigned a / 4096)
                (bv_unsigned lo + bv_unsigned sz + 4096 - 1
                 - 4096 * (bv_unsigned a / 4096))); lia.
Qed.

Lemma vm_find_base_complete_aux : forall h nZ k a,
  (bv_unsigned a <= Z.of_nat k * page_size)%Z ->
  vm_base_ok h nZ a = true ->
  exists c, In c (vm_base_candidates h) /\ vm_base_ok h nZ c = true.
Proof.
  intros h nZ k. induction k as [|k IH]; intros a Hk Hok.
  - pose proof (vm_base_ok_sound h nZ a Hok) as (_ & Hpos & _). cbn in Hk. lia.
  - destruct (vm_base_ok_step h nZ a Hok) as [Hin | (a' & Ua' & Hok')].
    + exists a. split; assumption.
    + apply (IH a'); [|exact Hok'].
      rewrite Ua'. rewrite Nat2Z.inj_succ in Hk. unfold page_size in *. lia.
Qed.

Lemma vm_find_base_complete : forall h nZ a,
  vm_base_ok h nZ a = true -> vm_gap_available h nZ = true.
Proof.
  intros h nZ a Hok.
  pose proof (bv_unsigned_in_range 64 a) as [Ha _].
  destruct (vm_find_base_complete_aux h nZ (Z.to_nat (bv_unsigned a)) a)
    as (c & Hin & Hc); [unfold page_size; lia|exact Hok|].
  unfold vm_gap_available, vm_find_base.
  destruct (List.find (vm_base_ok h nZ) (vm_base_candidates h)) eqn:Hf;
    [reflexivity|exfalso].
  pose proof (List.find_none _ _ Hf c Hin) as Hn. cbn beta in Hn.
  rewrite Hc in Hn. discriminate Hn.
Qed.

Lemma vm_gap_available_iff : forall h nZ,
  vm_gap_available h nZ = true <->
  exists a, (bv_unsigned a mod page_size = 0)%Z
            /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top h)%Z
            /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ. split.
  - intros H. apply vm_gap_available_find in H as [a Ha].
    exists a. exact (vm_find_base_sound h nZ a Ha).
  - intros (a & Hal & Hpos & Htop & Hfree).
    apply (vm_find_base_complete h nZ a). unfold vm_base_ok.
    rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
      (proj2 (Z.leb_le _ _) Htop), Hfree. reflexivity.
Qed.

Definition mmap_grant_refusable (flags : word) (m : Model) (nZ : Z) : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ)
  || negb (vm_gap_available (m_vmmaps m) nZ).

Definition mmap_reserve_refusable (m : Model) (nZ : Z) : bool :=
  negb (vm_gap_available (m_vmmaps m) nZ).

Definition mmap_fixed_fresh_refusable (flags : word) (m : Model) (nZ : Z) : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ).

Definition mmap_fixed_commit_refusable (flags : word) (m : Model) (addr n : word) : bool :=
  negb (mmap_fixed_rw_budget_ok flags m addr n).

Definition mmap_fixed_span_refusable (flags : word) (m : Model) (addr n : word) : bool :=
  negb (mmap_fixed_rw_span_budget_ok flags m addr n).

Definition mprotect_errnos_when (forced : bool) : list Z :=
  if forced then mprotect_errnos else [].

Definition mprotect_refusable (m : Model) (addr n : word) : bool :=
  negb (mprotect_budget_ok m addr n).
