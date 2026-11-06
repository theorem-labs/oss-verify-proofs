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

Definition alloc_no_b (n : Z) : bool
  := List.existsb (Z.eqb n) Run.alloc_mark_sysnos.

Lemma alloc_no_b_In (n : Z)
  : alloc_no_b n = true <-> List.In n Run.alloc_mark_sysnos.
Proof.
  unfold alloc_no_b; rewrite existsb_exists; split.
  - intros [k [Hk Hkeq]]; apply Z.eqb_eq in Hkeq; subst k; assumption.
  - intro Hmem; exists n; rewrite Z.eqb_refl; split; [assumption | reflexivity].
Qed.

Lemma alloc_no_b_false (n : Z)
  : alloc_no_b n = false -> not (List.In n Run.alloc_mark_sysnos).
Proof.
  intros Hfalse Hmem; apply alloc_no_b_In in Hmem; congruence.
Qed.

Lemma acfg_family_off_in (i : SyscallInput)
  : injected_family_off ACFG i = true
  -> List.In (bv_unsigned (in_sysno i)) Run.alloc_mark_sysnos.
Proof.
  unfold injected_family_off; intro Hoff.
  destruct (injected_arm (bv_unsigned (in_sysno i))) as [arm|] eqn:Harm; [| discriminate Hoff].
  eapply alloc_family_dispatched; [exact Harm |].
  destruct (ia_family arm); cbn in Hoff; [reflexivity | discriminate Hoff ..].
Qed.

Lemma acfg_family_on_notin (i : SyscallInput)
  : not (List.In (bv_unsigned (in_sysno i)) Run.alloc_mark_sysnos)
  -> injected_family_off ACFG i = false.
Proof.
  intro Hout; case_eq (injected_family_off ACFG i); intro Hoff; [exfalso | reflexivity].
  exact (Hout (acfg_family_off_in i Hoff)).
Qed.

Lemma acfg_family_off_no : forall i n,
  bv_unsigned (in_sysno i) = n -> In n alloc_mark_sysnos -> injected_family_off ACFG i = true.
Proof.
  intros i n E Hin. unfold injected_family_off. rewrite E. cbn [alloc_mark_sysnos In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; reflexivity.
Qed.

Lemma acfg_nonspurious (i : SyscallInput) (m : Model) (eff : SyscallEffect)
  : not (List.In (bv_unsigned (in_sysno i)) Run.alloc_mark_sysnos)
  -> not (spurious_refusal_cfg ACFG i m eff).
Proof.
  intro Hout; exact (spurious_refusal_family_on ACFG i m eff (acfg_family_on_notin i Hout)).
Qed.

Lemma acfg_nonspurious_b (i : SyscallInput) (m : Model) (eff : SyscallEffect)
  : alloc_no_b (bv_unsigned (in_sysno i)) = false -> not (spurious_refusal_cfg ACFG i m eff).
Proof.
  intro Hb; exact (acfg_nonspurious i m eff (alloc_no_b_false _ Hb)).
Qed.

Lemma ret_in_errnos_errno : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros es e Hin. unfold ret_in_errnos. apply existsb_exists. exists e. split; [exact Hin|].
  apply bv_eqb_eq. reflexivity.
Qed.

Lemma ret_in_errnos_ENOMEM (r : word)
  : ret_in_errnos (ENOMEM :: nil) r = bv_eqb r (errno_ret ENOMEM).
Proof.
  unfold ret_in_errnos; cbn [existsb]; now rewrite orb_false_r.
Qed.

Lemma page_aligned_not_ENOMEM (a : word)
  : (bv_unsigned a mod page_size)%Z = 0%Z -> bv_eqb a (errno_ret ENOMEM) = false.
Proof.
  intro Haligned; destruct (bv_eqb a (errno_ret ENOMEM)) eqn:Hhit; [exfalso | reflexivity].
  unfold bv_eqb in Hhit; apply Z.eqb_eq in Hhit; rewrite Hhit in Haligned.
  vm_compute in Haligned; congruence.
Qed.

Lemma ret_in_errnos_ENOMEM_aligned (a : word)
  : (bv_unsigned a mod page_size)%Z = 0%Z -> ret_in_errnos (ENOMEM :: nil) a = false.
Proof.
  intro Haligned; rewrite ret_in_errnos_ENOMEM; exact (page_aligned_not_ENOMEM a Haligned).
Qed.

Lemma refusal_b_222 (i : SyscallInput) (m : Model) (r : word)
  : bv_unsigned (in_sysno i) = 222%Z -> refusal_b i m r = ret_in_errnos mmap_errnos r.
Proof. intro Hno; unfold refusal_b; rewrite Hno; reflexivity. Qed.
Lemma refusal_b_226 (i : SyscallInput) (m : Model) (r : word)
  : bv_unsigned (in_sysno i) = 226%Z -> refusal_b i m r = ret_in_errnos mprotect_errnos r.
Proof. intro Hno; unfold refusal_b; rewrite Hno; reflexivity. Qed.
Lemma refusal_b_216 (i : SyscallInput) (m : Model) (r : word)
  : bv_unsigned (in_sysno i) = 216%Z -> refusal_b i m r = ret_in_errnos mremap_errnos r.
Proof. intro Hno; unfold refusal_b; rewrite Hno; reflexivity. Qed.
Lemma refusal_b_214 (i : SyscallInput) (m : Model) (r : word)
  : bv_unsigned (in_sysno i) = 214%Z -> refusal_b i m r = brk_refusal_b m (in_arg i 0) r.
Proof. intro Hno; unfold refusal_b; rewrite Hno; reflexivity. Qed.

Definition spec_step_ok (i : SyscallInput) (m : Model)
    (o : outcome SyscallEffect) : Prop :=
  match o with
  | Ok eff m' _ =>
      m_halted m' = None -> not (spurious_refusal_cfg ACFG i m eff)
  | Unmodeled => True end.

Definition syscall_spec_acfg : Sys SyscallEffect := fun i m o =>
  and (syscall_spec i m o) (spec_step_ok i m o).

Lemma syscall_spec_acfg_spec (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
  : syscall_spec_acfg i m o -> syscall_spec i m o.
Proof. intros [Hspec_only _]; exact Hspec_only. Qed.

Lemma syscall_spec_acfg_unmodeled (i : SyscallInput) (m : Model)
  : (syscall_spec_acfg i m Unmodeled <-> syscall_spec i m Unmodeled).
Proof.
  split; [intros [Hu _]; exact Hu | intro Hu; split; [exact Hu | exact I]].
Qed.

Lemma syscall_spec_acfg_nonalloc (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
  : not (List.In (bv_unsigned (in_sysno i)) Run.alloc_mark_sysnos)
  -> (syscall_spec_acfg i m o <-> syscall_spec i m o).
Proof.
  intro Hout; split; [exact (syscall_spec_acfg_spec i m o) |].
  intro Hspec_o; split; [exact Hspec_o |]; destruct o as [eff1 m1 evs1 |]; [| exact I].
  exact (fun _ => acfg_nonspurious i m eff1 Hout).
Qed.

Lemma syscall_spec_acfg_nonalloc_b (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
  : alloc_no_b (bv_unsigned (in_sysno i)) = false
  -> (syscall_spec_acfg i m o <-> syscall_spec i m o).
Proof. intro Hb; exact (syscall_spec_acfg_nonalloc i m o (alloc_no_b_false _ Hb)). Qed.

Lemma acfg_si_nonalloc (segs : list Segment) (ms : machine_state) (x8 : word) (m : Model)
    (o : outcome SyscallEffect)
  : alloc_no_b (bv_unsigned x8) = false
  -> (syscall_spec_acfg (sys_input segs ms x8) m o <-> syscall_spec (sys_input segs ms x8) m o).
Proof. exact (syscall_spec_acfg_nonalloc_b (sys_input segs ms x8) m o). Qed.

Lemma syscall_spec_acfg_nonrefusal (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : list event)
  : syscall_spec i m (Ok eff m' evs) -> refusal_b i m (eff_ret eff) = false
  -> syscall_spec_acfg i m (Ok eff m' evs).
Proof.
  intros Hspec_ok Hnr; split; [exact Hspec_ok |].
  intros _; exact (spurious_refusal_not_refusal ACFG i m eff Hnr).
Qed.

Lemma syscall_spec_acfg_forced (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : list event)
  : syscall_spec i m (Ok eff m' evs)
  -> (forall (eff' : SyscallEffect) (m'' : Model) (evs' : list event),
        syscall_spec i m (Ok eff' m'' evs') -> refusal_b i m (eff_ret eff') = true)
  -> syscall_spec_acfg i m (Ok eff m' evs).
Proof.
  intros Hspec_ok Hevery; split; [exact Hspec_ok |].
  intros _ [_ [_ [eff2 [m2 [evs2 [Hspec2 Hnr2]]]]]].
  rewrite (Hevery eff2 m2 evs2 Hspec2) in Hnr2; discriminate Hnr2.
Qed.

Lemma syscall_spec_acfg_det (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : list event)
  : (forall o : outcome SyscallEffect, syscall_spec i m o <-> o = Ok eff m' evs)
  -> forall o : outcome SyscallEffect, (syscall_spec_acfg i m o <-> o = Ok eff m' evs).
Proof.
  intros Hunique o; split.
  - intros [Hspec_o _]; apply Hunique; exact Hspec_o.
  - intro Heq_o; subst o; split; [apply Hunique; reflexivity |].
    intros _ [_ [Href [eff2 [m2 [evs2 [Hspec2 Hnr2]]]]]].
    apply Hunique in Hspec2; injection Hspec2 as Heff _ _; subst eff2; congruence.
Qed.

Lemma syscall_spec_acfg_uniform (i : SyscallInput) (m : Model) (o : outcome SyscallEffect)
  : syscall_spec i m o
  -> (forall (eff : SyscallEffect) (m' : Model) (evs : list event)
        (eff' : SyscallEffect) (m'' : Model) (evs' : list event),
        syscall_spec i m (Ok eff m' evs) -> syscall_spec i m (Ok eff' m'' evs')
        -> refusal_b i m (eff_ret eff) = refusal_b i m (eff_ret eff'))
  -> syscall_spec_acfg i m o.
Proof.
  intros Hspec_o Hsame; split; [exact Hspec_o |]; destruct o as [eff1 m1 evs1 |]; [| exact I].
  intros _ [_ [Href [eff2 [m2 [evs2 [Hspec2 Hnr2]]]]]].
  rewrite (Hsame eff1 m1 evs1 eff2 m2 evs2 Hspec_o Hspec2) in Href; congruence.
Qed.

Lemma syscall_spec_acfg_halted : forall i m eff m' evs,
  m_halted m' <> None ->
  syscall_spec_acfg i m (Ok eff m' evs) <-> syscall_spec i m (Ok eff m' evs).
Proof.
  intros i m eff m' evs Hh. unfold syscall_spec_acfg. split; [tauto|]. intros H. split; [exact H|].
  cbn. intros Hn. contradiction.
Qed.

Lemma exists_nonspurious (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff0 : SyscallEffect) (m0 : Model) (evs0 : list event)
  : syscall_spec i m (Ok eff0 m0 evs0)
  -> exists (eff : SyscallEffect) (m' : Model) (evs : list event),
       syscall_spec i m (Ok eff m' evs) /\ not (spurious_refusal_cfg cfg i m eff).
Proof.
  intro Hspec0; destruct (classic (spurious_refusal_cfg cfg i m eff0)) as [Hsp | Hnsp].
  - destruct Hsp as [_ [_ [eff1 [m1 [evs1 [Hspec1 Hnr1]]]]]]; exists eff1, m1, evs1.
    exact (conj Hspec1 (spurious_refusal_not_refusal cfg i m eff1 Hnr1)).
  - exists eff0, m0, evs0; exact (conj Hspec0 Hnsp).
Qed.

Lemma exists_acfg (i : SyscallInput) (m : Model) (eff0 : SyscallEffect) (m0 : Model)
    (evs0 : list event)
  : syscall_spec i m (Ok eff0 m0 evs0)
  -> exists (eff : SyscallEffect) (m' : Model) (evs : list event), syscall_spec_acfg i m (Ok eff m' evs).
Proof.
  intro Hspec0; destruct (exists_nonspurious ACFG i m eff0 m0 evs0 Hspec0)
    as [eff1 [m1 [evs1 [Hspec1 Hnsp1]]]].
  exists eff1, m1, evs1; split; [exact Hspec1 | intros _; exact Hnsp1].
Qed.

Lemma nonspurious_refusal_forced (i : SyscallInput) (m : Model) (eff : SyscallEffect)
  : not (spurious_refusal_cfg ACFG i m eff)
  -> injected_family_off ACFG i = true
  -> refusal_b i m (eff_ret eff) = true
  -> forall (eff' : SyscallEffect) (m' : Model) (evs' : list event),
     syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true.
Proof.
  intros Hnsp Hoff Href eff2 m2 evs2 Hspec2.
  case_eq (refusal_b i m (eff_ret eff2)); intro Hr2; [reflexivity | exfalso].
  apply Hnsp; split; [exact Hoff | split; [exact Href | exists eff2, m2, evs2; split; assumption]].
Qed.

Lemma acfg_refusal_forced (i : SyscallInput) (m : Model) (eff : SyscallEffect)
    (m' : Model) (evs : list event)
  : syscall_spec_acfg i m (Ok eff m' evs)
  -> m_halted m' = None
  -> injected_family_off ACFG i = true
  -> refusal_b i m (eff_ret eff) = true
  -> forall (eff' : SyscallEffect) (m'' : Model) (evs' : list event),
     syscall_spec i m (Ok eff' m'' evs') -> refusal_b i m (eff_ret eff') = true.
Proof.
  intros [_ Hstep_ok] Hnot_halted.
  exact (nonspurious_refusal_forced i m eff (Hstep_ok Hnot_halted)).
Qed.

Lemma acfg_char_split (i : SyscallInput) (m : Model)
    (Ref Grant : outcome SyscallEffect -> Prop) (forced : bool)
  : injected_family_off ACFG i = true
  -> (forall o : outcome SyscallEffect, syscall_spec i m o <-> Ref o \/ Grant o)
  -> (forall (eff : SyscallEffect) (m' : Model) (evs : list event),
        syscall_spec i m (Ok eff m' evs) -> m_halted m' = None)
  -> (forall o : outcome SyscallEffect, Ref o -> exists (eff : SyscallEffect) (m' : Model)
        (evs : list event), o = Ok eff m' evs /\ refusal_b i m (eff_ret eff) = true)
  -> (forall o : outcome SyscallEffect, Grant o -> exists (eff : SyscallEffect) (m' : Model)
        (evs : list event), o = Ok eff m' evs /\ refusal_b i m (eff_ret eff) = false)
  -> (forall o : outcome SyscallEffect, Grant o -> forced = false)
  -> (forced = false -> exists o : outcome SyscallEffect, Grant o)
  -> forall o : outcome SyscallEffect,
     (syscall_spec_acfg i m o <-> (forced = true /\ Ref o) \/ Grant o).
Proof.
  intros Hfam Hsplit Hlive Href_ok Hgrant_ok Hgrant_forced Hgrant_some o; split.
  - intros [Hspec_o Hstep_o]; destruct (proj1 (Hsplit o) Hspec_o) as [Hr_o | Hg_o];
      [| right; exact Hg_o].
    left; split; [| exact Hr_o]; destruct forced; [reflexivity | exfalso].
    destruct (Href_ok o Hr_o) as [effr [mr [evsr [Ho Href_true]]]]; subst o.
    destruct (Hgrant_some eq_refl) as [og Hg_og].
    destruct (Hgrant_ok og Hg_og) as [effg [mg [evsg [Hog Hgrant_false]]]]; subst og.
    apply (Hstep_o (Hlive _ _ _ Hspec_o)); split; [exact Hfam |]; split; [exact Href_true |].
    exists effg, mg, evsg; split; [apply Hsplit; right; exact Hg_og | exact Hgrant_false].
  - intros [[Hforced_true Hr_o] | Hg_o].
    + split; [apply Hsplit; left; exact Hr_o |].
      destruct (Href_ok o Hr_o) as [effr [mr [evsr [Ho Href_true]]]]; subst o.
      intros _ [_ [_ [eff2 [m2 [evs2 [Hspec2 Hnr2]]]]]].
      destruct (proj1 (Hsplit _) Hspec2) as [Hr2 | Hg2].
      * destruct (Href_ok _ Hr2) as [eff3 [m3 [evs3 [Heq3 Hr3]]]].
        injection Heq3 as Heff _ _; subst eff3; congruence.
      * rewrite (Hgrant_forced _ Hg2) in Hforced_true; discriminate Hforced_true.
    + split; [apply Hsplit; right; exact Hg_o |].
      destruct (Hgrant_ok o Hg_o) as [effg [mg [evsg [Ho Hgrant_false]]]]; subst o.
      intros _; exact (spurious_refusal_not_refusal ACFG i m effg Hgrant_false).
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma sstep_cfg_halted_none (c : config) (e : list event) (st : step_to)
  : sstep_cfg segs ACFG c e st -> m_halted (cfg_model c) = None.
Proof. intro Hst; destruct Hst; assumption. Qed.

Lemma star_cfg_halted_nil (c : config) (tr : list event) (c' : config)
  : m_halted (cfg_model c) <> None
  -> star_cfg segs ACFG c tr c' -> tr = nil /\ c' = c.
Proof.
  intros Hhalted Hstar; destruct Hstar as [c0 | c1 evs1 c2 tr2 c3 Hfirst _];
    [split; reflexivity |].
  exfalso; apply Hhalted; exact (sstep_cfg_halted_none c1 evs1 (SNext c2) Hfirst).
Qed.

Lemma star_cfg_one : forall c evs c',
  sstep_cfg segs ACFG c evs (SNext c') -> star_cfg segs ACFG c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs).
  econstructor; [exact H | apply star_cfg_refl].
Qed.

Lemma star_cfg_trans (c1 : config) (t1 : list event) (c2 : config) (t2 : list event)
    (c3 : config)
  : star_cfg segs ACFG c1 t1 c2
  -> star_cfg segs ACFG c2 t2 c3 -> star_cfg segs ACFG c1 (t1 ++ t2) c3.
Proof.
  intro Hleft; revert t2 c3; induction Hleft as [x | x evsx y trx z Hxy _ IHrest];
    intros t2' w Hright; [exact Hright |].
  rewrite <- app_assoc.
  exact (star_cfg_step segs ACFG x evsx y (trx ++ t2') w Hxy (IHrest t2' w Hright)).
Qed.

Lemma obs_trace_cfg_nil (c : config) : obs_trace_cfg segs ACFG c nil.
Proof. exists nil; exists c; exact (conj (star_cfg_refl segs ACFG c) (is_prefix_nil nil)). Qed.

Lemma star_cfg_inv (Inv : config -> Prop)
    (Hstep : forall (c : config) (evs : list event) (c' : config),
       Inv c -> sstep_cfg segs ACFG c evs (SNext c') -> Inv c')
  : forall (c : config) (tr : list event) (c' : config),
    Inv c -> star_cfg segs ACFG c tr c' -> Inv c'.
Proof.
  intros c tr c' Hinv Hstar; revert Hinv.
  induction Hstar as [x | x evsx y trx z Hxy _ IHrest]; intro Hx; [exact Hx |].
  exact (IHrest (Hstep x evsx y Hx Hxy)).
Qed.

Lemma inv_no_reaches_error_cfg (Inv : config -> Prop)
    (Hstep : forall (c : config) (evs : list event) (c' : config),
       Inv c -> sstep_cfg segs ACFG c evs (SNext c') -> Inv c')
    (Hnoerr : forall (c : config) (evs : list event),
       Inv c -> not (sstep_cfg segs ACFG c evs SError))
  : forall c : config, Inv c -> not (reaches_error_cfg segs ACFG c).
Proof.
  intros c Hc [tr [cerr [evs [Hreach Herr]]]].
  exact (Hnoerr cerr evs (star_cfg_inv Inv Hstep c tr cerr Hc Hreach) Herr).
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

Lemma sstep_cfg_syscall_acfg (ms : machine_state) (model : Model) (x8 : word)
    (eff : SyscallEffect) (model' model'' : Model) (evs : list event)
  : m_halted model = None
  -> ms_svc_pending ms = Some x8
  -> syscall_spec_acfg (sys_input segs ms x8) model (Ok eff model' evs)
  -> m_halted model' = None
  -> materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
  -> sstep_cfg segs ACFG {| cfg_ms := ms; cfg_model := model |} evs
       (SNext {| cfg_ms := advance_past_svc (apply_effect ms eff); cfg_model := model'' |}).
Proof.
  intros Hlive Hpend [Hspec Hok] Hlive' Hmat.
  apply sstep_cfg_syscall with (x8 := x8) (model' := model'); try assumption.
  exact (Hok Hlive').
Qed.

Lemma sstep_cfg_syscall_mf_acfg (ms : machine_state) (model : Model) (x8 : word)
    (eff : SyscallEffect) (model' : Model) (evs : list event)
  : m_halted model = None
  -> ms_svc_pending ms = Some x8
  -> syscall_spec_acfg (sys_input segs ms x8) model (Ok eff model' evs)
  -> m_halted model' = None
  -> materialize_model_accesses model' (syscall_effect_accesses eff) = None
  -> sstep_cfg segs ACFG {| cfg_ms := ms; cfg_model := model |} nil SError.
Proof.
  intros Hlive Hpend [Hspec Hok] Hlive' Hmat.
  refine (sstep_cfg_syscall_materialization_fault segs ACFG ms model x8 eff model' evs
            Hlive Hpend Hspec _ Hlive' Hmat).
  exact (Hok Hlive').
Qed.

Lemma sstep_cfg_sys_inv_acfg (ms : machine_state) (model : Model) (x8 : word)
    (evs : list event) (st : step_to)
  : ms_svc_pending ms = Some x8
  -> sstep_cfg segs ACFG {| cfg_ms := ms; cfg_model := model |} evs st
  -> let i := sys_input segs ms x8 in
     (exists (eff : SyscallEffect) (model' : Model) (evs0 : list event),
        syscall_spec_acfg i model (Ok eff model' evs0) /\ m_halted model' = None
        /\ match materialize_model_accesses model' (syscall_effect_accesses eff) with
        | Some model'' => evs = evs0 /\
            st = SNext {| cfg_ms := advance_past_svc (apply_effect ms eff); cfg_model := model'' |}
        | None => evs = nil /\ st = SError
        end)
     \/ (exists (eff : SyscallEffect) (model' : Model) (evs0 : list event) (code' : word),
           syscall_spec_acfg i model (Ok eff model' evs0) /\ m_halted model' = Some code' /\
           m_killed model' = None /\ evs = (evs0 ++ ExitEv code' (m_fs model') :: nil)%list /\
           st = SNext {| cfg_ms := ms; cfg_model := model' |})
     \/ (exists (eff : SyscallEffect) (model' : Model) (evs0 : list event) (sig : word),
           syscall_spec_acfg i model (Ok eff model' evs0) /\ m_killed model' = Some sig /\
           evs = (evs0 ++ KillEv sig (m_fs model') :: nil)%list /\
           st = SNext {| cfg_ms := ms; cfg_model := model' |})
     \/ (syscall_spec_acfg i model Unmodeled /\ evs = nil /\ st = SError).
Proof.
  intros Hpend Hstep; cbv zeta; inversion Hstep; subst;
    try (match goal with Hnone : ms_svc_pending ms = None |- _ => congruence end);
    match goal with Hsome : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hpend in Hsome; injection Hsome; intro Hy; subst y end.
  - left; do 3 eexists; split; [split; [eassumption | intro; eassumption] |].
    split; [eassumption |].
    match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ =>
      rewrite Hm; split; reflexivity end.
  - left; do 3 eexists; split; [split; [eassumption | intro; eassumption] |].
    split; [eassumption |].
    match goal with Hm : materialize_model_accesses _ _ = None |- _ =>
      rewrite Hm; split; reflexivity end.
  - right; left; do 4 eexists.
    split; [split; [eassumption | intro Hnone; exfalso; congruence] |].
    repeat split; try eassumption; reflexivity.
  - right; right; left; do 4 eexists.
    split; [split; [eassumption | intro Hnone; exfalso] |].
    + match goal with Hk : m_killed _ = Some _ |- _ =>
        rewrite (m_killed_of_m_halted_none _ Hnone) in Hk; discriminate Hk end.
    + repeat split; try eassumption; reflexivity.
  - right; right; right; split; [split; [eassumption | exact I] | split; reflexivity].
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

Definition mmap_fixed_fresh_refusable
  (flags : word) (m : Model) (nZ : Z) : bool := negb (mmap_noreserve_backed_ok flags m nZ).

Definition mmap_fixed_commit_refusable
  (flags : word) (m : Model) (addr n : word) : bool := negb (mmap_fixed_rw_budget_ok flags m addr n).

Definition mmap_fixed_span_refusable
  (flags : word) (m : Model) (addr n : word) : bool :=
  negb (mmap_fixed_rw_span_budget_ok flags m addr n).

Definition mprotect_errnos_when (forced : bool) : list Z :=
  if forced then mprotect_errnos else [].

Definition mprotect_refusable (m : Model) (addr n : word) : bool :=
  negb (mprotect_budget_ok m addr n).

(* The two directions relating a refusable grant/reserve arm to the existence of a free, page-aligned base. *)
Lemma grant_conj_not_refusable (flags : word) (m : Model) (nZ : Z) (a : word)
  : (bv_unsigned a mod page_size)%Z = 0%Z
  -> (0 < bv_unsigned a)%Z
  -> (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z
  -> region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true
  -> mmap_noreserve_backed_ok flags m nZ = true
  -> mmap_grant_refusable flags m nZ = false.
Proof.
  intros Hal Hpos Htop Hfree Hbacked.
  assert (Hgap : vm_gap_available (m_vmmaps m) nZ = true)
    by (apply vm_gap_available_iff; exists a; tauto).
  unfold mmap_grant_refusable; rewrite Hbacked, Hgap; reflexivity.
Qed.

Lemma reserve_conj_not_refusable (m : Model) (nZ : Z) (a : word)
  : (bv_unsigned a mod page_size)%Z = 0%Z
  -> (0 < bv_unsigned a)%Z
  -> (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z
  -> region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true
  -> mmap_reserve_refusable m nZ = false.
Proof.
  intros Hal Hpos Htop Hfree.
  assert (Hgap : vm_gap_available (m_vmmaps m) nZ = true)
    by (apply vm_gap_available_iff; exists a; tauto).
  unfold mmap_reserve_refusable; rewrite Hgap; reflexivity.
Qed.

Lemma not_refusable_grant_conj (flags : word) (m : Model) (nZ : Z)
  : mmap_grant_refusable flags m nZ = false
  -> mmap_noreserve_backed_ok flags m nZ = true
     /\ (exists a : word, (bv_unsigned a mod page_size)%Z = 0%Z /\ (0 < bv_unsigned a)%Z /\
           (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z /\ region_free (vm_reserved (m_vmmaps m)
             ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true).
Proof.
  unfold mmap_grant_refusable; intro Hnot; apply orb_false_iff in Hnot; destruct Hnot as [Hb Hg].
  apply negb_false_iff in Hb; apply negb_false_iff in Hg.
  split; [exact Hb | exact (proj1 (vm_gap_available_iff (m_vmmaps m) nZ) Hg)].
Qed.

Lemma not_refusable_reserve_conj (m : Model) (nZ : Z)
  : mmap_reserve_refusable m nZ = false
  -> exists a : word, (bv_unsigned a mod page_size)%Z = 0%Z /\ (0 < bv_unsigned a)%Z /\
       (bv_unsigned a + nZ <= alloc_top (m_vmmaps m))%Z /\ region_free (vm_reserved (m_vmmaps m)
         ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true.
Proof.
  unfold mmap_reserve_refusable; intro Hnot; apply negb_false_iff in Hnot.
  exact (proj1 (vm_gap_available_iff (m_vmmaps m) nZ) Hnot).
Qed.
