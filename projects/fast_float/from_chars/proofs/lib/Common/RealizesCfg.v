(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

Section WithSegsCfg.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
Definition node_ok_cfg (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs cfg c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs cfg c e st ->
        exists i, e = evs i /\ st = SNext (nx i)).

(* [comment removed for export] *)
Definition silent_closed (S : config -> Prop) : Prop :=
  forall c, S c -> forall e st, sstep_cfg segs cfg c e st ->
    e = [] /\ exists c', st = SNext c' /\ S c'.

Inductive realizes_cfg : config -> TSet -> Prop :=
| rzc_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok_cfg c I evs nx ->
    (forall i, realizes_cfg (nx i) (T i)) ->
    realizes_cfg c (t_alt (fun i => t_emit (evs i) (T i)))
| rzc_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes_cfg c t_nil
| rzc_conseq : forall c T T',
    realizes_cfg c T -> t_eq T T' -> realizes_cfg c T'.

#[using="Type"] Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs cfg c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

#[using="Type"] Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs cfg c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
Qed.

#[using="Type"] Lemma star_cfg_silent : forall S, silent_closed S ->
  forall c tr c', S c -> star_cfg segs cfg c tr c' -> tr = [] /\ S c'.
Proof.
  intros S HS c tr c' Hc Hstar; revert Hc.
  induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros Hc;
    [split; [reflexivity | exact Hc]|].
  destruct (HS c1 Hc evs (SNext c2) Hss) as (-> & c2' & Heq & Hc2).
  injection Heq as <-. destruct (IH Hc2) as [-> Hc3]. split; [reflexivity | exact Hc3].
Qed.

#[using="Type"] Lemma realizes_cfg_nonempty : forall c T, realizes_cfg c T -> T [].
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

#[using="Type"] Lemma realizes_cfg_pclosed : forall c T, realizes_cfg c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma realizes_cfg_star_only : forall c T, realizes_cfg c T ->
  forall tr c', star_cfg segs cfg c tr c' -> T tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      injection Heq2 as ->.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil c tr c' Hh Hstar) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

#[using="Type"] Lemma obs_trace_cfg_nil : forall c, obs_trace_cfg segs cfg c [].
Proof. intros c. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil]. Qed.

#[using="Type"] Lemma star_cfg_one : forall c evs c',
  sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs).
  econstructor; [exact H | apply star_cfg_refl].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma realizes_cfg_admits : forall c T, realizes_cfg c T ->
  forall tr, T tr -> obs_trace_cfg segs cfg c tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar]
             | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem realizes_cfg_obs_iff : forall c T, realizes_cfg c T ->
  forall tr, obs_trace_cfg segs cfg c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply realizes_cfg_pclosed;
      [exact H | eapply realizes_cfg_star_only; eauto | exact Hp].
  - apply realizes_cfg_admits; exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma realizes_cfg_step : forall c T e c',
  realizes_cfg c T -> sstep_cfg segs cfg c e (SNext c') -> exists T', realizes_cfg c' T'.
Proof.
  intros c T e c' H; revert e c';
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    injection Heq2 as ->. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

#[using="Type"] Lemma realizes_cfg_no_sserror : forall c T e,
  realizes_cfg c T -> ~ sstep_cfg segs cfg c e SError.
Proof.
  intros c T e H; revert e;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate Hbad.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

#[using="Type"] Lemma realizes_cfg_star : forall c T tr c',
  realizes_cfg c T -> star_cfg segs cfg c tr c' -> exists T', realizes_cfg c' T'.
Proof.
  intros c T tr c' H Hstar; revert T H.
  induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros T H; [exists T; exact H|].
  destruct (realizes_cfg_step c1 T evs c2 H Hss) as (T2 & H2). exact (IH T2 H2).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem realizes_cfg_no_error : forall c T,
  realizes_cfg c T -> ~ reaches_error_cfg segs cfg c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  destruct (realizes_cfg_star c T tr c' H Hstar) as (T' & H').
  exact (realizes_cfg_no_sserror c' T' evs H' Herr).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_silent1 : forall c c' T,
  node_ok_cfg c unit (fun _ => []) (fun _ => c') ->
  realizes_cfg c' T ->
  realizes_cfg c T.
Proof.
  intros c c' T Hnode Hc.
  apply (rzc_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rzc_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply realizes_cfg_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_emit1 : forall c c' e T,
  node_ok_cfg c unit (fun _ => e) (fun _ => c') ->
  realizes_cfg c' T ->
  realizes_cfg c (t_emit e T).
Proof.
  intros c c' e T Hnode Hc.
  apply (rzc_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rzc_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_silent_const : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok_cfg c I (fun _ => []) nx ->
  (forall i, realizes_cfg (nx i) T) ->
  realizes_cfg c T.
Proof.
  intros c I nx T i0 Hnode Hc.
  assert (HT : T []) by (eapply realizes_cfg_nonempty; apply (Hc i0)).
  apply (rzc_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (rzc_node c I (fun _ => []) nx (fun _ => T) i0 Hnode). exact Hc.
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT tr) Hi).
    + intro Htr. exists i0. exact (proj2 (t_emit_nil_eq T HT tr) Htr).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                        (a0 : IA) (b0 : IB),
  node_ok_cfg c (IA + IB) (fun _ => []) nx ->
  (forall i, realizes_cfg (nx (inl i)) A) ->
  (forall i, realizes_cfg (nx (inr i)) B) ->
  realizes_cfg c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply realizes_cfg_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply realizes_cfg_nonempty; apply (HB b0)).
  apply (rzc_conseq c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (rzc_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_node_sound : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                              (T : I -> TSet) (i0 : I),
  sstep_cfg segs cfg c (evs i0) (SNext (nx i0)) ->
  (forall e st, sstep_cfg segs cfg c e st -> exists i, e = evs i /\ st = SNext (nx i)) ->
  (forall i, sstep_cfg segs cfg c (evs i) (SNext (nx i)) -> realizes_cfg (nx i) (T i)) ->
  realizes_cfg c (t_alt (fun (j : {i : I | sstep_cfg segs cfg c (evs i) (SNext (nx i))}) =>
                            t_emit (evs (proj1_sig j)) (T (proj1_sig j)))).
Proof.
  intros c I evs nx T i0 H0 Hsound Hcont.
  apply (rzc_node c {i : I | sstep_cfg segs cfg c (evs i) (SNext (nx i))}
           (fun j => evs (proj1_sig j)) (fun j => nx (proj1_sig j))
           (fun j => T (proj1_sig j)) (exist _ i0 H0)).
  - split.
    + intros [i Hi]. exact Hi.
    + intros e st Hss. destruct (Hsound e st Hss) as (i & -> & ->).
      exists (exist _ i Hss). split; reflexivity.
  - intros [i Hi]. apply Hcont. exact Hi.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma node_instr_cfg : forall ms model ms' model',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  node_ok_cfg (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model').
Proof.
  intros ms model ms' model' Hh Hsvc Hacc. split.
  - intros []. apply sstep_cfg_instr; assumption.
  - intros e st Hss. inversion Hss; subst; try congruence.
    exists tt. rewrite Hacc in *.
    match goal with H : MachineOk _ = MachineOk _ |- _ => injection H as -> -> end.
    split; reflexivity.
Qed.

#[using="Type"] Lemma rzc_step_acct : forall ms model ms' model' T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  realizes_cfg (mkCfg ms' model') T ->
  realizes_cfg (mkCfg ms model) T.
Proof.
  intros ms model ms' model' T Hh Hsvc Hacc Hc.
  eapply rzc_silent1; [apply node_instr_cfg; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rzc_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes_cfg (mkCfg ms' model) T ->
  realizes_cfg (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  apply (rzc_step_acct ms model ms' model T Hh Hsvc); [| exact Hc].
  rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

End WithSegsCfg.

(* [comment removed for export] *)
Inductive isteps (segs : list Segment) : machine_state -> machine_state -> Prop :=
| ist_refl : forall ms, isteps segs ms ms
| ist_step : forall ms ms' ms'',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    isteps segs ms' ms'' ->
    isteps segs ms ms''.

Lemma rzc_isteps : forall segs cfg ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  isteps segs ms ms' ->
  realizes_cfg segs cfg (mkCfg ms' model) T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros segs cfg ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intro Hc; [exact Hc|].
  eapply rzc_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem shape_strong_equiv_ef_scfg :
  forall (cfg : SpuriousCfg)
         source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes_cfg source_segs cfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes_cfg target_segs cfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv
       (bh_traces (run_scfg cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
       (bh_traces (run_scfg cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros cfg source_segs rpc rph rsp rbrk rmb rrnd rlim
    target_segs apc aph asp abrk amb arnd alim T inp Hsource Htarget.
  split; [| split].
  - cbn [run_scfg bh_errors]. unfold error_free. cbn [bh_errors].
    eapply realizes_cfg_no_error; exact Hsource.
  - cbn [run_scfg bh_errors]. unfold error_free. cbn [bh_errors].
    eapply realizes_cfg_no_error; exact Htarget.
  - intro tr. cbn [run_scfg bh_traces].
    rewrite (realizes_cfg_obs_iff source_segs cfg _ T Hsource tr).
    rewrite (realizes_cfg_obs_iff target_segs cfg _ T Htarget tr).
    reflexivity.
Qed.

(* [comment removed for export] *)
Theorem shape_strong_equiv_error_free_scfg :
  forall (cfg : SpuriousCfg)
         source_segs rpc rph rsp rbrk rmb rrnd
         target_segs apc aph asp abrk amb arnd
         (T : TSet) (inp : ProcInput),
  realizes_cfg source_segs cfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp) T ->
  realizes_cfg target_segs cfg
    (init_config target_segs apc aph asp abrk amb arnd target_alloc_limit inp) T ->
  strong_equiv_error_free_scfg cfg (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros. unfold strong_equiv_error_free_scfg.
  eapply shape_strong_equiv_ef_scfg; eassumption.
Qed.

(* [comment removed for export] *)
Corollary shape_strong_equiv_error_free_scfg_eq :
  forall (cfg : SpuriousCfg)
         source_segs rpc rph rsp rbrk rmb rrnd
         target_segs apc aph asp abrk amb arnd
         (T T' : TSet) (inp : ProcInput),
  realizes_cfg source_segs cfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp) T ->
  realizes_cfg target_segs cfg
    (init_config target_segs apc aph asp abrk amb arnd target_alloc_limit inp) T' ->
  t_eq T T' ->
  strong_equiv_error_free_scfg cfg (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros until T'. intros inp Hs Ht Heq.
  eapply shape_strong_equiv_error_free_scfg; [| exact Ht].
  eapply rzc_conseq; [exact Hs | exact Heq].
Qed.

(* [comment removed for export] *)
Lemma realizes_cfg_error_free : forall cfg segs pc ph sp brk0 mb rnd lim inp T,
  realizes_cfg segs cfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros. unfold error_free. cbn [run_scfg bh_errors].
  eapply realizes_cfg_no_error; eassumption.
Qed.

Lemma realizes_cfg_traces_iff : forall cfg segs pc ph sp brk0 mb rnd lim inp T tr,
  realizes_cfg segs cfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn [run_scfg bh_traces]. apply realizes_cfg_obs_iff. assumption. Qed.

(* [comment removed for export] *)
Definition image_realizes_cfg (cfg : SpuriousCfg) (segs : list Segment) (pc : N)
    (ph : PhdrInfo) (lim : Z) (Spec : ProcInput -> TSet) : Prop :=
  forall sp brk0 mb rnd inp,
    valid_entry (mkImage segs pc ph) (mkEntry sp brk0 mb rnd) inp ->
    valid_input inp ->
    realizes_cfg segs cfg (init_config segs pc ph sp brk0 mb rnd lim inp) (Spec inp).

(* [comment removed for export] *)
Theorem strong_universal_error_free_T_scfg_of_realizes :
  forall (cfg : SpuriousCfg) source_segs rpc rph target_segs apc aph
         (Spec : ProcInput -> TSet),
  image_realizes_cfg cfg source_segs rpc rph source_alloc_limit Spec ->
  image_realizes_cfg cfg target_segs apc aph target_alloc_limit Spec ->
  strong_universal_error_free_T_scfg cfg (mkImage source_segs rpc rph) (mkImage target_segs apc aph).
Proof.
  intros cfg source_segs rpc rph target_segs apc aph Spec HS HT
    [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hvs Hvt Hinp.
  apply shape_strong_equiv_error_free_scfg with (T := Spec inp).
  - exact (HS rsp rbrk rmb rrnd inp Hvs Hinp).
  - exact (HT asp abrk amb arnd inp Hvt Hinp).
Qed.

(* [comment removed for export] *)
Corollary strong_universal_error_free_T_scfg_of_realizes_eq :
  forall (cfg : SpuriousCfg) source_segs rpc rph target_segs apc aph
         (SpecS SpecT : ProcInput -> TSet),
  image_realizes_cfg cfg source_segs rpc rph source_alloc_limit SpecS ->
  image_realizes_cfg cfg target_segs apc aph target_alloc_limit SpecT ->
  (forall inp, valid_input inp -> t_eq (SpecT inp) (SpecS inp)) ->
  strong_universal_error_free_T_scfg cfg (mkImage source_segs rpc rph) (mkImage target_segs apc aph).
Proof.
  intros cfg source_segs rpc rph target_segs apc aph SpecS SpecT HS HT Heq.
  apply strong_universal_error_free_T_scfg_of_realizes with (Spec := SpecS); [exact HS|].
  intros sp brk0 mb rnd inp Hv Hinp.
  eapply rzc_conseq; [exact (HT sp brk0 mb rnd inp Hv Hinp) | exact (Heq inp Hinp)].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition svc_unfiltered (segs : list Segment) (cfg : SpuriousCfg) (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    injected_family_off cfg (sys_input segs (cfg_ms c) x8) = false.

(* [comment removed for export] *)
Definition injected_family_off_no (cfg : SpuriousCfg) (no : Z) : bool :=
  match injected_arm no with
  | Some a => negb (family_may_fail cfg (ia_family a))
  | None => false
  end.

Lemma injected_family_off_sys_input : forall segs cfg ms x8,
  injected_family_off cfg (sys_input segs ms x8) = injected_family_off_no cfg (bv_unsigned x8).
Proof. reflexivity. Qed.

Lemma svc_unfiltered_instr : forall segs cfg ms model,
  ms_svc_pending ms = None -> svc_unfiltered segs cfg (mkCfg ms model).
Proof. intros segs cfg ms model Hsvc x8 Hx. cbn in Hx. congruence. Qed.

Lemma svc_unfiltered_sys : forall segs cfg ms model x8,
  ms_svc_pending ms = Some x8 ->
  injected_family_off_no cfg (bv_unsigned x8) = false ->
  svc_unfiltered segs cfg (mkCfg ms model).
Proof.
  intros segs cfg ms model x8 Hsvc Hoff y Hy. cbn in Hy.
  rewrite Hsvc in Hy. injection Hy as <-.
  rewrite injected_family_off_sys_input. exact Hoff.
Qed.

(* [comment removed for export] *)
Lemma alloc_only_false_off_no : forall no,
  injected_family_off_no (alloc_only_cfg false) no = true ->
  no = 214%Z \/ no = 216%Z \/ no = 222%Z \/ no = 226%Z.
Proof.
  intros no H. unfold injected_family_off_no, injected_arm, injected_table in H.
  cbn [lookup_injected ia_no] in H.
  repeat match type of H with
  | context [Z.eqb ?k no] =>
      let Ek := fresh "Ek" in
      destruct (Z.eqb k no) eqn:Ek;
        [ apply Z.eqb_eq in Ek; subst no; cbn in H;
          first [ discriminate H | lia ]
        | clear Ek ]
  end.
  cbn in H. discriminate H.
Qed.

Lemma svc_unfiltered_alloc_only : forall segs ms model x8,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 <> 214%Z -> bv_unsigned x8 <> 216%Z ->
  bv_unsigned x8 <> 222%Z -> bv_unsigned x8 <> 226%Z ->
  svc_unfiltered segs (alloc_only_cfg false) (mkCfg ms model).
Proof.
  intros segs ms model x8 Hsvc H1 H2 H3 H4.
  apply (svc_unfiltered_sys segs _ ms model x8 Hsvc).
  destruct (injected_family_off_no (alloc_only_cfg false) (bv_unsigned x8)) eqn:E;
    [| reflexivity].
  exfalso. destruct (alloc_only_false_off_no _ E) as [?|[?|[?|?]]]; congruence.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_of_sstep : forall segs cfg c e st,
  svc_unfiltered segs cfg c ->
  sstep segs c e st -> sstep_cfg segs cfg c e st.
Proof.
  intros segs cfg c e st Hunf Hss.
  destruct Hss as
    [ms model ms' model' Hh Hsvc Hacc
    | ms model Hh Hsvc Hacc
    | ms model Hh Hsvc Hacc
    | ms model x8 eff model' model'' evs Hh Hsvc Hspec Hh' Hmat
    | ms model x8 eff model' evs Hh Hsvc Hspec Hh' Hmat
    | ms model x8 eff model' evs code Hh Hsvc Hspec Hh' Hk
    | ms model x8 eff model' evs sig Hh Hsvc Hspec Hk
    | ms model x8 Hh Hsvc Hspec].
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
  - eapply sstep_cfg_syscall; try eassumption.
    apply spurious_refusal_family_on. exact (Hunf x8 Hsvc).
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption.
    apply spurious_refusal_family_on. exact (Hunf x8 Hsvc).
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

(* [comment removed for export] *)
Lemma node_ok_lift : forall segs cfg c (I : Type) (evs : I -> list event) (nx : I -> config),
  svc_unfiltered segs cfg c ->
  ((forall i, sstep segs c (evs i) (SNext (nx i)))
   /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i))) ->
  node_ok_cfg segs cfg c I evs nx.
Proof.
  intros segs cfg c I evs nx Hunf [Hcomp Hsound]. split.
  - intro i. apply sstep_cfg_of_sstep; [exact Hunf | apply Hcomp].
  - intros e st Hss. apply Hsound. exact (sstep_cfg_sub segs cfg c e st Hss).
Qed.

(* [comment removed for export] *)
Lemma rzc_node_lift : forall segs cfg c (I : Type) (evs : I -> list event) (nx : I -> config)
                             (T : I -> TSet) (i0 : I),
  svc_unfiltered segs cfg c ->
  ((forall i, sstep segs c (evs i) (SNext (nx i)))
   /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i))) ->
  (forall i, realizes_cfg segs cfg (nx i) (T i)) ->
  realizes_cfg segs cfg c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros segs cfg c I evs nx T i0 Hunf Hnode Hcont.
  apply (rzc_node segs cfg c I evs nx T i0); [| exact Hcont].
  apply node_ok_lift; assumption.
Qed.

Section SysNodes.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
#[using="Type"] Lemma node_sys_cfg : forall ms model x8 (I : Type)
    (E : I -> SyscallEffect) (M MM : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (E i) (M i) (EV i))) ->
  (forall i, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model (E i)) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff ->
     exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     m_halted m' = None) ->
  (forall i, materialize_model_accesses (M i) (syscall_effect_accesses (E i)) = Some (MM i)) ->
  node_ok_cfg segs cfg (mkCfg ms model) I EV
    (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (MM i)).
Proof.
  intros ms model x8 I E M MM EV Hh Hsvc Hcomp Hns Hsound Hnu Hnh Hmat. split.
  - intro i. eapply sstep_cfg_syscall; [exact Hh | exact Hsvc | apply Hcomp | apply Hns
                                       | exact (Hnh _ _ _ (Hcomp i)) | apply Hmat].
  - intros e st Hss. inversion Hss; subst;
      match goal with
      | H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1
      | H1 : ms_svc_pending ms = Some ?y |- _ =>
          rewrite Hsvc in H1; injection H1; intro; subst y
      end.
    + (* [comment removed for export] *)
      match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
          destruct (Hsound _ _ _ Hs Hn) as (i & -> & -> & ->);
          rewrite (Hmat i) in Hm; injection Hm as <-
      end.
      exists i. split; reflexivity.
    + (* [comment removed for export] *)
      exfalso.
      match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = None |- _ =>
          destruct (Hsound _ _ _ Hs Hn) as (i & -> & -> & ->);
          rewrite (Hmat i) in Hm; discriminate Hm
      end.
    + (* [comment removed for export] *)
      exfalso.
      match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hc : m_halted ?m1 = Some _ |- _ =>
          rewrite (Hnh _ _ _ Hs) in Hc; discriminate Hc
      end.
    + (* [comment removed for export] *)
      exfalso.
      match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hk : m_killed ?m1 = Some _ |- _ =>
          rewrite (m_killed_of_m_halted_none _ (Hnh _ _ _ Hs)) in Hk; discriminate Hk
      end.
    + (* [comment removed for export] *)
      exfalso. apply Hnu. assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma node_sys_cfg_nl : forall ms model x8 (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (E i) (M i) (EV i))) ->
  (forall i, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model (E i)) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff ->
     exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     m_halted m' = None) ->
  (forall i, m_vm_lazy (M i) = []) ->
  node_ok_cfg segs cfg (mkCfg ms model) I EV
    (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)).
Proof.
  intros ms model x8 I E M EV Hh Hsvc Hcomp Hns Hsound Hnu Hnh Hnl.
  apply (node_sys_cfg ms model x8 I E M M EV); try assumption.
  intro i. apply materialize_model_accesses_no_lazy. apply Hnl.
Qed.

End SysNodes.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition exit_sysno (no : word) : Prop :=
  bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

Lemma syscall_spec_exit_cfg : forall i m o,
  exit_sysno (in_sysno i) ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof.
  intros i m o [E|E]; unfold syscall_spec, dispatch; rewrite E; reflexivity.
Qed.

Lemma exit_spec_ok : forall i m,
  exit_sysno (in_sysno i) ->
  syscall_spec i m
    (Ok (mkEffect (Z_to_bv 64 0) [] [])
        (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []).
Proof.
  intros i m Hno. apply (proj2 (syscall_spec_exit_cfg i m _ Hno)).
  unfold exit_spec, set_halted, ret_only, modify, bind, pure. cbn.
  eexists tt, (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m),
    [], []. repeat split; reflexivity.
Qed.

Lemma exit_spec_ok_inv : forall i m eff m' evs,
  exit_sysno (in_sysno i) ->
  syscall_spec i m (Ok eff m' evs) ->
  eff = mkEffect (Z_to_bv 64 0) [] [] /\
  m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m /\ evs = [].
Proof.
  intros i m eff m' evs Hno Hspec.
  apply (proj1 (syscall_spec_exit_cfg i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct. rewrite app_nil_l in *. repeat split; congruence.
Qed.

Lemma exit_spec_no_unmodeled : forall i m,
  exit_sysno (in_sysno i) -> ~ syscall_spec i m Unmodeled.
Proof.
  intros i m Hno Hspec.
  apply (proj1 (syscall_spec_exit_cfg i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct.
Qed.

Lemma node_exit_cfg : forall segs cfg ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  exit_sysno x8 ->
  node_ok_cfg segs cfg (mkCfg ms model) unit
    (fun _ => [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)])
    (fun _ => mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
Proof.
  intros segs cfg ms model x8 Hh Hsvc Hx8.
  assert (Hno : exit_sysno (in_sysno (sys_input segs ms x8))) by exact Hx8.
  split.
  - intros [].
    replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                     (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
      by reflexivity.
    apply (sstep_cfg_exit segs cfg ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
             (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
             (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)));
      [ exact Hh | exact Hsvc | exact (exit_spec_ok (sys_input segs ms x8) model Hno)
      | apply m_halted_with_halted | apply m_killed_with_halted ].
  - intros e st Hss. inversion Hss; subst;
      match goal with
      | H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1
      | H1 : ms_svc_pending ms = Some ?y |- _ =>
          rewrite Hsvc in H1; injection H1; intro; subst y
      end.
    + exfalso.
      match goal with
      | Hs : syscall_spec _ _ (Ok _ ?m1 _), H6 : m_halted ?m1 = None |- _ =>
          destruct (exit_spec_ok_inv _ _ _ _ _ Hno Hs) as (_ & -> & _);
          rewrite m_halted_with_halted in H6; discriminate H6
      end.
    + exfalso.
      match goal with
      | Hs : syscall_spec _ _ (Ok _ ?m1 _), H6 : m_halted ?m1 = None |- _ =>
          destruct (exit_spec_ok_inv _ _ _ _ _ Hno Hs) as (_ & -> & _);
          rewrite m_halted_with_halted in H6; discriminate H6
      end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok _ ?m1 ?ev), H6 : m_halted ?m1 = Some _ |- _ =>
          destruct (exit_spec_ok_inv _ _ _ _ _ Hno Hs) as (_ & -> & ->);
          rewrite m_halted_with_halted in H6; injection H6 as <-
      end.
      exists tt. split; reflexivity.
    + exfalso.
      match goal with
      | Hs : syscall_spec _ _ (Ok _ ?m1 _), Hk : m_killed ?m1 = Some _ |- _ =>
          destruct (exit_spec_ok_inv _ _ _ _ _ Hno Hs) as (_ & -> & _);
          rewrite m_killed_with_halted in Hk; discriminate Hk
      end.
    + exfalso. eapply exit_spec_no_unmodeled; eassumption.
Qed.

(* [comment removed for export] *)
Lemma rzc_exit : forall segs cfg ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  exit_sysno x8 ->
  realizes_cfg segs cfg (mkCfg ms model)
    (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros segs cfg ms model x8 Hh Hsvc Hx8. unfold t_exit.
  eapply rzc_emit1; [apply (node_exit_cfg segs cfg ms model x8 Hh Hsvc Hx8) |].
  apply rzc_halt. cbn [cfg_model]. rewrite m_halted_with_halted. discriminate.
Qed.
