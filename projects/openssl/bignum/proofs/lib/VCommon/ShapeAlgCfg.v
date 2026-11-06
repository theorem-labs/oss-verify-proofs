(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import CatSim ShapeAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section Facts.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs cfg c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs cfg c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh H. inversion H as [c0 | c1 e c2 tr2 c3 Hs Hst]; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hs.
Qed.

Lemma star_cfg_one : forall c e c',
  sstep_cfg segs cfg c e (SNext c') -> star_cfg segs cfg c e c'.
Proof.
  intros c e c' H. rewrite <- (app_nil_r e).
  eapply star_cfg_step; [exact H | apply star_cfg_refl].
Qed.

Definition silent_inv (S : config -> Prop) : Prop :=
  forall c1 e st, S c1 -> sstep_cfg segs cfg c1 e st -> e = [] /\ exists c2, st = SNext c2 /\ S c2.

Lemma star_cfg_silent_inv : forall (S : config -> Prop), silent_inv S ->
  forall c tr c', star_cfg segs cfg c tr c' -> S c -> tr = [] /\ S c'.
Proof.
  intros S Hinv c tr c' Hstar. induction Hstar as [c | c1 e c2 tr c3 Hs Hst IH]; intros HS.
  - split; [reflexivity | exact HS].
  - destruct (Hinv c1 e (SNext c2) HS Hs) as [-> (c2' & Heq & HS2)]. inversion Heq; subst c2'.
    destruct (IH HS2) as [-> HS3]. split; [reflexivity | exact HS3].
Qed.

Lemma obs_trace_cfg_nil : forall c, obs_trace_cfg segs cfg c [].
Proof. intros c. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil]. Qed.

End Facts.

Section WithCfg.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Definition node_ok_cfg (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs cfg c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs cfg c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Inductive realizes_cfg : config -> TSet -> Prop :=
| rzc_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok_cfg c I evs nx ->
    (forall i, realizes_cfg (nx i) (T i)) ->
    realizes_cfg c (t_alt (fun i => t_emit (evs i) (T i)))
| rzc_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes_cfg c t_nil
| rzc_spin : forall c (S : config -> Prop),
    S c ->
    silent_inv segs cfg S ->
    False ->
    realizes_cfg c t_nil
| rzc_conseq : forall c T T',
    realizes_cfg c T -> t_eq T T' -> realizes_cfg c T'.

Lemma realizes_cfg_nonempty : forall c T, realizes_cfg c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c S0 HS Hinv | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma realizes_cfg_pclosed : forall c T, realizes_cfg c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c S0 HS Hinv | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

Lemma realizes_cfg_star_only : forall c T, realizes_cfg c T ->
  forall tr c', star_cfg segs cfg c tr c' -> T tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c S0 HS Hinv | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil segs cfg c tr c' Hh Hstar) as [-> _]. reflexivity.
  - destruct (star_cfg_silent_inv segs cfg S0 Hinv c tr c' Hstar HS) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

Lemma realizes_cfg_admits : forall c T, realizes_cfg c T ->
  forall tr, T tr -> obs_trace_cfg segs cfg c tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c S0 HS Hinv | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - apply IH. apply Heq. exact HT.
Qed.

Theorem realizes_cfg_obs_iff : forall c T, realizes_cfg c T ->
  forall tr, obs_trace_cfg segs cfg c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply realizes_cfg_pclosed; [exact H | eapply realizes_cfg_star_only; eauto | exact Hp].
  - apply realizes_cfg_admits; exact H.
Qed.

Lemma realizes_cfg_step : forall c T e c',
  realizes_cfg c T -> sstep_cfg segs cfg c e (SNext c') -> exists T', realizes_cfg c' T'.
Proof.
  intros c T e c' H; revert e c';
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c S0 HS Hinv | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - destruct (Hinv c e (SNext c') HS Hss) as [_ (c2 & Heq2 & HS2)]. inversion Heq2; subst c2.
    exfalso. assumption.
  - eapply IH; exact Hss.
Qed.

Lemma realizes_cfg_no_sserror : forall c T e,
  realizes_cfg c T -> ~ sstep_cfg segs cfg c e SError.
Proof.
  intros c T e H; revert e;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c S0 HS Hinv | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - destruct (Hinv c e SError HS Hss) as [_ (c2 & Hbad & _)]. discriminate Hbad.
  - eapply IH; exact Hss.
Qed.

Lemma realizes_cfg_star : forall c T tr c',
  realizes_cfg c T -> star_cfg segs cfg c tr c' -> exists T', realizes_cfg c' T'.
Proof.
  intros c T tr c' H Hstar. revert T H.
  induction Hstar as [c | c1 e c2 tr c3 Hs Hst IH]; intros T H.
  - exists T. exact H.
  - destruct (realizes_cfg_step c1 T e c2 H Hs) as (T2 & H2). exact (IH T2 H2).
Qed.

Theorem realizes_cfg_no_error : forall c T, realizes_cfg c T -> ~ reaches_error_cfg segs cfg c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  destruct (realizes_cfg_star c T tr c' H Hstar) as (T' & H').
  exact (realizes_cfg_no_sserror c' T' evs H' Herr).
Qed.

Lemma rzc_silent1 : forall c c' T,
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

Lemma rzc_silent_all : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok_cfg c I (fun _ => []) nx ->
  (forall i, realizes_cfg (nx i) T) ->
  realizes_cfg c T.
Proof.
  intros c I nx T i0 Hnode Hc.
  assert (HT0 : T []) by (eapply realizes_cfg_nonempty; apply (Hc i0)).
  apply (rzc_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (rzc_node c I (fun _ => []) nx (fun _ => T) i0 Hnode). exact Hc.
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intro Htr. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.

End WithCfg.

Section Transparent.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Definition cfg_transparent (c : config) : Prop :=
  forall e st, sstep segs c e st -> sstep_cfg segs cfg c e st.

Lemma transparent_family_on : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  injected_family_off cfg (sys_input segs ms x8) = false ->
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

Lemma transparent_uninjected : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  injected_arm (bv_unsigned x8) = None ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hno.
  apply (transparent_family_on ms model x8 Hsvc).
  unfold injected_family_off. cbn [sys_input in_sysno]. rewrite Hno. reflexivity.
Qed.

Lemma node_ok_cfg_of_transparent : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
  node_ok segs c I evs nx ->
  cfg_transparent c ->
  node_ok_cfg segs cfg c I evs nx.
Proof.
  intros c I evs nx [Hcomp Hsound] Ht. split.
  - intro i. apply Ht. apply Hcomp.
  - intros e st Hss. apply Hsound. eapply sstep_cfg_sub; exact Hss.
Qed.

End Transparent.

Section Filter.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Definition ret_of (c : config) : word := ms_gpr (cfg_ms c) 0.

End Filter.
