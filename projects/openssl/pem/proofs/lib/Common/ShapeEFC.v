(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import
  SimInv ExitSim CatSim ShapeAlg SpinAlg ShapeEF ShapeEFS CfgStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition init_cfg_of (img : Image) (lim : Z) (en : ExecEntry) (inp : ProcInput) : config :=
  init_config (img_segments img) (img_init_pc img) (img_phdrs img)
              (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp.

Lemma init_cfg_of_mk : forall segs pc ph sp brk0 mb rnd lim inp,
  init_cfg_of (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
  = init_config segs pc ph sp brk0 mb rnd lim inp.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma srealizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
  srealizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg kit_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply srealizes_no_error; eassumption. Qed.

Lemma srealizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  srealizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg kit_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply srealizes_obs_iff. assumption. Qed.

(* [comment removed for export] *)
Theorem srz_strong_equiv_ef_budgets :
  forall (lim_s lim_t : Z) (src tgt : Image) (en_s en_t : ExecEntry)
         (T T' : TSet) (inp : ProcInput),
  srealizes (img_segments src) (init_cfg_of src lim_s en_s inp) T ->
  srealizes (img_segments tgt) (init_cfg_of tgt lim_t en_t inp) T' ->
  t_eq T T' ->
  strong_equiv_error_free_budgets_scfg kit_cfg lim_s lim_t src tgt en_s en_t inp.
Proof.
  intros lim_s lim_t [ssegs spc sph] [tsegs tpc tph] [ssp sbrk smb srnd] [tsp tbrk tmb trnd]
    T T' inp Hs Ht Heq.
  unfold strong_equiv_error_free_budgets_scfg.
  apply (shape_strong_equiv_ss ssegs spc sph ssp sbrk smb srnd lim_s
           tsegs tpc tph tsp tbrk tmb trnd lim_t T' inp); [| exact Ht].
  eapply srz_conseq; [exact Hs | exact Heq].
Qed.

(* [comment removed for export] *)
Theorem srz_strong_equiv_ef_scfg :
  forall (src tgt : Image) (en_s en_t : ExecEntry) (T T' : TSet) (inp : ProcInput),
  srealizes (img_segments src) (init_cfg_of src source_alloc_limit en_s inp) T ->
  srealizes (img_segments tgt) (init_cfg_of tgt target_alloc_limit en_t inp) T' ->
  t_eq T T' ->
  strong_equiv_error_free_scfg kit_cfg src tgt en_s en_t inp.
Proof.
  intros src tgt en_s en_t T T' inp Hs Ht Heq.
  apply (proj1 (strong_equiv_error_free_budgets_scfg_pinned kit_cfg src tgt en_s en_t inp)).
  exact (srz_strong_equiv_ef_budgets _ _ src tgt en_s en_t T T' inp Hs Ht Heq).
Qed.

(* [comment removed for export] *)
Theorem srz_universal_scfg : forall (src tgt : Image),
  (forall en_s en_t inp,
     valid_entry src en_s inp -> valid_entry tgt en_t inp -> valid_input inp ->
     exists T T',
       srealizes (img_segments src) (init_cfg_of src source_alloc_limit en_s inp) T
       /\ srealizes (img_segments tgt) (init_cfg_of tgt target_alloc_limit en_t inp) T'
       /\ t_eq T T') ->
  strong_universal_error_free_T_scfg kit_cfg src tgt.
Proof.
  intros src tgt H en_s en_t inp Hs Ht Hv.
  destruct (H en_s en_t inp Hs Ht Hv) as (T & T' & H1 & H2 & Heq).
  exact (srz_strong_equiv_ef_scfg src tgt en_s en_t T T' inp H1 H2 Heq).
Qed.

(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition srealizes_wb (c : config) (T : TSet) : Prop :=
  ~ reaches_budget_refused_cfg segs kit_cfg c -> srealizes segs c T.

Lemma srealizes_wb_of_srealizes : forall c T, srealizes segs c T -> srealizes_wb c T.
Proof. intros c T H _. exact H. Qed.

Lemma reaches_budget_refused_cfg_step : forall c e c',
  sstep_cfg segs kit_cfg c e (SNext c') ->
  reaches_budget_refused_cfg segs kit_cfg c' -> reaches_budget_refused_cfg segs kit_cfg c.
Proof.
  intros c e c' Hss (tr & c2 & Hstar & Hb).
  exists (e ++ tr), c2. split; [eapply star_cfg_step; eassumption | exact Hb].
Qed.

(* [comment removed for export] *)
Lemma swb_guard : forall c T,
  (~ budget_refused_at segs c -> srealizes_wb c T) -> srealizes_wb c T.
Proof.
  intros c T H Hnr. apply H; [| exact Hnr].
  intros Hb. apply Hnr. exists [], c. split; [apply star_cfg_refl | exact Hb].
Qed.

Lemma swb_node : forall c (I : Type) evs nx (T : I -> TSet) (i0 : I),
  node_ok segs c I evs nx ->
  (forall i, srealizes_wb (nx i) (T i)) ->
  srealizes_wb c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 Hnode Hc Hnr.
  apply (srz_node segs c I evs nx T i0 Hnode). intros i. apply Hc.
  intros Hr. apply Hnr.
  eapply reaches_budget_refused_cfg_step; [apply (proj1 Hnode i) | exact Hr].
Qed.

Lemma swb_conseq : forall c T T', srealizes_wb c T -> t_eq T T' -> srealizes_wb c T'.
Proof. intros c T T' H Heq Hnr. eapply srz_conseq; [apply H; exact Hnr | exact Heq]. Qed.

Lemma swb_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  srealizes_wb c' T -> srealizes_wb c T.
Proof.
  intros c c' T Hnode Hc Hnr. apply (srz_silent1 segs c c' T Hnode). apply Hc.
  intros Hr. apply Hnr.
  eapply reaches_budget_refused_cfg_step; [apply (proj1 Hnode tt) | exact Hr].
Qed.

(* [comment removed for export] *)
Lemma not_budget_refused_alloc : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  ~ budget_refused_at segs (mkCfg ms model) ->
  alloc_budget_refused_b (sys_input segs ms x8) model = false.
Proof.
  intros ms model x8 Hh Hsvc Hnb.
  destruct (alloc_budget_refused_b (sys_input segs ms x8) model) eqn:E; [| reflexivity].
  exfalso. apply Hnb. split; [exact Hh |]. right. exists x8. cbn [cfg_ms cfg_model].
  split; [exact Hsvc | left; exact E].
Qed.

End WithSegs.

(* [comment removed for export] *)
Theorem srz_universal_scfg_budgets : forall (lim_s lim_t : Z) (src tgt : Image),
  (forall en_s en_t inp,
     valid_entry src en_s inp -> valid_entry tgt en_t inp -> valid_input inp ->
     exists T T',
       srealizes_wb (img_segments src) (init_cfg_of src lim_s en_s inp) T
       /\ srealizes (img_segments tgt) (init_cfg_of tgt lim_t en_t inp) T'
       /\ t_eq T T') ->
  strong_universal_error_free_T_scfg_budgets kit_cfg lim_s lim_t src tgt.
Proof.
  intros lim_s lim_t src tgt H en_s en_t inp Hs Ht Hv Hb.
  destruct (H en_s en_t inp Hs Ht Hv) as (T & T' & H1 & H2 & Heq).
  apply (srz_strong_equiv_ef_budgets lim_s lim_t src tgt en_s en_t T T' inp);
    [| exact H2 | exact Heq].
  apply H1. intros Hr. apply Hb.
  destruct src as [ssegs spc sph], en_s as [ssp sbrk smb srnd]. exact Hr.
Qed.

(* [comment removed for export] *)
Corollary srz_universal_scfg_budgets_shipped : forall (src tgt : Image),
  (forall en_s en_t inp,
     valid_entry src en_s inp -> valid_entry tgt en_t inp -> valid_input inp ->
     exists T T',
       srealizes (img_segments src) (init_cfg_of src source_alloc_limit en_s inp) T
       /\ srealizes (img_segments tgt) (init_cfg_of tgt target_alloc_limit en_t inp) T'
       /\ t_eq T T') ->
  strong_universal_error_free_T_scfg_budgets kit_cfg ShippedBudgets.lim_source
    ShippedBudgets.lim_target src tgt.
Proof.
  intros src tgt H.
  apply strong_universal_error_free_T_scfg_budgets_of_scfg.
  apply srz_universal_scfg. exact H.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem srz_good_input_s : forall (O1 O2 : Image) (inp : ProcInput) (T0 : TSet),
  (forall en, valid_entry O1 en inp ->
     exists T, srealizes (img_segments O1) (init_cfg_of O1 source_alloc_limit en inp) T
               /\ t_eq T T0) ->
  (forall en, valid_entry O2 en inp ->
     exists T, srealizes (img_segments O2) (init_cfg_of O2 target_alloc_limit en inp) T
               /\ t_eq T T0) ->
  good_input_s kit_cfg O1 O2 inp.
Proof.
  intros O1 O2 inp T0 H1 H2 en1 en2 Hv1 Hv2.
  destruct (H1 en1 Hv1) as (T & HT & Heq). destruct (H2 en2 Hv2) as (T' & HT' & Heq').
  apply (srz_strong_equiv_ef_scfg O1 O2 en1 en2 T T' inp HT HT').
  eapply t_eq_trans; [exact Heq | apply t_eq_sym; exact Heq'].
Qed.

(* [comment removed for export] *)
Theorem srz_agree_s_refl : forall (X : Image) (lim : Z) (inp : ProcInput) (T0 : TSet),
  (forall en, valid_entry X en inp ->
     exists T, srealizes (img_segments X) (init_cfg_of X lim en inp) T /\ t_eq T T0) ->
  agree_s kit_cfg X X lim inp.
Proof.
  intros X lim inp T0 H. split; [| split; [| split]]; try reflexivity.
  intros enX enY HvX HvY.
  destruct (H enX HvX) as (T & HT & Heq). destruct (H enY HvY) as (T' & HT' & Heq').
  destruct X as [segs pc ph], enX as [sp1 b1 m1 r1], enY as [sp2 b2 m2 r2].
  intro tr.
  rewrite (srealizes_traces_iff _ _ _ _ _ _ _ _ _ _ tr HT).
  rewrite (srealizes_traces_iff _ _ _ _ _ _ _ _ _ _ tr HT').
  rewrite (Heq tr), (Heq' tr). reflexivity.
Qed.
