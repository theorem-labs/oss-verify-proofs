(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import SimInv ExitSim CatSim ShapeAlg CfgStep.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Theorem shape_strong_equiv_ef_side :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  rz_side source_segs (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) ->
  rz_side target_segs (init_config target_segs apc aph asp abrk amb arnd alim inp) ->
  error_free (run_scfg kit_cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg kit_cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg kit_cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg kit_cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget Hss Hst.
  split; [| split].
  - cbn. eapply realizes_no_error; eassumption.
  - cbn. eapply realizes_no_error; eassumption.
  - intro tr. cbn.
    rewrite (realizes_obs_iff source_segs _ T Hsource Hss tr).
    rewrite (realizes_obs_iff target_segs _ T Htarget Hst tr).
    reflexivity.
Qed.

(* [comment removed for export] *)
Theorem shape_strong_equiv_ef :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput) {HBs : BigBudget rlim} {HBt : BigBudget alim},
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg kit_cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg kit_cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg kit_cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg kit_cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp HBs HBt Hsource Htarget.
  apply shape_strong_equiv_ef_side with (T := T); [exact Hsource | exact Htarget | |];
    apply rz_side_init_bigc; assumption.
Qed.

(* [comment removed for export] *)
Corollary shape_strong_equiv_ef_eq :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T T' : TSet) (inp : ProcInput) {HBs : BigBudget rlim} {HBt : BigBudget alim},
  realizes source_segs
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  error_free (run_scfg kit_cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg kit_cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg kit_cfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg kit_cfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros until T'. intros inp HBs HBt Hs Ht Heq.
  apply shape_strong_equiv_ef_side with (T := T');
    [eapply rz_conseq; [exact Hs | exact Heq] | exact Ht
    | apply rz_side_init_bigc; assumption | apply rz_side_init_bigc; assumption].
Qed.

(* [comment removed for export] *)
Lemma realizes_error_free_side : forall segs pc ph sp brk0 mb rnd lim inp T,
  realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  rz_side segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  error_free (run_scfg kit_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply realizes_no_error; eassumption. Qed.

Lemma realizes_traces_iff_side : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  rz_side segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  bh_traces (run_scfg kit_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply realizes_obs_iff; assumption. Qed.

Lemma realizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T {HB : BigBudget lim},
  realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg kit_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. apply (realizes_error_free_side segs pc ph sp brk0 mb rnd lim inp T); [assumption | apply rz_side_init_bigc; assumption]. Qed.

Lemma realizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr {HB : BigBudget lim},
  realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg kit_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. apply (realizes_traces_iff_side segs pc ph sp brk0 mb rnd lim inp T); [assumption | apply rz_side_init_bigc; assumption]. Qed.

(* [comment removed for export] *)
Lemma realizes_source_within_budget : forall segs pc ph sp brk0 mb rnd lim inp T,
  realizes segs (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  source_within_budget_scfg kit_cfg lim (mkImage segs pc ph) (mkEntry sp brk0 mb rnd) inp ->
  error_free (run_scfg kit_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp)
  /\ forall tr, bh_traces (run_scfg kit_cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp T H Hw.
  assert (Hs : rz_side segs (init_config segs pc ph sp brk0 mb rnd lim inp)) by (apply rz_side_init_nr; exact Hw).
  split; [exact (realizes_error_free_side segs pc ph sp brk0 mb rnd lim inp T H Hs) |].
  intros tr. exact (realizes_traces_iff_side segs pc ph sp brk0 mb rnd lim inp T tr H Hs).
Qed.
