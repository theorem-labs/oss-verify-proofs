(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import ShapeAlg SpinAlgCfg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Definition src_real (segs : list Segment) (c : config) (TS : list event -> Prop) : Prop :=
  (forall tr, obs_trace_cfg segs CFG c tr <-> TS tr) /\ ~ reaches_error_cfg segs CFG c.

Lemma srealizes_cfg_src_real : forall segs c T, srealizes_cfg segs c T -> src_real segs c T.
Proof.
  intros segs c T H. split; [exact (srealizes_cfg_obs_iff segs c T H) | exact (srealizes_cfg_no_error segs c T H)].
Qed.

(* [comment removed for export] *)
Lemma CFG_spurious_cfg : CFG = mkSpuriousCfg false true true true true true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem cfg_strong_equiv_ef :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (TS TT : list event -> Prop) (inp : ProcInput),
  src_real source_segs (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) TS ->
  srealizes_cfg target_segs (init_config target_segs apc aph asp abrk amb arnd alim inp) TT ->
  (forall tr, TS tr <-> TT tr) ->
  error_free (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg CFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg CFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim TS TT inp
    [Hobs Hnoerr] Htarget Heq.
  split; [| split].
  - cbn. exact Hnoerr.
  - cbn. exact (srealizes_cfg_no_error _ _ _ Htarget).
  - intro tr. cbn.
    rewrite (Hobs tr), (srealizes_cfg_obs_iff target_segs _ TT Htarget tr). apply Heq.
Qed.

(* [comment removed for export] *)
Corollary cfg_strong_equiv_ef_ss :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  srealizes_cfg source_segs (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes_cfg target_segs (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg CFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg CFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg CFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros until inp. intros Hs Ht.
  apply (cfg_strong_equiv_ef source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim T T inp);
    [exact (srealizes_cfg_src_real _ _ _ Hs) | exact Ht | intro tr; reflexivity].
Qed.

(* [comment removed for export] *)
Theorem cfg_universal_error_free_budgets :
  forall (lim_source lim_target : Z) (src tgt : Image)
         (S TT : ProcInput -> list event -> Prop),
  (forall en_source inp, valid_entry src en_source inp -> valid_input inp ->
     match src, en_source with
     | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
         src_real segs (init_config segs pc ph sp brk0 mbase rnd lim_source inp) (S inp)
     end) ->
  (forall en_target inp, valid_entry tgt en_target inp -> valid_input inp ->
     match tgt, en_target with
     | mkImage segs pc ph, mkEntry sp brk0 mbase rnd =>
         srealizes_cfg segs (init_config segs pc ph sp brk0 mbase rnd lim_target inp) (TT inp)
     end) ->
  (forall inp tr, S inp tr <-> TT inp tr) ->
  strong_universal_error_free_T_scfg_budgets CFG lim_source lim_target src tgt.
Proof.
  intros lim_source lim_target [ssegs spc sph] [tsegs tpc tph] S TT HS HT Heq
    [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
  specialize (HS _ _ Hens Hvalid). specialize (HT _ _ Hent Hvalid). cbv beta iota in HS, HT.
  unfold strong_equiv_error_free_budgets_scfg.
  exact (cfg_strong_equiv_ef ssegs spc sph rsp rbrk rmb rrnd lim_source tsegs tpc tph asp abrk amb arnd lim_target
           (S inp) (TT inp) inp HS HT (Heq inp)).
Qed.
