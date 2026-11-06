(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import CfgStep ShapeAlg SpinAlg ShapeEFC HaltsKit.
From OSSVerify.Proofs.openssl.pem.lib.Common.LimSim Require Import LimSimSys.
From OSSVerify.Proofs.openssl.pem.lib.Top Require Import TopBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section ImageHalts.
  Variables (segs : list Segment) (pc : N) (ph : PhdrInfo).
  Variable SPEC : list (list byte) -> Fs.Fs -> TSet.
  Variable S : list word.
  Hypothesis SPEC_exits : forall argv fs, exits_in S (SPEC argv fs).
  Hypothesis SPEC_kill_free : forall argv fs, kill_free (SPEC argv fs).

  (* [comment removed for export] *)
  Theorem image_lane_halts : forall lim,
    image_realizes segs pc ph lim SPEC -> lane_halts forced_only_cfg segs pc ph lim S.
  Proof.
    intros lim HR en inp Hen Hv.
    pose proof (image_realizes_at segs pc ph lim SPEC HR en inp Hen Hv) as Hs.
    apply (realizes_of_srealizes segs) in Hs.
    unfold init_cfg_of in Hs. cbn [img_segments img_init_pc img_phdrs] in Hs.
    apply (realizes_must_exit_forced_only segs _ (SPEC (in_argv inp) (in_fs inp)) S Hs).
    - apply SPEC_exits.
    - apply SPEC_kill_free.
    - reflexivity.
  Qed.

  (* [comment removed for export] *)
  Corollary image_must_exit_at : forall lim,
    image_realizes segs pc ph lim SPEC ->
    forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
      must_exit_in_scfg forced_only_cfg S (mkImage segs pc ph) lim en inp.
  Proof.
    intros lim HR en inp Hen Hv. destruct en as [sp brk0 mbase rnd].
    exact (image_lane_halts lim HR (mkEntry sp brk0 mbase rnd) inp Hen Hv).
  Qed.

  (* [comment removed for export] *)
  Theorem image_halts_budgets : forall (Lbig Lsmall : Z),
    Lsmall <= Lbig ->
    image_realizes segs pc ph Lbig SPEC ->
    halts_allowed_T_scfg_budgets forced_only_cfg Lsmall S (mkImage segs pc ph).
  Proof.
    intros Lbig Lsmall Hle HR en inp Hen Hv Hbudget.
    exact (must_exit_in_scfg_relim_closed forced_only_cfg S (mkImage segs pc ph) Lbig Lsmall en inp Hle Hbudget
             (image_must_exit_at Lbig HR en inp Hen Hv)).
  Qed.
End ImageHalts.

(* [comment removed for export] *)
Lemma lim_source_le_target : source_alloc_limit <= target_alloc_limit.
Proof. unfold source_alloc_limit, target_alloc_limit. apply Z.leb_le. reflexivity. Qed.

Lemma lim_source_le_source : source_alloc_limit <= source_alloc_limit.
Proof. apply Z.le_refl. Qed.
