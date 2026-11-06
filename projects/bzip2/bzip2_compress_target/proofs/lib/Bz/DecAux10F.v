(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
Section ACeilS1. Context {ACEIL__ : ACeil}.
  Lemma dpureF_set_mtfa : forall cx b0 pl J d s i v, dpureF cx b0 pl J d s -> 0 <= v < 256 ->
    dpureF cx b0 pl J (d_set_mtfa d (zset (d_mtfa d) i v)) s.
  Proof.
    intros cx b0 pl J d s i v DP Hv. pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP.
    eapply (dpureF_frame _ _ _ _ _ _ _ _ _ DP); try (destruct d; reflexivity); try exact (dpureF_jwf _ _ _ _ _ _ DP); try exact (dpureF_static _ _ _ _ _ _ DP);
      try exact (dpureF_in _ _ _ _ _ _ DP).
    all: dmodel_cbn.
    - exact (dpureF_bb _ _ _ _ _ _ DP).
    - exact (dpureF_bl _ _ _ _ _ _ DP).
    - exact (proj1 (dpureF_cbn _ _ _ _ _ _ DP)).
    - exact (proj2 (dpureF_cbn _ _ _ _ _ _ DP)).
    - exact (dpureF_snb _ _ _ _ _ _ DP).
    - exact (dpureF_nbu _ _ _ _ _ _ DP).
    - unfold drep in *. dmodel_cbn. destruct d; cbn in *.
      repeat match goal with |- _ /\ _ => split end; try tauto;
      try (intros k; rewrite zget_zset; destruct (k =? i); [lia|]); try apply RP; tauto.
  Qed.
  Lemma dpureF_set_mtfbase : forall cx b0 pl J d s a, dpureF cx b0 pl J d s -> dpureF cx b0 pl J (d_set_mtfbase d a) s.
  Proof.
    intros cx b0 pl J d s a DP. pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP.
    eapply (dpureF_frame _ _ _ _ _ _ _ _ _ DP); try (destruct d; reflexivity); try exact (dpureF_jwf _ _ _ _ _ _ DP); try exact (dpureF_static _ _ _ _ _ _ DP);
      try exact (dpureF_in _ _ _ _ _ _ DP).
    all: dmodel_cbn.
    - exact (dpureF_bb _ _ _ _ _ _ DP).
    - exact (dpureF_bl _ _ _ _ _ _ DP).
    - exact (proj1 (dpureF_cbn _ _ _ _ _ _ DP)).
    - exact (proj2 (dpureF_cbn _ _ _ _ _ _ DP)).
    - exact (dpureF_snb _ _ _ _ _ _ DP).
    - exact (dpureF_nbu _ _ _ _ _ _ DP).
    - unfold drep in *. dmodel_cbn. destruct d; cbn in *. exact RP.
  Qed.
End ACeilS1.
