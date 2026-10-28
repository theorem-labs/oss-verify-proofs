(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
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
