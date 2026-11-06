(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzInv BzTables BzContracts DecCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK DecCutF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0F_g10A.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.

Section ACeilS1. Context {ACEIL__ : ACeil}.
Lemma g10_save0_of_bytes : forall segs m A,
  rw_cells segs m A [CB 108 (repeat (Z_to_bv 8 0) 108)] -> rw_cells segs m A SAVE0_CELLS.
Proof.
  intros segs m A H. eapply (rw_cells_same_bytes segs m A _ SAVE0_CELLS); [ | | | exact H].
  - vm_compute. reflexivity.
  - reflexivity.
  - unfold SAVE0_CELLS. cbn [cells_wf cell_wf]. repeat split.
Qed.
Lemma g10_save0_save_cells : forall segs m A,
  rw_cells segs m A SAVE0_CELLS -> rw_cells segs m A (SAVE_CELLS (repeat (Z_to_bv 8 0) 44) 0 (repeat (Z_to_bv 8 0) 60)).
Proof.
  intros segs m A H. eapply (rw_cells_same_bytes segs m A SAVE0_CELLS _); [ | | | exact H].
  - vm_compute. reflexivity.
  - reflexivity.
  - cbn [cells_wf cell_wf]. repeat split.
Qed.
Lemma g10_dpureF_bupd : forall cx (b0 : bzs) ai til tih pay J d st,
  dpureF cx (bupd b0 ai til tih) pay J d st -> (ai <= bs_ai b0)%Z -> dpureF cx b0 pay J d st.
Proof.
  intros cx b0 ai til tih pay J d st DP Hai. unfold dpureF, jk_static, bupd in *. destruct b0; cbn in *.
  decompose [and] DP. repeat match goal with |- _ /\ _ => split end; try assumption; lia.
Qed.
End ACeilS1.
