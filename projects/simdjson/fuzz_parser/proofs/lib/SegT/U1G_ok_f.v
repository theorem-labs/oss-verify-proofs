(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegVC.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjInv SjS1Lem SjS1Bytes SjS1Ghost SjVCPre SjS1VC SjS1Pre.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegT Require Import U1G_defs U1G_vcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Lemma U1G_vc_65_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_65.
Proof. intros d. unfold U1G_vc_65. s1p_solve. Qed.
Lemma U1G_vc_66_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_66.
Proof. intros d. unfold U1G_vc_66. s1p_solve. Qed.
Lemma U1G_vc_67_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_67.
Proof. intros d. unfold U1G_vc_67. s1p_solve. Qed.
Lemma U1G_vc_68_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_68.
Proof. intros d. unfold U1G_vc_68. s1p_solve. Qed.
Lemma U1G_vc_69_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_69.
Proof. intros d. unfold U1G_vc_69. s1p_solve. Qed.
Lemma U1G_vc_70_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_70.
Proof. intros d. unfold U1G_vc_70. s1p_solve. Qed.
Lemma U1G_vc_71_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_71.
Proof. intros d. unfold U1G_vc_71. s1p_solve. Qed.
Lemma U1G_vc_72_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_72.
Proof. intros d. unfold U1G_vc_72. s1p_solve. Qed.
Lemma U1G_vc_73_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_73.
Proof. intros d. unfold U1G_vc_73. s1p_solve. Qed.
Lemma U1G_vc_74_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_74.
Proof. intros d. unfold U1G_vc_74. s1p_solve. Qed.
Lemma U1G_vc_75_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_75.
Proof. intros d. unfold U1G_vc_75. s1p_solve. Qed.
Lemma U1G_vc_76_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_76.
Proof. intros d. unfold U1G_vc_76. s1p_solve. Qed.
Lemma U1G_vc_77_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_77.
Proof. intros d. unfold U1G_vc_77. s1p_solve. Qed.
