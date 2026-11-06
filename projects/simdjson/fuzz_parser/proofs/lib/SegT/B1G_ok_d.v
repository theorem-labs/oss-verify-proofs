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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegT Require Import B1G_defs B1G_vcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Lemma B1G_vc_72_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_72.
Proof. intros d. unfold B1G_vc_72. s1p_solve. Qed.
Lemma B1G_vc_73_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_73.
Proof. intros d. unfold B1G_vc_73. s1p_solve. Qed.
Lemma B1G_vc_74_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_74.
Proof. intros d. unfold B1G_vc_74. s1p_solve. Qed.
Lemma B1G_vc_75_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_75.
Proof. intros d. unfold B1G_vc_75. s1p_solve. Qed.
Lemma B1G_vc_76_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_76.
Proof. intros d. unfold B1G_vc_76. s1p_solve. Qed.
Lemma B1G_vc_77_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_77.
Proof. intros d. unfold B1G_vc_77. s1p_solve. Qed.
Lemma B1G_vc_78_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_78.
Proof. intros d. unfold B1G_vc_78. s1p_solve. Qed.
Lemma B1G_vc_79_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_79.
Proof. intros d. unfold B1G_vc_79. s1p_solve. Qed.
Lemma B1G_vc_80_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_80.
Proof. intros d. unfold B1G_vc_80. s1p_solve. Qed.
Lemma B1G_vc_81_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_81.
Proof. intros d. unfold B1G_vc_81. s1p_solve. Qed.
Lemma B1G_vc_82_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_82.
Proof. intros d. unfold B1G_vc_82. s1p_solve. Qed.
Lemma B1G_vc_83_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_83.
Proof. intros d. unfold B1G_vc_83. s1p_solve. Qed.
Lemma B1G_vc_84_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_84.
Proof. intros d. unfold B1G_vc_84. s1p_solve. Qed.
Lemma B1G_vc_85_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_85.
Proof. intros d. unfold B1G_vc_85. s1p_solve. Qed.
Lemma B1G_vc_86_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_86.
Proof. intros d. unfold B1G_vc_86. s1p_solve. Qed.
Lemma B1G_vc_87_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_87.
Proof. intros d. unfold B1G_vc_87. s1p_solve. Qed.
Lemma B1G_vc_88_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_88.
Proof. intros d. unfold B1G_vc_88. s1p_solve. Qed.
Lemma B1G_vc_89_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_89.
Proof. intros d. unfold B1G_vc_89. s1p_solve. Qed.
Lemma B1G_vc_90_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_90.
Proof. intros d. unfold B1G_vc_90. s1p_solve. Qed.
Lemma B1G_vc_91_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_91.
Proof. intros d. unfold B1G_vc_91. s1p_solve. Qed.
