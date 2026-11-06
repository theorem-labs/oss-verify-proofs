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
Lemma B1G_vc_0_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_0.
Proof. intros d. unfold B1G_vc_0. s1p_solve. Qed.
Lemma B1G_vc_1_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_1.
Proof. intros d. unfold B1G_vc_1. s1p_solve. Qed.
Lemma B1G_vc_4_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_4.
Proof. intros d. unfold B1G_vc_4. s1p_solve. Qed.
Lemma B1G_vc_7_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_7.
Proof. intros d. unfold B1G_vc_7. s1p_solve. Qed.
Lemma B1G_vc_8_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_8.
Proof. intros d. unfold B1G_vc_8. s1p_solve. Qed.
Lemma B1G_vc_11_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_11.
Proof. intros d. unfold B1G_vc_11. s1p_solve. Qed.
Lemma B1G_vc_12_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_12.
Proof. intros d. unfold B1G_vc_12. s1p_solve. Qed.
Lemma B1G_vc_13_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_13.
Proof. intros d. unfold B1G_vc_13. s1p_solve. Qed.
Lemma B1G_vc_14_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_14.
Proof. intros d. unfold B1G_vc_14. s1p_solve. Qed.
Lemma B1G_vc_15_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_15.
Proof. intros d. unfold B1G_vc_15. s1p_solve. Qed.
Lemma B1G_vc_16_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_16.
Proof. intros d. unfold B1G_vc_16. s1p_solve. Qed.
Lemma B1G_vc_17_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_17.
Proof. intros d. unfold B1G_vc_17. s1p_solve. Qed.
Lemma B1G_vc_18_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_18.
Proof. intros d. unfold B1G_vc_18. s1p_solve. Qed.
Lemma B1G_vc_19_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_19.
Proof. intros d. unfold B1G_vc_19. s1p_solve. Qed.
Lemma B1G_vc_20_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_20.
Proof. intros d. unfold B1G_vc_20. s1p_solve. Qed.
Lemma B1G_vc_21_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_21.
Proof. intros d. unfold B1G_vc_21. s1p_solve. Qed.
Lemma B1G_vc_22_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_22.
Proof. intros d. unfold B1G_vc_22. s1p_solve. Qed.
Lemma B1G_vc_23_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_23.
Proof. intros d. unfold B1G_vc_23. s1p_solve. Qed.
Lemma B1G_vc_24_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_24.
Proof. intros d. unfold B1G_vc_24. s1p_solve. Qed.
Lemma B1G_vc_25_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_25.
Proof. intros d. unfold B1G_vc_25. s1p_solve. Qed.
Lemma B1G_vc_26_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_26.
Proof. intros d. unfold B1G_vc_26. s1p_solve. Qed.
Lemma B1G_vc_27_ok : forall d, SG.vc_holds SG (s1_gp d) B1G_vc_27.
Proof. intros d. unfold B1G_vc_27. s1p_solve. Qed.
