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
Lemma U1G_vc_26_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_26.
Proof. intros d. unfold U1G_vc_26. s1p_solve. Qed.
Lemma U1G_vc_27_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_27.
Proof. intros d. unfold U1G_vc_27. s1p_solve. Qed.
Lemma U1G_vc_28_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_28.
Proof. intros d. unfold U1G_vc_28. s1p_solve. Qed.
Lemma U1G_vc_29_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_29.
Proof. intros d. unfold U1G_vc_29. s1p_solve. Qed.
Lemma U1G_vc_30_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_30.
Proof. intros d. unfold U1G_vc_30. s1p_solve. Qed.
Lemma U1G_vc_31_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_31.
Proof. intros d. unfold U1G_vc_31. s1p_solve. Qed.
Lemma U1G_vc_32_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_32.
Proof. intros d. unfold U1G_vc_32. s1p_solve. Qed.
Lemma U1G_vc_33_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_33.
Proof. intros d. unfold U1G_vc_33. s1p_solve. Qed.
Lemma U1G_vc_34_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_34.
Proof. intros d. unfold U1G_vc_34. s1p_solve. Qed.
Lemma U1G_vc_35_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_35.
Proof. intros d. unfold U1G_vc_35. s1p_solve. Qed.
Lemma U1G_vc_36_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_36.
Proof. intros d. unfold U1G_vc_36. s1p_solve. Qed.
Lemma U1G_vc_37_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_37.
Proof. intros d. unfold U1G_vc_37. s1p_solve. Qed.
Lemma U1G_vc_38_ok : forall d, SG.vc_holds SG (s1_gp d) U1G_vc_38.
Proof. intros d. unfold U1G_vc_38. s1p_solve. Qed.
