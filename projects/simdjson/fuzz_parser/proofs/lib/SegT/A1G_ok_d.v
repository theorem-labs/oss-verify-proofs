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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegT Require Import A1G_defs A1G_vcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
Lemma A1G_vc_51_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_51.
Proof. intros d. unfold A1G_vc_51. s1p_solve. Qed.
Lemma A1G_vc_52_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_52.
Proof. intros d. unfold A1G_vc_52. s1p_solve. Qed.
Lemma A1G_vc_53_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_53.
Proof. intros d. unfold A1G_vc_53. s1p_solve. Qed.
Lemma A1G_vc_54_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_54.
Proof. intros d. unfold A1G_vc_54. s1p_solve. Qed.
Lemma A1G_vc_55_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_55.
Proof. intros d. unfold A1G_vc_55. s1p_solve. Qed.
Lemma A1G_vc_56_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_56.
Proof. intros d. unfold A1G_vc_56. s1p_solve. Qed.
Lemma A1G_vc_57_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_57.
Proof. intros d. unfold A1G_vc_57. s1p_solve. Qed.
Lemma A1G_vc_58_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_58.
Proof. intros d. unfold A1G_vc_58. s1p_solve. Qed.
Lemma A1G_vc_59_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_59.
Proof. intros d. unfold A1G_vc_59. s1p_solve. Qed.
Lemma A1G_vc_60_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_60.
Proof. intros d. unfold A1G_vc_60. s1p_solve. Qed.
Lemma A1G_vc_61_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_61.
Proof. intros d. unfold A1G_vc_61. s1p_solve. Qed.
Lemma A1G_vc_62_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_62.
Proof. intros d. unfold A1G_vc_62. s1p_solve. Qed.
Lemma A1G_vc_63_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_63.
Proof. intros d. unfold A1G_vc_63. s1p_solve. Qed.
Lemma A1G_vc_64_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_64.
Proof. intros d. unfold A1G_vc_64. s1p_solve. Qed.
