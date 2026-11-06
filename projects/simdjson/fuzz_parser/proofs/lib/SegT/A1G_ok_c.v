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
Lemma A1G_vc_34_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_34.
Proof. intros d. unfold A1G_vc_34. s1p_solve. Qed.
Lemma A1G_vc_35_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_35.
Proof. intros d. unfold A1G_vc_35. s1p_solve. Qed.
Lemma A1G_vc_36_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_36.
Proof. intros d. unfold A1G_vc_36. s1p_solve. Qed.
Lemma A1G_vc_37_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_37.
Proof. intros d. unfold A1G_vc_37. s1p_solve. Qed.
Lemma A1G_vc_38_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_38.
Proof. intros d. unfold A1G_vc_38. s1p_solve. Qed.
Lemma A1G_vc_39_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_39.
Proof. intros d. unfold A1G_vc_39. s1p_solve. Qed.
Lemma A1G_vc_40_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_40.
Proof. intros d. unfold A1G_vc_40. s1p_solve. Qed.
Lemma A1G_vc_41_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_41.
Proof. intros d. unfold A1G_vc_41. s1p_solve. Qed.
Lemma A1G_vc_42_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_42.
Proof. intros d. unfold A1G_vc_42. s1p_solve. Qed.
Lemma A1G_vc_43_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_43.
Proof. intros d. unfold A1G_vc_43. s1p_solve. Qed.
Lemma A1G_vc_44_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_44.
Proof. intros d. unfold A1G_vc_44. s1p_solve. Qed.
Lemma A1G_vc_45_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_45.
Proof. intros d. unfold A1G_vc_45. s1p_solve. Qed.
Lemma A1G_vc_46_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_46.
Proof. intros d. unfold A1G_vc_46. s1p_solve. Qed.
Lemma A1G_vc_47_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_47.
Proof. intros d. unfold A1G_vc_47. s1p_solve. Qed.
Lemma A1G_vc_48_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_48.
Proof. intros d. unfold A1G_vc_48. s1p_solve. Qed.
Lemma A1G_vc_49_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_49.
Proof. intros d. unfold A1G_vc_49. s1p_solve. Qed.
Lemma A1G_vc_50_ok : forall d, SG.vc_holds SG (s1_gp d) A1G_vc_50.
Proof. intros d. unfold A1G_vc_50. s1p_solve. Qed.
