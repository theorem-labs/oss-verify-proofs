(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegVC SegLin.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjVCPre.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWV.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NUMP_D.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOW_vcs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWG_vcA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Import NUMP_D.SLOW_defs.
(* [comment removed for export] *)

Lemma SLOWG_vc_4_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_4.
Proof. unfold SLOWG_vc_4. SNV.sn_solve. Qed.
Lemma SLOWG_vc_12_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_12.
Proof. unfold SLOWG_vc_12. SNV.sn_solve. Qed.
Lemma SLOWG_vc_20_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_20.
Proof. unfold SLOWG_vc_20. SNV.sn_solve. Qed.
Lemma SLOWG_vc_28_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_28.
Proof. unfold SLOWG_vc_28. SNV.sn_solve. Qed.
Lemma SLOWG_vc_36_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_36.
Proof. unfold SLOWG_vc_36. SNV.sn_solve. Qed.
Lemma SLOWG_vc_44_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_44.
Proof. unfold SLOWG_vc_44. SNV.sn_solve. Qed.
Lemma SLOWG_vc_52_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_52.
Proof. unfold SLOWG_vc_52. SNV.sn_solve. Qed.

Import NUMP_D.SLOW_defs.
(* [comment removed for export] *)

Lemma SLOWG_vc_5_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_5.
Proof. unfold SLOWG_vc_5. SNV.sn_solve. Qed.
Lemma SLOWG_vc_13_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_13.
Proof. unfold SLOWG_vc_13. SNV.sn_solve. Qed.
Lemma SLOWG_vc_21_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_21.
Proof. unfold SLOWG_vc_21. SNV.sn_solve. Qed.
Lemma SLOWG_vc_29_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_29.
Proof. unfold SLOWG_vc_29. SNV.sn_solve. Qed.
Lemma SLOWG_vc_37_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_37.
Proof. unfold SLOWG_vc_37. SNV.sn_solve. Qed.
Lemma SLOWG_vc_45_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_45.
Proof. unfold SLOWG_vc_45. SNV.sn_solve. Qed.
Lemma SLOWG_vc_53_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_53.
Proof. unfold SLOWG_vc_53. SNV.sn_solve. Qed.

Import NUMP_D.SLOW_defs.
(* [comment removed for export] *)

Lemma SLOWG_vc_6_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_6.
Proof. unfold SLOWG_vc_6. SNV.sn_solve. Qed.
Lemma SLOWG_vc_14_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_14.
Proof. unfold SLOWG_vc_14. SNV.sn_solve. Qed.
Lemma SLOWG_vc_22_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_22.
Proof. unfold SLOWG_vc_22. SNV.sn_solve. Qed.
Lemma SLOWG_vc_30_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_30.
Proof. unfold SLOWG_vc_30. SNV.sn_solve. Qed.
Lemma SLOWG_vc_38_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_38.
Proof. unfold SLOWG_vc_38. SNV.sn_solve. Qed.
Lemma SLOWG_vc_46_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_46.
Proof. unfold SLOWG_vc_46. SNV.sn_solve. Qed.
Lemma SLOWG_vc_54_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_54.
Proof. unfold SLOWG_vc_54. SNV.sn_solve. Qed.

Import NUMP_D.SLOW_defs.
(* [comment removed for export] *)

Lemma SLOWG_vc_7_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_7.
Proof. unfold SLOWG_vc_7. SNV.sn_solve. Qed.
Lemma SLOWG_vc_15_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_15.
Proof. unfold SLOWG_vc_15. SNV.sn_solve. Qed.
Lemma SLOWG_vc_23_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_23.
Proof. unfold SLOWG_vc_23. SNV.sn_solve. Qed.
Lemma SLOWG_vc_31_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_31.
Proof. unfold SLOWG_vc_31. SNV.sn_solve. Qed.
Lemma SLOWG_vc_39_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_39.
Proof. unfold SLOWG_vc_39. SNV.sn_solve. Qed.
Lemma SLOWG_vc_47_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_47.
Proof. unfold SLOWG_vc_47. SNV.sn_solve. Qed.
Lemma SLOWG_vc_55_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_55.
Proof. unfold SLOWG_vc_55. SNV.sn_solve. Qed.

Import NUMP_D.SLOW_defs.
(* [comment removed for export] *)


Lemma SLOWG_GV_ok : Forall (SG.vc_holds SG (SNG.sng_gp SG)) SLOWG_GV.
Proof.
  unfold SLOWG_GV.
  apply Forall_cons; [exact SLOWG_vc_0_ok|].
  apply Forall_cons; [exact SLOWG_vc_1_ok|].
  apply Forall_cons; [exact SLOWG_vc_2_ok|].
  apply Forall_cons; [exact SLOWG_vc_3_ok|].
  apply Forall_cons; [exact SLOWG_vc_4_ok|].
  apply Forall_cons; [exact SLOWG_vc_5_ok|].
  apply Forall_cons; [exact SLOWG_vc_6_ok|].
  apply Forall_cons; [exact SLOWG_vc_7_ok|].
  apply Forall_cons; [exact SLOWG_vc_8_ok|].
  apply Forall_cons; [exact SLOWG_vc_9_ok|].
  apply Forall_cons; [exact SLOWG_vc_10_ok|].
  apply Forall_cons; [exact SLOWG_vc_11_ok|].
  apply Forall_cons; [exact SLOWG_vc_12_ok|].
  apply Forall_cons; [exact SLOWG_vc_13_ok|].
  apply Forall_cons; [exact SLOWG_vc_14_ok|].
  apply Forall_cons; [exact SLOWG_vc_15_ok|].
  apply Forall_cons; [exact SLOWG_vc_16_ok|].
  apply Forall_cons; [exact SLOWG_vc_17_ok|].
  apply Forall_cons; [exact SLOWG_vc_18_ok|].
  apply Forall_cons; [exact SLOWG_vc_19_ok|].
  apply Forall_cons; [exact SLOWG_vc_20_ok|].
  apply Forall_cons; [exact SLOWG_vc_21_ok|].
  apply Forall_cons; [exact SLOWG_vc_22_ok|].
  apply Forall_cons; [exact SLOWG_vc_23_ok|].
  apply Forall_cons; [exact SLOWG_vc_24_ok|].
  apply Forall_cons; [exact SLOWG_vc_25_ok|].
  apply Forall_cons; [exact SLOWG_vc_26_ok|].
  apply Forall_cons; [exact SLOWG_vc_27_ok|].
  apply Forall_cons; [exact SLOWG_vc_28_ok|].
  apply Forall_cons; [exact SLOWG_vc_29_ok|].
  apply Forall_cons; [exact SLOWG_vc_30_ok|].
  apply Forall_cons; [exact SLOWG_vc_31_ok|].
  apply Forall_cons; [exact SLOWG_vc_32_ok|].
  apply Forall_cons; [exact SLOWG_vc_33_ok|].
  apply Forall_cons; [exact SLOWG_vc_34_ok|].
  apply Forall_cons; [exact SLOWG_vc_35_ok|].
  apply Forall_cons; [exact SLOWG_vc_36_ok|].
  apply Forall_cons; [exact SLOWG_vc_37_ok|].
  apply Forall_cons; [exact SLOWG_vc_38_ok|].
  apply Forall_cons; [exact SLOWG_vc_39_ok|].
  apply Forall_cons; [exact SLOWG_vc_40_ok|].
  apply Forall_cons; [exact SLOWG_vc_41_ok|].
  apply Forall_cons; [exact SLOWG_vc_42_ok|].
  apply Forall_cons; [exact SLOWG_vc_43_ok|].
  apply Forall_cons; [exact SLOWG_vc_44_ok|].
  apply Forall_cons; [exact SLOWG_vc_45_ok|].
  apply Forall_cons; [exact SLOWG_vc_46_ok|].
  apply Forall_cons; [exact SLOWG_vc_47_ok|].
  apply Forall_cons; [exact SLOWG_vc_48_ok|].
  apply Forall_cons; [exact SLOWG_vc_49_ok|].
  apply Forall_cons; [exact SLOWG_vc_50_ok|].
  apply Forall_cons; [exact SLOWG_vc_51_ok|].
  apply Forall_cons; [exact SLOWG_vc_52_ok|].
  apply Forall_cons; [exact SLOWG_vc_53_ok|].
  apply Forall_cons; [exact SLOWG_vc_54_ok|].
  apply Forall_cons; [exact SLOWG_vc_55_ok|].
  apply Forall_nil.
Qed.
