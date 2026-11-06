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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWV.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMV.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NUMU_D.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWU_vcs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWUG_vcA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Import NUMU_D.SLOWU_defs.
(* [comment removed for export] *)

Lemma SLOWUG_vc_2_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_2.
Proof. unfold SLOWUG_vc_2. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_6_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_6.
Proof. unfold SLOWUG_vc_6. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_10_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_10.
Proof. unfold SLOWUG_vc_10. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_14_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_14.
Proof. unfold SLOWUG_vc_14. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_18_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_18.
Proof. unfold SLOWUG_vc_18. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_22_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_22.
Proof. unfold SLOWUG_vc_22. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_26_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_26.
Proof. unfold SLOWUG_vc_26. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_30_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_30.
Proof. unfold SLOWUG_vc_30. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_34_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_34.
Proof. unfold SLOWUG_vc_34. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_38_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_38.
Proof. unfold SLOWUG_vc_38. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_42_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_42.
Proof. unfold SLOWUG_vc_42. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_46_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_46.
Proof. unfold SLOWUG_vc_46. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_50_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_50.
Proof. unfold SLOWUG_vc_50. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_54_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_54.
Proof. unfold SLOWUG_vc_54. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_58_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_58.
Proof. unfold SLOWUG_vc_58. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_62_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_62.
Proof. unfold SLOWUG_vc_62. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.

Import NUMU_D.SLOWU_defs.
(* [comment removed for export] *)

Lemma SLOWUG_vc_3_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_3.
Proof. unfold SLOWUG_vc_3. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_7_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_7.
Proof. unfold SLOWUG_vc_7. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_11_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_11.
Proof. unfold SLOWUG_vc_11. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_15_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_15.
Proof. unfold SLOWUG_vc_15. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_19_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_19.
Proof. unfold SLOWUG_vc_19. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_23_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_23.
Proof. unfold SLOWUG_vc_23. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_27_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_27.
Proof. unfold SLOWUG_vc_27. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_31_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_31.
Proof. unfold SLOWUG_vc_31. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_35_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_35.
Proof. unfold SLOWUG_vc_35. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_39_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_39.
Proof. unfold SLOWUG_vc_39. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_43_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_43.
Proof. unfold SLOWUG_vc_43. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_47_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_47.
Proof. unfold SLOWUG_vc_47. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_51_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_51.
Proof. unfold SLOWUG_vc_51. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_55_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_55.
Proof. unfold SLOWUG_vc_55. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_59_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_59.
Proof. unfold SLOWUG_vc_59. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_63_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_63.
Proof. unfold SLOWUG_vc_63. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.

Import NUMU_D.SLOWU_defs.
(* [comment removed for export] *)


Lemma SLOWUG_GV_ok : Forall (SG.vc_holds SG (SNU.snu_gp SG)) SLOWUG_GV.
Proof.
  unfold SLOWUG_GV.
  apply Forall_cons; [exact SLOWUG_vc_0_ok|].
  apply Forall_cons; [exact SLOWUG_vc_1_ok|].
  apply Forall_cons; [exact SLOWUG_vc_2_ok|].
  apply Forall_cons; [exact SLOWUG_vc_3_ok|].
  apply Forall_cons; [exact SLOWUG_vc_4_ok|].
  apply Forall_cons; [exact SLOWUG_vc_5_ok|].
  apply Forall_cons; [exact SLOWUG_vc_6_ok|].
  apply Forall_cons; [exact SLOWUG_vc_7_ok|].
  apply Forall_cons; [exact SLOWUG_vc_8_ok|].
  apply Forall_cons; [exact SLOWUG_vc_9_ok|].
  apply Forall_cons; [exact SLOWUG_vc_10_ok|].
  apply Forall_cons; [exact SLOWUG_vc_11_ok|].
  apply Forall_cons; [exact SLOWUG_vc_12_ok|].
  apply Forall_cons; [exact SLOWUG_vc_13_ok|].
  apply Forall_cons; [exact SLOWUG_vc_14_ok|].
  apply Forall_cons; [exact SLOWUG_vc_15_ok|].
  apply Forall_cons; [exact SLOWUG_vc_16_ok|].
  apply Forall_cons; [exact SLOWUG_vc_17_ok|].
  apply Forall_cons; [exact SLOWUG_vc_18_ok|].
  apply Forall_cons; [exact SLOWUG_vc_19_ok|].
  apply Forall_cons; [exact SLOWUG_vc_20_ok|].
  apply Forall_cons; [exact SLOWUG_vc_21_ok|].
  apply Forall_cons; [exact SLOWUG_vc_22_ok|].
  apply Forall_cons; [exact SLOWUG_vc_23_ok|].
  apply Forall_cons; [exact SLOWUG_vc_24_ok|].
  apply Forall_cons; [exact SLOWUG_vc_25_ok|].
  apply Forall_cons; [exact SLOWUG_vc_26_ok|].
  apply Forall_cons; [exact SLOWUG_vc_27_ok|].
  apply Forall_cons; [exact SLOWUG_vc_28_ok|].
  apply Forall_cons; [exact SLOWUG_vc_29_ok|].
  apply Forall_cons; [exact SLOWUG_vc_30_ok|].
  apply Forall_cons; [exact SLOWUG_vc_31_ok|].
  apply Forall_cons; [exact SLOWUG_vc_32_ok|].
  apply Forall_cons; [exact SLOWUG_vc_33_ok|].
  apply Forall_cons; [exact SLOWUG_vc_34_ok|].
  apply Forall_cons; [exact SLOWUG_vc_35_ok|].
  apply Forall_cons; [exact SLOWUG_vc_36_ok|].
  apply Forall_cons; [exact SLOWUG_vc_37_ok|].
  apply Forall_cons; [exact SLOWUG_vc_38_ok|].
  apply Forall_cons; [exact SLOWUG_vc_39_ok|].
  apply Forall_cons; [exact SLOWUG_vc_40_ok|].
  apply Forall_cons; [exact SLOWUG_vc_41_ok|].
  apply Forall_cons; [exact SLOWUG_vc_42_ok|].
  apply Forall_cons; [exact SLOWUG_vc_43_ok|].
  apply Forall_cons; [exact SLOWUG_vc_44_ok|].
  apply Forall_cons; [exact SLOWUG_vc_45_ok|].
  apply Forall_cons; [exact SLOWUG_vc_46_ok|].
  apply Forall_cons; [exact SLOWUG_vc_47_ok|].
  apply Forall_cons; [exact SLOWUG_vc_48_ok|].
  apply Forall_cons; [exact SLOWUG_vc_49_ok|].
  apply Forall_cons; [exact SLOWUG_vc_50_ok|].
  apply Forall_cons; [exact SLOWUG_vc_51_ok|].
  apply Forall_cons; [exact SLOWUG_vc_52_ok|].
  apply Forall_cons; [exact SLOWUG_vc_53_ok|].
  apply Forall_cons; [exact SLOWUG_vc_54_ok|].
  apply Forall_cons; [exact SLOWUG_vc_55_ok|].
  apply Forall_cons; [exact SLOWUG_vc_56_ok|].
  apply Forall_cons; [exact SLOWUG_vc_57_ok|].
  apply Forall_cons; [exact SLOWUG_vc_58_ok|].
  apply Forall_cons; [exact SLOWUG_vc_59_ok|].
  apply Forall_cons; [exact SLOWUG_vc_60_ok|].
  apply Forall_cons; [exact SLOWUG_vc_61_ok|].
  apply Forall_cons; [exact SLOWUG_vc_62_ok|].
  apply Forall_cons; [exact SLOWUG_vc_63_ok|].
  apply Forall_cons; [exact SLOWUG_vc_64_ok|].
  apply Forall_cons; [exact SLOWUG_vc_65_ok|].
  apply Forall_nil.
Qed.
