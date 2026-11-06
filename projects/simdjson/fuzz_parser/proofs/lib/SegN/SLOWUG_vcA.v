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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Import NUMU_D.SLOWU_defs.
(* [comment removed for export] *)

Lemma SLOWUG_vc_0_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_0.
Proof. unfold SLOWUG_vc_0. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_4_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_4.
Proof. unfold SLOWUG_vc_4. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_8_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_8.
Proof. unfold SLOWUG_vc_8. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_12_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_12.
Proof. unfold SLOWUG_vc_12. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_16_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_16.
Proof. unfold SLOWUG_vc_16. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_20_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_20.
Proof. unfold SLOWUG_vc_20. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_24_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_24.
Proof. unfold SLOWUG_vc_24. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_28_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_28.
Proof. unfold SLOWUG_vc_28. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_32_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_32.
Proof. unfold SLOWUG_vc_32. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_36_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_36.
Proof. unfold SLOWUG_vc_36. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_40_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_40.
Proof. unfold SLOWUG_vc_40. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_44_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_44.
Proof. unfold SLOWUG_vc_44. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_48_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_48.
Proof. unfold SLOWUG_vc_48. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_52_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_52.
Proof. unfold SLOWUG_vc_52. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_56_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_56.
Proof. unfold SLOWUG_vc_56. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_60_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_60.
Proof. unfold SLOWUG_vc_60. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_64_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_64.
Proof. unfold SLOWUG_vc_64. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.

Import NUMU_D.SLOWU_defs.
(* [comment removed for export] *)

Lemma SLOWUG_vc_1_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_1.
Proof. unfold SLOWUG_vc_1. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_5_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_5.
Proof. unfold SLOWUG_vc_5. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_9_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_9.
Proof. unfold SLOWUG_vc_9. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_13_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_13.
Proof. unfold SLOWUG_vc_13. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_17_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_17.
Proof. unfold SLOWUG_vc_17. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_21_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_21.
Proof. unfold SLOWUG_vc_21. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_25_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_25.
Proof. unfold SLOWUG_vc_25. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_29_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_29.
Proof. unfold SLOWUG_vc_29. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_33_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_33.
Proof. unfold SLOWUG_vc_33. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_37_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_37.
Proof. unfold SLOWUG_vc_37. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_41_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_41.
Proof. unfold SLOWUG_vc_41. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_45_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_45.
Proof. unfold SLOWUG_vc_45. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_49_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_49.
Proof. unfold SLOWUG_vc_49. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_53_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_53.
Proof. unfold SLOWUG_vc_53. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_57_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_57.
Proof. unfold SLOWUG_vc_57. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_61_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_61.
Proof. unfold SLOWUG_vc_61. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
Lemma SLOWUG_vc_65_ok : SG.vc_holds SG (SNU.snu_gp SG) SLOWUG_vc_65.
Proof. unfold SLOWUG_vc_65. first [SNV.sn_solve | NRV.nv_flags | NRV.nv_solve]. Qed.
