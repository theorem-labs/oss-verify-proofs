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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Import NUMP_D.SLOW_defs.
(* [comment removed for export] *)

Lemma SLOWG_vc_0_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_0.
Proof. unfold SLOWG_vc_0. SNV.sn_solve. Qed.
Lemma SLOWG_vc_8_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_8.
Proof. unfold SLOWG_vc_8. SNV.sn_solve. Qed.
Lemma SLOWG_vc_16_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_16.
Proof. unfold SLOWG_vc_16. SNV.sn_solve. Qed.
Lemma SLOWG_vc_24_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_24.
Proof. unfold SLOWG_vc_24. SNV.sn_solve. Qed.
Lemma SLOWG_vc_32_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_32.
Proof. unfold SLOWG_vc_32. SNV.sn_solve. Qed.
Lemma SLOWG_vc_40_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_40.
Proof. unfold SLOWG_vc_40. SNV.sn_solve. Qed.
Lemma SLOWG_vc_48_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_48.
Proof. unfold SLOWG_vc_48. SNV.sn_solve. Qed.

Import NUMP_D.SLOW_defs.
(* [comment removed for export] *)

Lemma SLOWG_vc_1_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_1.
Proof. unfold SLOWG_vc_1. SNV.sn_solve. Qed.
Lemma SLOWG_vc_9_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_9.
Proof. unfold SLOWG_vc_9. SNV.sn_solve. Qed.
Lemma SLOWG_vc_17_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_17.
Proof. unfold SLOWG_vc_17. SNV.sn_solve. Qed.
Lemma SLOWG_vc_25_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_25.
Proof. unfold SLOWG_vc_25. SNV.sn_solve. Qed.
Lemma SLOWG_vc_33_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_33.
Proof. unfold SLOWG_vc_33. SNV.sn_solve. Qed.
Lemma SLOWG_vc_41_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_41.
Proof. unfold SLOWG_vc_41. SNV.sn_solve. Qed.
Lemma SLOWG_vc_49_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_49.
Proof. unfold SLOWG_vc_49. SNV.sn_solve. Qed.

Import NUMP_D.SLOW_defs.
(* [comment removed for export] *)

Lemma SLOWG_vc_2_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_2.
Proof. unfold SLOWG_vc_2. SNV.sn_solve. Qed.
Lemma SLOWG_vc_10_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_10.
Proof. unfold SLOWG_vc_10. SNV.sn_solve. Qed.
Lemma SLOWG_vc_18_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_18.
Proof. unfold SLOWG_vc_18. SNV.sn_solve. Qed.
Lemma SLOWG_vc_26_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_26.
Proof. unfold SLOWG_vc_26. SNV.sn_solve. Qed.
Lemma SLOWG_vc_34_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_34.
Proof. unfold SLOWG_vc_34. SNV.sn_solve. Qed.
Lemma SLOWG_vc_42_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_42.
Proof. unfold SLOWG_vc_42. SNV.sn_solve. Qed.
Lemma SLOWG_vc_50_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_50.
Proof. unfold SLOWG_vc_50. SNV.sn_solve. Qed.

Import NUMP_D.SLOW_defs.
(* [comment removed for export] *)

Lemma SLOWG_vc_3_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_3.
Proof. unfold SLOWG_vc_3. SNV.sn_solve. Qed.
Lemma SLOWG_vc_11_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_11.
Proof. unfold SLOWG_vc_11. SNV.sn_solve. Qed.
Lemma SLOWG_vc_19_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_19.
Proof. unfold SLOWG_vc_19. SNV.sn_solve. Qed.
Lemma SLOWG_vc_27_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_27.
Proof. unfold SLOWG_vc_27. SNV.sn_solve. Qed.
Lemma SLOWG_vc_35_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_35.
Proof. unfold SLOWG_vc_35. SNV.sn_solve. Qed.
Lemma SLOWG_vc_43_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_43.
Proof. unfold SLOWG_vc_43. SNV.sn_solve. Qed.
Lemma SLOWG_vc_51_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWG_vc_51.
Proof. unfold SLOWG_vc_51. SNV.sn_solve. Qed.
