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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SWARZ.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWV.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWVA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWVB.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBBF_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBBF_vcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_0.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_1.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_4.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_5.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_6.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_7.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_8.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_9.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_10.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_11.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_12.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_13.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_14.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_15.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGF_vcok_16.

Lemma SLOWBGF_GV_ok : Forall (SG.vc_holds SG (SNG.sng_gp SG)) SLOWBGF_GV.
Proof.
  unfold SLOWBGF_GV.
  apply Forall_cons; [exact SLOWBGF_vc_0_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_1_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_2_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_3_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_4_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_5_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_6_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_7_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_8_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_9_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_10_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_11_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_12_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_13_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_14_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_15_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_16_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_17_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_18_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_19_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_20_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_21_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_22_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_23_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_24_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_25_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_26_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_28_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_29_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_32_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_35_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_36_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_37_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_38_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_39_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_40_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_42_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_43_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_44_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_45_ok|].
  apply Forall_cons; [exact SLOWBGF_vc_46_ok|].
  apply Forall_nil.
Qed.
