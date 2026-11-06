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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBBN_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBBN_vcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBGN_vcok_0.

Lemma SLOWBGN_GV_ok : Forall (SG.vc_holds SG (SNG.sng_gp SG)) SLOWBGN_GV.
Proof.
  unfold SLOWBGN_GV.
  apply Forall_cons; [exact SLOWBGN_vc_0_ok|].
  apply Forall_cons; [exact SLOWBGN_vc_1_ok|].
  apply Forall_cons; [exact SLOWBGN_vc_3_ok|].
  apply Forall_cons; [exact SLOWBGN_vc_4_ok|].
  apply Forall_cons; [exact SLOWBGN_vc_7_ok|].
  apply Forall_cons; [exact SLOWBGN_vc_10_ok|].
  apply Forall_cons; [exact SLOWBGN_vc_11_ok|].
  apply Forall_cons; [exact SLOWBGN_vc_12_ok|].
  apply Forall_cons; [exact SLOWBGN_vc_13_ok|].
  apply Forall_cons; [exact SLOWBGN_vc_14_ok|].
  apply Forall_cons; [exact SLOWBGN_vc_15_ok|].
  apply Forall_cons; [exact SLOWBGN_vc_16_ok|].
  apply Forall_cons; [exact SLOWBGN_vc_17_ok|].
  apply Forall_nil.
Qed.
