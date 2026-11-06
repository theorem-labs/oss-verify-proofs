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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWVA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWAB_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWAB_vcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Lemma SLOWAG1_vc_0_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_0.
Proof. unfold SLOWAG1_vc_0. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_6_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_6.
Proof. unfold SLOWAG1_vc_6. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_12_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_12.
Proof. unfold SLOWAG1_vc_12. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_18_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_18.
Proof. unfold SLOWAG1_vc_18. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_24_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_24.
Proof. unfold SLOWAG1_vc_24. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_30_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_30.
Proof. unfold SLOWAG1_vc_30. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_36_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_36.
Proof. unfold SLOWAG1_vc_36. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_42_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_42.
Proof. unfold SLOWAG1_vc_42. SNVA.sna_auto. Qed.
