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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBB_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWBB_vcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Lemma SLOWBG1_vc_11_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWBG1_vc_11.
Proof. unfold SLOWBG1_vc_11. SNVA.sna_auto. Qed.
Lemma SLOWBG1_vc_3_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWBG1_vc_3.
Proof. unfold SLOWBG1_vc_3. SNVA.sna_auto. Qed.
Lemma SLOWBG1_vc_26_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWBG1_vc_26.
Proof. unfold SLOWBG1_vc_26. SNVA.sna_auto. Qed.
Lemma SLOWBG1_vc_4_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWBG1_vc_4.
Proof. unfold SLOWBG1_vc_4. SNVA.sna_auto. Qed.
Lemma SLOWBG1_vc_27_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWBG1_vc_27.
Proof. unfold SLOWBG1_vc_27. SNVA.sna_auto. Qed.
Lemma SLOWBG1_vc_31_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWBG1_vc_31.
Proof. unfold SLOWBG1_vc_31. SNVA.sna_auto. Qed.
Lemma SLOWBG1_vc_20_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWBG1_vc_20.
Proof. unfold SLOWBG1_vc_20. SNVA.sna_auto. Qed.
Lemma SLOWBG1_vc_21_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWBG1_vc_21.
Proof. unfold SLOWBG1_vc_21. SNVA.sna_auto. Qed.
Lemma SLOWBG1_vc_25_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWBG1_vc_25.
Proof. unfold SLOWBG1_vc_25. SNVA.sna_auto. Qed.
Lemma SLOWBG1_vc_9_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWBG1_vc_9.
Proof. unfold SLOWBG1_vc_9. SNVA.sna_auto. Qed.
Lemma SLOWBG1_vc_1_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWBG1_vc_1.
Proof. unfold SLOWBG1_vc_1. SNVA.sna_auto. Qed.
