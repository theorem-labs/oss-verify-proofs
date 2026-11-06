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

Lemma SLOWAG1_vc_5_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_5.
Proof. unfold SLOWAG1_vc_5. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_11_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_11.
Proof. unfold SLOWAG1_vc_11. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_17_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_17.
Proof. unfold SLOWAG1_vc_17. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_23_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_23.
Proof. unfold SLOWAG1_vc_23. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_29_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_29.
Proof. unfold SLOWAG1_vc_29. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_35_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_35.
Proof. unfold SLOWAG1_vc_35. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_41_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_41.
Proof. unfold SLOWAG1_vc_41. SNVA.sna_auto. Qed.
