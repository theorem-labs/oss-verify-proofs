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

Lemma SLOWAG1_vc_1_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_1.
Proof. unfold SLOWAG1_vc_1. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_7_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_7.
Proof. unfold SLOWAG1_vc_7. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_13_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_13.
Proof. unfold SLOWAG1_vc_13. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_19_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_19.
Proof. unfold SLOWAG1_vc_19. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_25_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_25.
Proof. unfold SLOWAG1_vc_25. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_31_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_31.
Proof. unfold SLOWAG1_vc_31. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_37_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_37.
Proof. unfold SLOWAG1_vc_37. SNVA.sna_auto. Qed.
Lemma SLOWAG1_vc_43_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAG1_vc_43.
Proof. unfold SLOWAG1_vc_43. SNVA.sna_auto. Qed.
