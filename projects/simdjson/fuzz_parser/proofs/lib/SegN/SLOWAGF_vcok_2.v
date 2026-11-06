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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWVB.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWABF_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWABF_vcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Lemma SLOWAGF_vc_2_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAGF_vc_2.
Proof. unfold SLOWAGF_vc_2. SNVA.sna_auto. Qed.
Lemma SLOWAGF_vc_7_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAGF_vc_7.
Proof. unfold SLOWAGF_vc_7. SNVA.sna_auto. Qed.
Lemma SLOWAGF_vc_12_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAGF_vc_12.
Proof. unfold SLOWAGF_vc_12. SNVA.sna_auto. Qed.
Lemma SLOWAGF_vc_17_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAGF_vc_17.
Proof. unfold SLOWAGF_vc_17. SNVA.sna_auto. Qed.
Lemma SLOWAGF_vc_24_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAGF_vc_24.
Proof. unfold SLOWAGF_vc_24. SNVA.sna_auto. Qed.
Lemma SLOWAGF_vc_32_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAGF_vc_32.
Proof. unfold SLOWAGF_vc_32. SNVA.sna_auto. Qed.
Lemma SLOWAGF_vc_37_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAGF_vc_37.
Proof. unfold SLOWAGF_vc_37. SNVA.sna_auto. Qed.
