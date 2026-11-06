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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWABN_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWABN_vcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Lemma SLOWAGN_vc_1_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAGN_vc_1.
Proof. unfold SLOWAGN_vc_1. SNVB.snb_solve. Qed.
Lemma SLOWAGN_vc_5_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAGN_vc_5.
Proof. unfold SLOWAGN_vc_5. SNVA.sna_auto. Qed.
Lemma SLOWAGN_vc_10_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAGN_vc_10.
Proof. unfold SLOWAGN_vc_10. SNVA.sna_auto. Qed.
Lemma SLOWAGN_vc_12_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAGN_vc_12.
Proof. unfold SLOWAGN_vc_12. SNVA.sna_auto. Qed.
Lemma SLOWAGN_vc_14_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAGN_vc_14.
Proof. unfold SLOWAGN_vc_14. SNVA.sna_auto. Qed.
Lemma SLOWAGN_vc_16_ok : SG.vc_holds SG (SNG.sng_gp SG) SLOWAGN_vc_16.
Proof. unfold SLOWAGN_vc_16. SNVA.sna_auto. Qed.
