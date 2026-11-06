(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zso.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Z9p Sj_kit Zsl Zsr Zvl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma numu_memcpy_closed : memcpyZ_stmt_g usegs 0x7c3dc.
Proof. unfold memcpyZ_stmt_g. intros. eapply evt_mono; [eapply Sj_kit.memcpy_callZ; eassumption|]. intros ms' P. exact P. Qed.
Lemma numu_memset_closed : memsetZ_stmt_g usegs 0x7c95c.
Proof. unfold memsetZ_stmt_g. intros. eapply evt_mono; [eapply Z9p.memset_callZ; eassumption|]. intros ms' P. exact P. Qed.

Theorem slowfu_closed : slowfu_stmt_g usegs 0x47214 0xb5000.
Proof. exact (numu_slowf numu_memcpy_closed numu_memset_closed). Qed.
Theorem pffu_closed : pffu_stmt_g usegs 0x472c4 0xb5000.
Proof. exact (numu_pff numu_memcpy_closed numu_memset_closed). Qed.

Print Assumptions slowfu_closed.
