(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_num_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import F_memset Sj_kit Sj_num_iface Sj_num_kitu Sj_num_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma numu_memcpy_closed : memcpyZ_stmt_g usegs 0xd5a30.
Proof. unfold memcpyZ_stmt_g. intros. eapply evt_mono; [eapply Sj_kit.memcpy_callZ; eassumption|]. intros ms' P. exact P. Qed.
Lemma numu_memset_closed : memsetZ_stmt_g usegs 0xd5fb0.
Proof. unfold memsetZ_stmt_g. intros. eapply evt_mono; [eapply F_memset.memset_callZ; eassumption|]. intros ms' P. exact P. Qed.

Theorem slowfu_closed : slowfu_stmt_g usegs 0x62060 0x117000.
Proof. exact (numu_slowf numu_memcpy_closed numu_memset_closed). Qed.
Theorem pffu_closed : pffu_stmt_g usegs 0x62110 0x117000.
Proof. exact (numu_pff numu_memcpy_closed numu_memset_closed). Qed.

Print Assumptions slowfu_closed.
