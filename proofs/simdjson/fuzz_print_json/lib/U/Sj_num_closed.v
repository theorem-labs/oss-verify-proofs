(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import F_memset Sj_kit Sj_num_iface Sj_num_kitu Sj_num_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma numu_memcpy_closed : memcpyZ_stmt_g usegs 0xcfe78.
Proof. unfold memcpyZ_stmt_g. intros. eapply evt_mono; [eapply Sj_kit.memcpy_callZ; eassumption|]. intros ms' P. exact P. Qed.
Lemma numu_memset_closed : memsetZ_stmt_g usegs 0xd03f8.
Proof. unfold memsetZ_stmt_g. intros. eapply evt_mono; [eapply F_memset.memset_callZ; eassumption|]. intros ms' P. exact P. Qed.

Theorem slowfu_closed : slowfu_stmt_g usegs 0x5f104 0x110000.
Proof. exact (numu_slowf numu_memcpy_closed numu_memset_closed). Qed.
Theorem pffu_closed : pffu_stmt_g usegs 0x5f1b4 0x110000.
Proof. exact (numu_pff numu_memcpy_closed numu_memset_closed). Qed.

Print Assumptions slowfu_closed.
