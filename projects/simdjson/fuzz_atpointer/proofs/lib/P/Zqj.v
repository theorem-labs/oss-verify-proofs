(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z9p Sj_kit Zso Zsl Zvl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma num_memcpy_closed : memcpyZ_stmt_g psegs 0x71d00.
Proof. unfold memcpyZ_stmt_g. intros. eapply evt_mono; [eapply Sj_kit.memcpy_callZ; eassumption|]. intros ms' P. exact P. Qed.

Lemma num_memset_closed : memsetZ_stmt_g psegs 0x72280.
Proof. unfold memsetZ_stmt_g. intros. eapply evt_mono; [eapply Z9p.memset_callZ; eassumption|]. intros ms' P. exact P. Qed.

Theorem slowf_closed : slowf_stmt_g psegs 0x3cb88 0xab000.
Proof. exact (num_slowf num_memcpy_closed num_memset_closed). Qed.

Theorem pff_closed : pff_stmt_g psegs 0x3cc10 0xab000.
Proof. exact (num_pff num_memcpy_closed num_memset_closed). Qed.

Print Assumptions slowf_closed.
Print Assumptions pff_closed.
