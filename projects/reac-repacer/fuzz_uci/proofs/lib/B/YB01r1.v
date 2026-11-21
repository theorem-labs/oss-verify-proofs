(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs: generated for reac-repacer/fuzz_uci image B (asan-ubsan) from its own collector run (pass 2, provenance/startup-gen/B/logs/pass2.B.log: 220 leaves = 50 hand-offs at main 0x7ee48 + 168 spins + 2 merges, 0 failure leaves) on the pinned fuzz_uci.asan-ubsan (sha256 a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc); the donor file's form, this image's states. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of this unit's recorded hand-off states (YB01.v): the computations of B/YB01r.v at CONFIG_RSEQ flag 1 (B/YB01r0.v holds flag 0), with the hand-off states collected arm by arm (B/YB01rb.v), as plugin-hostd/fuzz_command's B/YB01r1.v; internal commit ids in comments replaced by public commits or removed. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_repacer.fuzz_uci.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB12 YB1h YB1l YB05.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB01rb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL_arms 1 JS_1.
