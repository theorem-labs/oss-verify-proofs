(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v; the shape of A/AB01r.v; the computations of this unit's B/YB01r.v at CONFIG_RSEQ flag 0 (B/YB01r1.v holds flag 1), with the hand-off states collected arm by arm (B/YB01rb.v), as plugin-hostd/fuzz_command's B/YB01r0.v. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 0. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB12 YB1h YB1k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YB1j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1l YB05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB01rb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
