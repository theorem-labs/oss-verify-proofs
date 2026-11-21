(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: generated for reac-repacer/fuzz_uci's asan image from the start-up collector (tools/startup, both-arms ColA d198e5a14160) run in the donor workspace with fuzz_uci's image, relocated plan (itabranges whole .text; probe-measured tail 2 x XMemset) and table; the pass-2 collector log, sha256 70c3f021088b *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of this unit's recorded hand-off states (AB01.v): the computations of A/AB01r.v at CONFIG_RSEQ flag 1 (A/AB01r0.v holds flag 0), with the hand-off states collected arm by arm (A/AB01rb.v), as plugin-hostd/fuzz_command's A/AB01r1.v. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_repacer.fuzz_uci.images Require Import Asan.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB12 AB1h AB1l AB05.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB01rb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL_arms 1 JS_1.
