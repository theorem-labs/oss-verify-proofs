(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the 50 hand-off states of reac-repacer/fuzz_wire's ASan build (fuzz_wire.asan sha256 2f8f8697cd4f), collected by the start-up collector from cgif_file_fuzzer's plan relocated to that image (itabranges whole .text; 0 asan_globals descriptors: plantail drop-registration and drop-nodes of the 30 StackDepot stores at UnwindFast+0xac) *)
(* Modified by Theorem Labs, 2026-11: made in place of AB01.v's recorded hand-off states and AB03.v's recorded join state for LPS 727298f3: both computed in the build from the start-up run by the certificate's own check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v, the plan's fresh variables renumbered by a map read from this unit's own start-up probe; shape of libreac/fuzz_boxreg's A/AB01r.v; then split per CONFIG_RSEQ flag as plugin-hostd/fuzz_command's A/AB01rb.v, AB01r0.v and AB01r1.v (the hand-off states collected arm by arm of the continuation's first case split; the hand-off states collected in one run of the check), after reac-pw/fuzz_role's copy. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 0. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_repacer.fuzz_wire.images Require Import Asan.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB12 AB1h AB1l AB05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB01rb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
