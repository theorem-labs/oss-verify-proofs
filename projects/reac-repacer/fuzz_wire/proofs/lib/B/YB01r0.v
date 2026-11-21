(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-repacer/fuzz_wire image B (asan-ubsan) from its own collector run (pass 2: 70 leaves = 50 hand-offs all at main 0x7f758 + 18 spins + 2 merges, 0 failure leaves; log pass2.B.log, sha256 d7e2ca50de48, not in the published tree) on fuzz_wire.asan-ubsan; the donor file's form, this image's states. *)
(* Modified by Theorem Labs, 2026-11: made in place of YB01.v's recorded hand-off states and YB03.v's recorded join state for LPS 727298f3: both computed in the build from the start-up run by the certificate's own check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v, the plan's fresh variables renumbered by a map read from this unit's own start-up probe; shape of libreac/fuzz_boxreg's B/AB01r.v; then split per CONFIG_RSEQ flag as plugin-hostd/fuzz_command's A/AB01rb.v, AB01r0.v and AB01r1.v (the hand-off states collected arm by arm of the continuation's first case split; the hand-off states collected in one run of the check), after reac-pw/fuzz_role's copy. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 0. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_repacer.fuzz_wire.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB12 YB1h YB1l YB05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB01rb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
