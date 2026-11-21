(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to libreac/fuzz_knock by a Theorem Labs lane from proofs/cgif/cgif_file_fuzzer/lib/A/AB01.v at theorem-labs/oss-verify-proofs@6b32741d849a; module paths renamed; the 50 hand-off states are fuzz_knock.asan's own start-up run *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v; the plan's fresh variables renumbered as the run reads them; the computations of this unit's A/AB01r.v at CONFIG_RSEQ flag 1 (AB01r0.v holds flag 0); the definitions are AB01rb.v's and AB01r.v joins them. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_knock.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AB12 AB1h AB1l AB05.
Import ListNotations.
Import AX2. Import APG.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AB01rb.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL 1 JS_1.
