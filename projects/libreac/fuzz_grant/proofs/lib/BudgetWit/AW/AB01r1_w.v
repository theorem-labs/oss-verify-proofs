(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB01.v, with its module paths changed; all 50 hand-off states are collected from fuzz_grant.asan's start-up run (a Theorem Labs lane's tools/startup collector, pass 2, both arms of every mmap node). *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from libreac/fuzz_boxreg's A/AB01r.v: the computation at CONFIG_RSEQ flag 1 (A/AB01r0.v holds flag 0) of the band join state and the hand-off states that A/AB01rb.v defines, collected arm by arm in one run of the check per arm, in the per-flag layout of plugin-hostd/fuzz_command's A/AB01r1.v. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from this unit's A/AB01r.v for the ASan run at the 16 GiB limit: the computation at CONFIG_RSEQ flag 1 (BudgetWit/AW/AB01r0_w.v holds flag 0) of the band join state and the hand-off states that BudgetWit/AW/AB01rb_w.v defines, collected arm by arm in one run of the check per arm, in the per-flag layout of plugin-hostd/fuzz_command's A/AB01r1.v; taken from projects/libreac/fuzz_grant/proofs/lib/A/AB01r1.v, lines 7-12 and 16-22, as in the LPS 727298f3 update. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_grant.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0c YK09 YA01. From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import AB12. From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
Import ListNotations.
Import AX2. Import APG.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.BudgetWit.AW Require Import AB01rb_w.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL_arms 1 JS_1.
