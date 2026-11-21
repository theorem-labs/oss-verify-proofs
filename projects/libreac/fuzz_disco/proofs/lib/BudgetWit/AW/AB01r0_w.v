(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AB01.v, with its module paths changed; its 50 hand-off states generated from libreac/fuzz_disco's ASan build by a Theorem Labs lane's start-up collector. *)
(* Modified by Theorem Labs, 2026-11: the computations of this unit's A/AB01r.v at CONFIG_RSEQ flag 0 (A/AB01r1.v holds flag 1): the band join state and the hand-off states, collected arm by arm (A/AB01rb.v), each arm's in one run of the check; the layout of plugin-hostd/fuzz_command's A/AB01r0.v and A/AB01r1.v. *)
(* Modified by Theorem Labs, 2026-11: the computations of this unit's BudgetWit/AW/AB01r_w.v at CONFIG_RSEQ flag 0 (BudgetWit/AW/AB01r1_w.v holds flag 1): the band join state and the hand-off states, collected arm by arm (BudgetWit/AW/AB01rb_w.v), each arm's in one run of the check; the layout of plugin-hostd/fuzz_command's A/AB01r0.v and A/AB01r1.v; taken from projects/libreac/fuzz_disco/proofs/lib/A/AB01r0.v, lines 7-8, 11-12 and 16-21, as in the LPS 727298f3 update. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 0. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_disco.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0c YK09 YA01. From OSSVerify.Proofs.libreac.fuzz_disco.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB12. From OSSVerify.Proofs.libreac.fuzz_disco.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
Import ListNotations. Import AX2. Import APG.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.BudgetWit.AW Require Import AB01rb_w.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
