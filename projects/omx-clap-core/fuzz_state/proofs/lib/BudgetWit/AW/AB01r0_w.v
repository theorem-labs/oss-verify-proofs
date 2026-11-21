(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v; the shape of cgif/cgif_file_fuzzer's A/AB01r.v in this working copy; made from A/AB01r0.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w): the computations of BudgetWit/AW/AB01r_w.v at CONFIG_RSEQ flag 0 (AB01r1_w.v holds flag 1), the hand-off states collected arm by arm in one run of the check each (AB01rb_w.v). *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 0, at the
   16 GiB limit. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB12.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.BudgetWit.AW Require Import AB01rb_w.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
