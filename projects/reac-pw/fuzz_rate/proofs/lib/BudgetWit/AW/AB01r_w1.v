(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the 50 hand-off states (and the pass-1 join state) are fuzz_rate.asan's own, collected by the start-up collector (coq/ColA.v d198e5a14160, hsform.py 9747a6731b7e) running the donor checker of proofs/cgif/cgif_file_fuzzer on this image with the plan probed for it (tail XMemset*58); header and Requires from proofs/cgif/cgif_file_fuzzer/lib/A with module paths changed *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states and band join state of AB01_w.v and AB03_w.v: both computed in the build from the start-up run by the certificate's own check, per CONFIG_RSEQ flag, with BudgetWit/AW/PlanRegen_w.v, the plan's variables renumbered by a map read from this unit's own probe; split per flag (definitions, flag 0, flag 1, joined) as reac-pw/fuzz_role's copy of plugin-hostd/fuzz_command's AB01rb.v, AB01r0.v, AB01r1.v and AB01r.v; internal commit ids in comments replaced by public commits or removed. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_rate.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import AB12.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.BudgetWit.AW Require Import AB01r_wb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL_arms 1 JS_1.
