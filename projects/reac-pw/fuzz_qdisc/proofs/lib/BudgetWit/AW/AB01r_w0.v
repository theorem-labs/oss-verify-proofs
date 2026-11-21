(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the 50 hand-off states (and the pass-1 join state) are fuzz_qdisc.asan's own, collected by port-reply's start-up collector (tools/startup, set startup-set-2026-10-29) running the donor checker on this image with the plan probed for it (tail XMemset*2); header and Requires from proofs/libreac/fuzz_knock/lib/A (h-small-a3) *)
(* Modified by Theorem Labs, 2026-11: made from A/AB01.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w); then split per CONFIG_RSEQ flag as plugin-hostd/fuzz_command's BudgetWit/AW/AB01r_wb.v, AB01r_w0.v and AB01r_w1.v (the hand-off states collected arm by arm of the continuation's first case split), from reac-pw/fuzz_role's copy; internal commit ids in comments replaced by public commits or removed. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_qdisc.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AB12.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.BudgetWit.AW Require Import AB01r_wb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
