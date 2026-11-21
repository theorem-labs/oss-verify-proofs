(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: generated for reac-repacer/fuzz_uci's asan image from the start-up collector (tools/startup, both-arms ColA d198e5a14160) run in the donor workspace with fuzz_uci's image, relocated plan (itabranges whole .text; probe-measured tail 2 x XMemset) and table; the pass-2 collector log, sha256 70c3f021088b *)
(* Modified by Theorem Labs, 2026-11: made from A/AB01r0.v (its computations at CONFIG_RSEQ flag 0; A/AB01r.v computes, in place of the recorded hand-off states of AB01_w.v and the recorded band join state of AB03_w.v, both from the start-up run by check, per CONFIG_RSEQ flag) for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 0. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_repacer.fuzz_uci.images Require Import Asan.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB12.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.BudgetWit.AW Require Import AB01rb_w.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
