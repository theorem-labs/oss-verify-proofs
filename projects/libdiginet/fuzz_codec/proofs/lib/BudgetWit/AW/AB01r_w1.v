(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_codec's asan image from the start-up collector (tools/startup, both-arms ColA d198e5a14160) run in the donor workspace with fuzz_codec's image, relocated plan (itabranges whole .text; probe-measured tail 41 x XMemset) and table; the pass-2 collector log, sha256 f163ffd6f97b *)
(* Modified by Theorem Labs, 2026-11: made from A/AB01r.v's computation for the ASan run at the 16 GiB limit (lib/BudgetWit/AW, with the modules it imports from that set renamed to their twins, suffix _w), for LPS 727298f3, in place of the recorded hand-off states of AB01_w.v and the recorded join state of AB03_w.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag (split per flag as plugin-hostd/fuzz_command's A/AB01rb.v, AB01r0.v and AB01r1.v), with BudgetWit/AW/PlanRegen_w.v (the hand-off states collected in one run of the check), the plan's variables renumbered by values read from probes of this unit's run. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libdiginet.fuzz_codec.images Require Import Asan.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AB12.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.BudgetWit.AW Require Import AB01r_wb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL_arms 1 JS_1.
