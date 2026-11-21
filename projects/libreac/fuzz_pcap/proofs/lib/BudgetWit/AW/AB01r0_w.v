(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v, from libreac/fuzz_boxreg's A/AB01r.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v, the plan's fresh variables renumbered by a map read from this unit's probes; its definitions are in A/AB01rb.v and its computations in A/AB01r0.v and A/AB01r1.v, one per flag, put together here under the names the rest of the unit reads (the layout of plugin-hostd/fuzz_command's A/AB01r.v). *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 at the 16 GiB limit (lib/BudgetWit/AW, the modules it imports from that set renamed to their twins, suffix _w) in place of the recorded hand-off states of AB01_w.v and the recorded join state of AB03_w.v: their computation in the build from the start-up run at CONFIG_RSEQ flag 0 (BudgetWit/AW/AB01r1_w.v holds flag 1) from the definitions of BudgetWit/AW/AB01rb_w.v, the hand-off states collected arm by arm (the layout of plugin-hostd/fuzz_command's A/AB01r0.v); taken from projects/libreac/fuzz_pcap/proofs/lib/A/AB01r.v, lines 8-21, as in the LPS 727298f3 update. *)
(* The band join state and the hand-off states of the start-up run at the 16 GiB limit at CONFIG_RSEQ flag 0. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB12.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AB01rb_w.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
