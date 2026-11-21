(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v; the shape of cgif/cgif_file_fuzzer's A/AB01r.v in this working copy; made for libreac/fuzz_decode from libreac/fuzz_boxreg's A/AB01r.v: this unit's module paths, and the plan's variables renumbered by a map read from this unit's probes; split per CONFIG_RSEQ flag (AB01rb.v definitions, AB01r0.v and AB01r1.v one flag each, AB01r.v joining them under the same names), the layout of plugin-hostd/fuzz_command's A/AB01r.v; the hand-off states collected in one run of the check (reac-pw/fuzz_headamp's collect_handoffs1). *)
(* Modified by Theorem Labs, 2026-11: made for the ASan run at the 16 GiB limit (lib/BudgetWit/AW) from this unit's A/AB01r.v, in place of AB01_w.v and AB03_w.v, with the modules it imports from that set renamed to their twins; split per CONFIG_RSEQ flag (AB01rb_w.v definitions, AB01r0_w.v and AB01r1_w.v one flag each, AB01r_w.v joining them under the same names), the layout of plugin-hostd/fuzz_command's A/AB01r.v; the hand-off states collected in one run of the check (reac-pw/fuzz_headamp's collect_handoffs1); taken from projects/libreac/fuzz_decode/proofs/lib/A/AB01r1.v, lines 4-9 and 13-18, as in the LPS 727298f3 update. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_decode.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AB12.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
Import ListNotations. Import AX2. Import APG.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.BudgetWit.AW Require Import AB01rb_w.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL 1 JS_1.
