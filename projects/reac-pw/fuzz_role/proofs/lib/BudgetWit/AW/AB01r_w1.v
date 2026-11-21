(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: the 50 hand-off states (and the pass-1 join state) are fuzz_role.asan's own, collected by the start-up collector (coq/ColA.v d198e5a14160, hsform.py eb5d13059ca8) running the donor checker of proofs/cgif/cgif_file_fuzzer on this image with the plan probed for it (tail XMemset*50); header and Requires from proofs/cgif/cgif_file_fuzzer/lib/A with module paths changed *)
(* Modified by Theorem Labs, 2026-11: made from A/AB01.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w); then made for LPS 727298f3 in place of the recorded hand-off states of AB01_w.v and the recorded join state of AB03_w.v: both computed in the build from the start-up run at the 16 GiB limit by check, per CONFIG_RSEQ flag (split as plugin-hostd/fuzz_command's A/AB01rb.v, AB01r0.v and AB01r1.v), with BudgetWit/AW/PlanRegen_w.v (as A/AB01r.v; the hand-off states collected in one run of the check), the plan's fresh variables renumbered by values read from probes of fuzz_role.asan's run at the 16 GiB limit. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_role.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import AB12.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.BudgetWit.AW Require Import AB01r_wb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL_arms 1 JS_1.
