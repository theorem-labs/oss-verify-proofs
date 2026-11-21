(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: the 50 hand-off states are fuzz_pin.asan's own, collected by the start-up collector of tools/startup (the start-up tool set at tools, hsform.py eb5d13059ca8) running the donor checker of proofs/cgif/cgif_file_fuzzer on this image with the plan probed for it (lib/A/AB05.v: tail XMemset*23, PMmap, XMemset*2); 0 filled holes; header and Requires from proofs/cgif/cgif_file_fuzzer/lib/A/AB01.v, module paths changed to this unit's lib/Reusable *)
(* Modified by Theorem Labs, 2026-11: made from A/AB01.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w); then made for LPS 727298f3 in place of the recorded hand-off states of AB01_w.v and the recorded join state of AB03_w.v: both computed in the build from the start-up run at the 16 GiB limit by check, per CONFIG_RSEQ flag, with BudgetWit/AW/PlanRegen_w.v, split per flag (AB01r_wb.v definitions, AB01r_w0.v and AB01r_w1.v, joined in AB01r_w.v) as A/AB01r*.v; the hand-off states collected in one run of the check; the plan's variables renumbered by values read from probes of that run; internal commit ids in comments replaced by public commits or removed. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_pin.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AB12.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import AB01r_wb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
