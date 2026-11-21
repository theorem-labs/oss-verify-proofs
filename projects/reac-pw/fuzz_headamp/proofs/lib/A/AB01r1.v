(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AB01.v; the 50 hand-off states are fuzz_headamp.asan's own, collected by the start-up collector (coq/ColA.v) running that donor's checker on this image with the plan probed for it (tail XMemset*44); module paths changed *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v (the shape of libreac/fuzz_boxreg's A/AB01r.v), the plan's fresh variables renumbered by values read from a probe of fuzz_headamp.asan's run. Split per CONFIG_RSEQ flag as plugin-hostd/fuzz_command's A/AB01rb.v, AB01r0.v and AB01r1.v (via reac-pw/fuzz_role's): the hand-off states are collected arm by arm of the continuation's first case split, in AB01r0.v and AB01r1.v compiled in parallel; the hand-off states collected in one run of the check. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_headamp.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import AB12 AB1h AB1l AB05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import AB01rb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL_arms 1 JS_1.
