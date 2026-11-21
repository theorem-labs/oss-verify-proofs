(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: regenerated for fuzz_manifest.asan: every one of the 50 hand-off states is the state the plan checker's own executor reaches at that hole on fuzz_manifest.asan (the start-up collector walks both arms of every mmap node; the checker itself reaches holes 0 1 8 9 16 17 24 25 32 36), read off and printed. *)
(* Modified by Theorem Labs, 2026-11: made from libreac/fuzz_boxreg's A/AB01r.v for LPS 727298f3, with its module paths changed: the computations of this unit's A/AB01r.v at CONFIG_RSEQ flag 1 (A/AB01r0.v holds flag 0), the band join state and the hand-off states computed in the build from the start-up run by check, the hand-off states collected arm by arm in one run of the check each (A/AB01rb.v; the layout of plugin-hostd/fuzz_command's A/AB01r1.v). *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB12 AB1h AB1l AB05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB01rb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL_arms 1 JS_1.
