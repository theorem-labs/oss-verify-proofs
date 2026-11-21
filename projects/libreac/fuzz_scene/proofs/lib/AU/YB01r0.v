(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the computations of this unit's AU/YB01r.v at CONFIG_RSEQ flag 0 (AU/YB01r1.v holds flag 1), with the hand-off states collected arm by arm (AU/YB01rb.v); the layout of plugin-hostd/fuzz_command's A/AB01r0.v and A/AB01r1.v. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 0. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_scene.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YB12 YB1h YB1l YB05.
Import ListNotations.
Import AX2. Import APG.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YB01rb.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
