(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AB01.v, with its module paths changed; its 50 hand-off states generated from libreac/fuzz_disco's ASan build by a Theorem Labs lane's start-up collector. *)
(* Modified by Theorem Labs, 2026-11: the computations of this unit's A/AB01r.v at CONFIG_RSEQ flag 1 (A/AB01r0.v holds flag 0): the band join state and the hand-off states, collected arm by arm (A/AB01rb.v), each arm's in one run of the check; the layout of plugin-hostd/fuzz_command's A/AB01r0.v and A/AB01r1.v. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_disco.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB12 AB1h AB1l AB05.
Import ListNotations. Import AX2. Import APG.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB01rb.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL_arms 1 JS_1.
