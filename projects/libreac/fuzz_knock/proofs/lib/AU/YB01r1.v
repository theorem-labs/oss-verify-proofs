(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported to libreac/fuzz_knock by a Theorem Labs lane from proofs/cgif/cgif_file_fuzzer/lib/YB01.v at theorem-labs/oss-verify-proofs@6b32741d849a; module paths renamed; the 50 hand-off states are fuzz_knock.asan-ubsan's own start-up run *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of YB01.v and the recorded join state of YB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v; the plan's fresh variables renumbered as the run reads them; the computations of this unit's AU/YB01r.v at CONFIG_RSEQ flag 1 (YB01r0.v holds flag 0); the definitions are YB01rb.v's and YB01r.v joins them. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_knock.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YB12 YB1h YB1l YB05.
Import ListNotations.
Import AX2. Import APG.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YB01rb.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL 1 JS_1.
