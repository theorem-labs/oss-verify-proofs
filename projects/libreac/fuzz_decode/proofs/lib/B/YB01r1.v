(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v; the shape of A/AB01r.v; made for libreac/fuzz_decode's image-B library from libreac/fuzz_boxreg's B/AB01r.v: this unit's module paths and YB names, and the plan's variables renumbered by a map read from this unit's probes; split per CONFIG_RSEQ flag (YB01rb.v definitions, YB01r0.v and YB01r1.v one flag each, YB01r.v joining them under the same names), the layout of plugin-hostd/fuzz_command's A/AB01r.v; the hand-off states collected in one run of the check (reac-pw/fuzz_headamp's collect_handoffs1). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_decode.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0c. From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB12 YB1h YB1l YB05.
Import ListNotations. Import AX2. Import APG.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB01rb.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL 1 JS_1.
