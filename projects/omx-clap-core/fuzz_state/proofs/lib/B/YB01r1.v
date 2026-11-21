(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v; the shape of cgif/cgif_file_fuzzer's A/AB01r.v in this working copy; the computations of libreac/fuzz_boxreg's A/AB01r.v for this unit's ASan+UBSan build (lib/B) at CONFIG_RSEQ flag 1 (B/YB01r0.v holds flag 0), with this unit's module paths: the band join state and the hand-off states computed in the build from the start-up run by check, the hand-off states collected arm by arm in one run of the check each (B/YB01rb.v; the layout of plugin-hostd/fuzz_command's B/YB01r1.v). *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB12 YB1h YB1l YB05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB01rb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL_arms 1 JS_1.
