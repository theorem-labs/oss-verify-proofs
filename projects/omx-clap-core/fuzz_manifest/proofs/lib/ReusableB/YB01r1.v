(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB01.v (donor image sha256 1c29845fe605), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: regenerated for fuzz_manifest.asan-ubsan: the 50 hand-off states of a Theorem Labs lane's collector pass 2 on this image (both mmap arms, no fill) *)
(* Modified by Theorem Labs, 2026-11: made from libreac/fuzz_boxreg's B/AB01r.v for LPS 727298f3, with its module paths changed: the computations of this unit's ReusableB/YB01r.v at CONFIG_RSEQ flag 1 (ReusableB/YB01r0.v holds flag 0), the band join state and the hand-off states computed in the build from the start-up run by check, the hand-off states collected arm by arm in one run of the check each (ReusableB/YB01rb.v; the layout of plugin-hostd/fuzz_command's B/YB01r1.v). *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB12 YB1h YB1l YB05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB01rb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL_arms 1 JS_1.
