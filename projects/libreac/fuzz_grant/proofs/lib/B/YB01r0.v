(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libreac/fuzz_grant image B (asan-ubsan, sha256 fde52226dc48) by the start-up tool set *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from libreac/fuzz_boxreg's B/AB01r.v: the computation at CONFIG_RSEQ flag 0 (B/YB01r1.v holds flag 1) of the band join state and the hand-off states that B/YB01rb.v defines, collected arm by arm in one run of the check per arm, in the per-flag layout of plugin-hostd/fuzz_command's B/YB01r0.v. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 0. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_grant.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0c. From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YB12 YB1h YB1l YB05.
Import ListNotations.
Import AX2. Import APG.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YB01rb.
Open Scope Z_scope.
Definition CS_VIA_0 : acs := Eval vm_compute in cs_via 0.
Definition JS_0 : acs := Eval vm_compute in js_of 0 CS_VIA_0.
Definition HSL_0 : list (nat * acs) := Eval vm_compute in HSL_arms 0 JS_0.
