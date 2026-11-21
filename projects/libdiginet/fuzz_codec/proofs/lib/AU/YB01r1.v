(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_codec image B (asan-ubsan) from its own collector run (pass 2, collector log sha256 b42a5c18207b: 220 leaves = 50 hand-offs at main 0x804fc + 168 spins + 2 merges, 0 failure leaves) on the pinned fuzz_codec.asan-ubsan (sha256 73109e32e77beff294d41ae6f16d607479ad1884485781b322645e6f8afa99c3); the donor file's form, this image's states. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of YB01.v and the recorded join state of YB03.v: both computed in the build from the start-up run by check, per CONFIG_RSEQ flag (split per flag as plugin-hostd/fuzz_command's A/AB01rb.v, AB01r0.v and AB01r1.v), with Reusable/PlanRegen.v (the shape of libreac/fuzz_boxreg's A/AB01r.v; the hand-off states collected in one run of the check), the plan's variables renumbered by values read from probes of this unit's run. *)
(* The band join state and the hand-off states of the start-up run at CONFIG_RSEQ flag 1. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libdiginet.fuzz_codec.images Require Import AsanUbsan.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YK11 YK0c YK09 YA01 YA0c YA02 YA0h PlanRegen.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YB12 YB1h YB1l YB05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YB01rb.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.
Definition CS_VIA_1 : acs := Eval vm_compute in cs_via 1.
Definition JS_1 : acs := Eval vm_compute in js_of 1 CS_VIA_1.
Definition HSL_1 : list (nat * acs) := Eval vm_compute in HSL_arms 1 JS_1.
