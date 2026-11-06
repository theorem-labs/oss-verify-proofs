(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset.asan image A, row A5 of the internal file FREE-PIECES-102.md. The invariants at the realloc
   record's Allocate call sites (YGcfReallocCompose.v K1r_t / Knr_t) for image A: RGthinS.v's K1r (Reallocate's
   `jal Allocate` 0x33054) and Knr (asan_realloc's NULL-input `jal Allocate` 0x32fb4), with the caller's ghost set Hp
   as the record's third argument; neither reads it. The prefix walks prove them (A/RGcfS1.v, A/RGcfS5.v); the thin
   segments use them (A/RGcfSegs.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YG00 YG0f YM05 RGtop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v RGthinS.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfReallocCompose.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition K1A (B : asyms) : YGcfReallocCompose.K1r_t tfibsegs :=
fun ly S Hp W regs mem md p n_old n ch S1 W1 regsA memA mdA =>
K1r B ly S W regs mem md p n_old n ch S1 W1 regsA memA mdA.

Definition KnA : YGcfReallocCompose.Knr_t tfibsegs :=
fun ly S Hp W regs mem md n ch S1 W1 regsA memA mdA =>
Knr ly S W regs mem md n ch S1 W1 regsA memA mdA.

End a.
