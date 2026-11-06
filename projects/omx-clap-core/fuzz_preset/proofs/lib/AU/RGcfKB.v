(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfK.v (hub 96e1d2182ec6, blob 7341bfb6d080), stated at fuzz_preset's asan image (ELF sha256 bff8519bbe3e), to its asan-ubsan image (ELF sha256 c90d4fa54d43): module paths to the image-B twins, every image numeral by symbol + offset, image bounds by the image-B start-up facts; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YG00 YG0f YM05 RGtop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import RGthinSB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfReallocCompose.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition K1B (B : asyms) : YGcfReallocCompose.K1r_t tfibsegs :=
fun ly S Hp W regs mem md p n_old n ch S1 W1 regsA memA mdA =>
K1r B ly S W regs mem md p n_old n ch S1 W1 regsA memA mdA.

Definition KnB : YGcfReallocCompose.Knr_t tfibsegs :=
fun ly S Hp W regs mem md n ch S1 W1 regsA memA mdA =>
Knr ly S W regs mem md n ch S1 W1 regsA memA mdA.

End a.
