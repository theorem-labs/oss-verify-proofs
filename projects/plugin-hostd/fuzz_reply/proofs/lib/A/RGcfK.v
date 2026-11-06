(* Modified by a Theorem Labs lane (ReallocPrimary.RealSegA), 2026-10-30: relocated from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfK.v (commit d0fcb396eeeb, sha256 4c094065bb7d476d; preset image p102: unstripped fuzz_preset.asan sha256 bff8519bbe3e, pin 1be0f53d96cb) to plugin-hostd/fuzz_reply's asan image A (unstripped fuzz_reply.asan sha256 d751b179ea49, pin 42c58610e125) by a Theorem Labs lane's alreloc.py (frozen-ced0368250cb6538): module paths changed, every image numeral moved by symbol + offset (hand-check table in the commit); preset lib.Reusable -> reply lib.A for: RGtop YGcfReallocCompose. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_reply.asan image A, row A5. The invariants at the realloc
   record's Allocate call sites (YGcfReallocCompose.v K1r_t / Knr_t) for image A: RGthinS.v's K1r (Reallocate's
   `jal Allocate` 0x32674) and Knr (asan_realloc's NULL-input `jal Allocate` 0x325d4), with the caller's ghost set Hp
   as the record's third argument; neither reads it. The prefix walks prove them (A/RGcfS1.v, A/RGcfS5.v); the thin
   segments use them (A/RGcfSegs.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YG00 YG0f YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RGtop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v RGthinS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfReallocCompose.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition K1A (B : asyms) : YGcfReallocCompose.K1r_t tfibsegs :=
fun ly S Hp W regs mem md p n_old n ch S1 W1 regsA memA mdA =>
K1r B ly S W regs mem md p n_old n ch S1 W1 regsA memA mdA.

Definition KnA : YGcfReallocCompose.Knr_t tfibsegs :=
fun ly S Hp W regs mem md n ch S1 W1 regsA memA mdA =>
Knr ly S W regs mem md n ch S1 W1 regsA memA mdA.

End a.
