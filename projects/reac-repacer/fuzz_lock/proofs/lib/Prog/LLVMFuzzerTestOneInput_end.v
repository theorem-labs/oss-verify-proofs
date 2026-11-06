(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/U/Prog/LLVMFuzzerTestOneInput_link.v, with its module paths changed; 9 of its 26 lines of code are new or changed and 22 lines of the source are left out. *)
(* fuzz_lock's LLVMFuzzerTestOneInput_contract in fuzz_lock.plain from the allocator and sink facts llvm_frame, in the
   form of libreac/fuzz_decode's lib/Prog/LLVMFuzzerTestOneInput_end.v (release 25e3d17bdb50). The libc strlen
   contract stays a premise of the unit. Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import strlen_c
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_g LLVMFuzzerTestOneInput_link Statement.
Import ListNotations.
Local Open Scope Z_scope.

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FR : llvm_frame rc B API SH SK.
Hypothesis STRLEN : strlen_contract.

Theorem llvm_contract : LLVMFuzzerTestOneInput_contract B API.
Proof.
  apply llvm_g_of_sr. destruct FR as (HA & Hel & HS).
  exact (LLVMFuzzerTestOneInput_holds B API HA Hel HS STRLEN).
Qed.

End E.
