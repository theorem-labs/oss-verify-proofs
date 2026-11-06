(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/A/WrapMallocAConsts.v, with its module paths changed. *)
(* Theorem Labs, 2026-10-30: the image-A (asan, pin 1be0f53d96cb) code addresses the malloc walks of
   omx-clap-core/fuzz_preset share, and their `ceil` tactic, in a file of their own so that the malloc BODY walk
   (WrapMallocABody*.v) does not Require the wrapper's call segment (WrapMallocACall.v re-exports this file). Moved
   verbatim from WrapMallocACall.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq AFgn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
Import ListNotations.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Open Scope Z_scope.
(* The return addresses the segment leaves: asan_malloc's `jal Allocate` (asan_malloc + 0x28) returns to asan_malloc
   + 0x2c (A 0x32588); ___interceptor_malloc's `jal asan_malloc` (+ 0x130) returns to + 0x134 (A 0x53a44). The entries
   are AB1w.v:51 / :302. *)
Definition RA_ALLOC : Z := tfib_A__ZN6__asan11asan_mallocEmPN11__sanitizer18BufferedStackTraceE + 0x2c.
Definition RA_ASAN_MALLOC : Z := tfib_A____interceptor_malloc + 0x134.
Definition PC_ALLOCATE : Z := tfib_A__ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb.
Definition PC_UNWINDIMPL : Z := tfib_A__ZN11__sanitizer18BufferedStackTrace10UnwindImplEmmPvbj.
