(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the proof of proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v:155-165 rt_trace_in
   (c8557374ad2e) for libreac/fuzz_scene's asan build, against the image-free statement
   P_LLVMFuzzerTestOneInput_ctx.rt_trace_in_stmt (a Theorem Labs lane) and scene's trace universe lib/A/ACej.v.
   Numbers, all read from fuzz_scene.asan (pinned in projects/libreac/fuzz_scene/harness.yaml), each re-derived by
   verify_acej.py:
     RA_LLVMF      0x82774  ra of target_run's call of LLVMFuzzerTestOneInput (jal at 0x82770)
     PC_MALLOC_RA0 0x54fb4  ___interceptor_malloc 0x54eec + 0xc8, ra of its GetCurrentPc call (0x54fb0)
     PC_FREE_RA0   0x54e54  ___interceptor_free 0x54d1c + 0x138, ra of its GetCurrentPc call (0x54e50)
     malloc sites  0x82ba0 (body, call 0x82b9c), 0x82d94 (again, 0x82d90), 0x82eb8 (before, 0x82eb4)
     free sites    0x82eac (again, call 0x82ea8), 0x83028 (before, 0x83024), 0x83030 (body, 0x8302c) *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_ctx ACej.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0d YG0f.
Import ListNotations.
Local Open Scope Z_scope.

Definition RA_LLVMF_A : Z := 0x82774.
Definition PC_MALLOC_RA0_A : Z := 0x54fb4.
Definition PC_FREE_RA0_A : Z := 0x54e54.
Definition RT_malloc1_ra_A : Z := 0x82ba0.
Definition RT_malloc2_ra_A : Z := 0x82d94.
Definition RT_malloc3_ra_A : Z := 0x82eb8.
Definition RT_free1_ra_A : Z := 0x82eac.
Definition RT_free2_ra_A : Z := 0x83028.
Definition RT_free3_ra_A : Z := 0x83030.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem rt_trace_in_A : forall segs,
  rt_trace_in_stmt segs RA_LLVMF_A PC_MALLOC_RA0_A PC_FREE_RA0_A
    RT_malloc1_ra_A RT_malloc2_ra_A RT_malloc3_ra_A RT_free1_ra_A RT_free2_ra_A RT_free3_ra_A Tfib_universe.
Proof.
intros segs pcf ra regsT cx Hra0 Hra Hpc.
rewrite call_trace_of_spine. unfold rt_ch.
destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)); cbn [spine map fst snd]; rewrite Hra; try rewrite Hra0;
unfold RA_LLVMF_A, PC_MALLOC_RA0_A, PC_FREE_RA0_A, RT_malloc1_ra_A, RT_malloc2_ra_A, RT_malloc3_ra_A,
  RT_free1_ra_A, RT_free2_ra_A, RT_free3_ra_A in Hpc |- *;
destruct Hpc as [[-> [-> | [-> | ->]]] | [-> [-> | [-> | ->]]]];
apply memZL_In; vm_compute; reflexivity.
Qed.
End a.
