(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the proof of proofs/cgif/cgif_file_fuzzer/lib/YCf5.v rt_trace_in (asan-ubsan twin of
   lib/A/ACf5.v:155-165, c8557374ad2e) for libreac/fuzz_scene's asan-ubsan build, against the image-free statement
   lib/AU/P_LLVMFuzzerTestOneInput_ctx.rt_trace_in_stmt (a Theorem Labs lane's lib/A ctx closed under lib.AU, since the asan-ubsan
   tree's YCbq is its own module) and scene's trace universe lib/AU/YCej.v.
   Numbers, all read from fuzz_scene.asan-ubsan (pinned in projects/libreac/fuzz_scene/harness.yaml), each re-derived by
   verify_acej.py:
     RA_LLVMF      0x827a0  ra of target_run's call of LLVMFuzzerTestOneInput (jal at 0x8279c)
     PC_MALLOC_RA0 0x54fe0  ___interceptor_malloc 0x54f18 + 0xc8, ra of its GetCurrentPc call (0x54fdc)
     PC_FREE_RA0   0x54e80  ___interceptor_free 0x54d48 + 0x138, ra of its GetCurrentPc call (0x54e7c)
     malloc sites  0x82c50 (body, call 0x82c4c), 0x82e70 (again, 0x82e6c), 0x82fac (before, 0x82fa8)
     free sites    0x82fa0 (again, call 0x82f9c), 0x83160 (before, 0x8315c), 0x83168 (body, 0x83164) *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx YCej.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0d YG0f.
Import ListNotations.
Local Open Scope Z_scope.

Definition RA_LLVMF_AU : Z := 0x827a0.
Definition PC_MALLOC_RA0_AU : Z := 0x54fe0.
Definition PC_FREE_RA0_AU : Z := 0x54e80.
Definition RT_malloc1_ra_AU : Z := 0x82c50.
Definition RT_malloc2_ra_AU : Z := 0x82e70.
Definition RT_malloc3_ra_AU : Z := 0x82fac.
Definition RT_free1_ra_AU : Z := 0x82fa0.
Definition RT_free2_ra_AU : Z := 0x83160.
Definition RT_free3_ra_AU : Z := 0x83168.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem rt_trace_in_AU : forall segs,
  rt_trace_in_stmt segs RA_LLVMF_AU PC_MALLOC_RA0_AU PC_FREE_RA0_AU
    RT_malloc1_ra_AU RT_malloc2_ra_AU RT_malloc3_ra_AU RT_free1_ra_AU RT_free2_ra_AU RT_free3_ra_AU Tfib_universe.
Proof.
intros segs pcf ra regsT cx Hra0 Hra Hpc.
rewrite call_trace_of_spine. unfold rt_ch.
destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)); cbn [spine map fst snd]; rewrite Hra; try rewrite Hra0;
unfold RA_LLVMF_AU, PC_MALLOC_RA0_AU, PC_FREE_RA0_AU, RT_malloc1_ra_AU, RT_malloc2_ra_AU, RT_malloc3_ra_AU,
  RT_free1_ra_AU, RT_free2_ra_AU, RT_free3_ra_AU in Hpc |- *;
destruct Hpc as [[-> [-> | [-> | ->]]] | [-> [-> | [-> | ->]]]];
apply memZL_In; vm_compute; reflexivity.
Qed.
End a.
