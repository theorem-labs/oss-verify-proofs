(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (asan-ubsan), the twin of lib/A/SceneTrace.v.
   The closing instance of the glue row HTRACE (lib/AU/G_Close.v, Section close; donor cgif A/ACeh.v:26, asan-ubsan
   twin the Y file of the same number), at the glue's concrete B := YD2l.TfibB:
     Hypothesis HTRACE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
       rt_trace_in_stmt SEGS RA_LLVMF (pc_malloc_ra0 (as_code B)) (pc_free_ra0 (as_code B))
         g_RT_malloc1_ra g_RT_malloc2_ra g_RT_malloc3_ra g_RT_free1_ra g_RT_free2_ra g_RT_free3_ra (as_universe B).
   The glue Requires this file, so this file does not Require G_Close or G_Top. RA_LLVMF and the six g_RT_* are
   Definitions of lib/AU/G_Top.v; scene_HTRACE states them as the literals they reduce to (A_LLVMF = 0x828a4):
     RA_LLVMF        0x827a0
     g_RT_malloc1_ra A_LLVMF + 0x3ac = 0x82c50    g_RT_free1_ra A_LLVMF + 0x6fc = 0x82fa0
     g_RT_malloc2_ra A_LLVMF + 0x5cc = 0x82e70    g_RT_free2_ra A_LLVMF + 0x8bc = 0x83160
     g_RT_malloc3_ra A_LLVMF + 0x708 = 0x82fac    g_RT_free3_ra A_LLVMF + 0x8c4 = 0x83168
   SEGS is the glue's (and a Theorem Labs lane's statement's) notation for the listing's segments. So the glue closes the row by
   `exact SceneTrace.scene_HTRACE`: conversion unfolds G_Top's Definitions to these literals.
   No code is walked here. The proof is rt_trace_in_AU (lib/AU/P_LLVMFuzzerTestOneInput_trace.v, whose literals these
   are), after two closed bridges and one conversion:
   - pc_malloc_ra0 (as_code TfibB) = 0x54fe0 and pc_free_ra0 (as_code TfibB) = 0x54e80: TfibB's as_code is Tfib_code
     (lib/AU/YD2l.v), whose fields are lib/AU/YF0l.v:10-11; each by `vm_compute; reflexivity`.
   - as_universe TfibB is Tfib_universe (lib/AU/YCej.v) by conversion (`change`). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import SceneSyms SceneList ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require YCej YD2l P_LLVMFuzzerTestOneInput_trace.
Open Scope Z_scope.

(* ---- TfibB's two allocator return pcs (the first entry of every allocation trace) ---- *)
Lemma scene_pc_malloc_ra0 : pc_malloc_ra0 (as_code YD2l.TfibB) = 0x54fe0.
Proof. vm_compute; reflexivity. Qed.
Lemma scene_pc_free_ra0 : pc_free_ra0 (as_code YD2l.TfibB) = 0x54e80.
Proof. vm_compute; reflexivity. Qed.

Lemma scene_HTRACE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  rt_trace_in_stmt (@pa_segs _ scene_listing PI_scene) 0x827a0
    (pc_malloc_ra0 (as_code YD2l.TfibB)) (pc_free_ra0 (as_code YD2l.TfibB))
    0x82c50 0x82e70 0x82fac 0x82fa0 0x83160 0x83168 (as_universe YD2l.TfibB).
Proof.
intros rc fx. change (as_universe YD2l.TfibB) with YCej.Tfib_universe.
rewrite scene_pc_malloc_ra0, scene_pc_free_ra0.
exact (P_LLVMFuzzerTestOneInput_trace.rt_trace_in_AU _).
Qed.

About scene_pc_malloc_ra0.
About scene_pc_free_ra0.
About scene_HTRACE.
Print Assumptions scene_pc_malloc_ra0.
Print Assumptions scene_pc_free_ra0.
Print Assumptions scene_HTRACE.
