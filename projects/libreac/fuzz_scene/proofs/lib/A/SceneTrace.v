(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (asan). The closing instance of the glue row
   HTRACE (lib/A/G_Close.v, Section close; donor cgif A/ACeh.v:26), at the glue's concrete B := AD2l.TfibB:
     Hypothesis HTRACE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
       rt_trace_in_stmt SEGS RA_LLVMF (pc_malloc_ra0 (as_code B)) (pc_free_ra0 (as_code B))
         g_RT_malloc1_ra g_RT_malloc2_ra g_RT_malloc3_ra g_RT_free1_ra g_RT_free2_ra g_RT_free3_ra (as_universe B).
   The glue Requires this file, so this file does not Require G_Close or G_Top. RA_LLVMF and the six g_RT_* are
   Definitions of lib/A/G_Top.v; scene_HTRACE states them as the literals they reduce to (A_LLVMF = 0x82878):
     RA_LLVMF        0x82774
     g_RT_malloc1_ra A_LLVMF + 0x328 = 0x82ba0    g_RT_free1_ra A_LLVMF + 0x634 = 0x82eac
     g_RT_malloc2_ra A_LLVMF + 0x51c = 0x82d94    g_RT_free2_ra A_LLVMF + 0x7b0 = 0x83028
     g_RT_malloc3_ra A_LLVMF + 0x640 = 0x82eb8    g_RT_free3_ra A_LLVMF + 0x7b8 = 0x83030
   SEGS is the glue's (and a Theorem Labs lane's statement's) notation for the listing's segments. So the glue closes the row by
   `exact SceneTrace.scene_HTRACE`: conversion unfolds G_Top's Definitions to these literals.
   No code is walked here. The proof is rt_trace_in_A (lib/A/P_LLVMFuzzerTestOneInput_trace.v, whose literals these
   are), after two closed bridges and one conversion:
   - pc_malloc_ra0 (as_code TfibB) = 0x54fb4 and pc_free_ra0 (as_code TfibB) = 0x54e54: TfibB's as_code is Tfib_code
     (lib/A/AD2l.v), whose fields are lib/A/AF0l.v:10-11; each by `vm_compute; reflexivity`.
   - as_universe TfibB is Tfib_universe (lib/A/ACej.v) by conversion (`change`). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import SceneSyms SceneList ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_LLVMFuzzerTestOneInput_ctx.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require ACej AD2l P_LLVMFuzzerTestOneInput_trace.
Open Scope Z_scope.

(* ---- TfibB's two allocator return pcs (the first entry of every allocation trace) ---- *)
Lemma scene_pc_malloc_ra0 : pc_malloc_ra0 (as_code AD2l.TfibB) = 0x54fb4.
Proof. vm_compute; reflexivity. Qed.
Lemma scene_pc_free_ra0 : pc_free_ra0 (as_code AD2l.TfibB) = 0x54e54.
Proof. vm_compute; reflexivity. Qed.

Lemma scene_HTRACE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  rt_trace_in_stmt (@pa_segs _ scene_listing PI_scene) 0x82774
    (pc_malloc_ra0 (as_code AD2l.TfibB)) (pc_free_ra0 (as_code AD2l.TfibB))
    0x82ba0 0x82d94 0x82eb8 0x82eac 0x83028 0x83030 (as_universe AD2l.TfibB).
Proof.
intros rc fx. change (as_universe AD2l.TfibB) with ACej.Tfib_universe.
rewrite scene_pc_malloc_ra0, scene_pc_free_ra0.
exact (P_LLVMFuzzerTestOneInput_trace.rt_trace_in_A _).
Qed.

About scene_pc_malloc_ra0.
About scene_pc_free_ra0.
About scene_HTRACE.
Print Assumptions scene_pc_malloc_ra0.
Print Assumptions scene_pc_free_ra0.
Print Assumptions scene_HTRACE.
