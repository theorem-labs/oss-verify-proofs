(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Test file (a Theorem Labs lane): a Theorem Labs lane's standing acceptance gate (06:19Z) for every glue green. A Theorem Labs lane's ruled PALibF
   (lib/AU/Prog/SceneFrame.v at 8df4a950395, the same blob at a Theorem Labs lane f6ab6e97937 and a Theorem Labs lane 722526c3436) states
   palf_sm8 = StackMalloc8Tbl.PC_STACK_MALLOC_8, and that field closes by vm_compute at scene's concrete B
   (YD2l.TfibB, a Theorem Labs lane d7f9043aaa7): G_Close.g_TLF builds PALibF at TfibB, its palf_sm8 field by a Theorem Labs lane's
   ScenePalfSm8.scene_palf_sm8 (c3131b23386), the others by computation. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym SceneSyms SceneList ScenePa SceneImg SceneFrame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Rt Require Import StackMalloc8Tbl.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require YD2l G_Close.
Print PALibF.
(* The gate line, a Theorem Labs lane's template (a Theorem Labs lane 06:19Z): palf_sm8 mentions no B, so it closes at PI_scene by vm_compute,
   with pa_sigma's RunCeil instance passed explicitly. *)
Example zz_palf_sm8_gate (rc : YM05.RunCeil) (fx : YK11.FPState) :
  @pa_sigma rc scene_listing (@PI_scene rc) SS___asan_stack_malloc_8 = StackMalloc8Tbl.PC_STACK_MALLOC_8.
Proof. vm_compute. reflexivity. Qed.
(* the same field read off PALibF at B := TfibB (G_Close.g_TLF, built by vm_compute) *)
Lemma g_palf_sm8_TfibB : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @pa_sigma rc scene_listing (@PI_scene rc) SS___asan_stack_malloc_8 = StackMalloc8Tbl.PC_STACK_MALLOC_8.
Proof. intros rc fx. exact (palf_sm8 YD2l.TfibB (G_Close.g_TLF rc fx)). Qed.
Check G_Close.g_TLF.
Print Assumptions G_Close.g_TLF.
Print Assumptions g_palf_sm8_TfibB.
