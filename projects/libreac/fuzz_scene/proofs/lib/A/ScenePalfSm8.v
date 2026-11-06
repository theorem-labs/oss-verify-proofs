(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (asan). scene_palf_sm8 is the palf_sm8 row of
   PALibF (lib/A/Prog/SceneFrame.v:105) at the listing scene_listing and its image instance PI_scene
   (lib/A/Prog/SceneImg.v:56), proved: PI_scene's pa_sigma is scene_sigma (lib/A/Prog/SceneAddr.v:17), which maps
   SS___asan_stack_malloc_8 to 0x3f40c, the value of StackMalloc8Tbl.PC_STACK_MALLOC_8 (lib/A/Rt/StackMalloc8Tbl.v:48).
   PAImg's one section variable is rc : YM05.RunCeil, so pa_sigma takes rc explicitly and the lemma binds it as a
   Section Context, as TLF does (forall rc). The first proof of the same statement, by the same script, is
   a Theorem Labs lane's probe zz_palf_sm8_gate (ZZGateA.v (sha256 0652feb59567; internal record), an Example, not
   published; rc=0, kernel primitives only).
   The glue gives TLF's palf_sm8 field as `exact scene_palf_sm8`. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require SceneSyms SceneList ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Rt Require StackMalloc8Tbl.
Section g.
Context {rc : YM05.RunCeil}.
Lemma scene_palf_sm8 :
  @ScenePa.pa_sigma rc SceneList.scene_listing SceneImg.PI_scene SceneSyms.SS___asan_stack_malloc_8 =
  StackMalloc8Tbl.PC_STACK_MALLOC_8.
Proof. vm_compute; reflexivity. Qed.
End g.
About scene_palf_sm8.
Print Assumptions scene_palf_sm8.
