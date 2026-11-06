(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (asan-ubsan), the twin of lib/A/SceneAlloc.v.
   The closing instances of the glue rows AMALLOC and AFREE (lib/AU/G_Close.v, Section close; donor cgif
   A/AD1q.v:43-44, asan-ubsan twin the Y file of the same number; a Theorem Labs lane's entry statement
   lib/AU/P_LLVMFuzzerTestOneInput.v, Section h, :275-276), at the glue's concrete B := YD2l.TfibB:
     Hypothesis AMALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), amalloc_realizes SEGS B.
     Hypothesis AFREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), afree_realizes SEGS B.
   SEGS is the glue's (and a Theorem Labs lane's statement's) notation for the listing's segments, (@pa_segs _ scene_listing
   PI_scene). scene_AMALLOC and scene_AFREE state each row with B := YD2l.TfibB and SEGS written out, so the glue
   closes the rows by `exact SceneAlloc.scene_AMALLOC` and `exact SceneAlloc.scene_AFREE`. The glue Requires this
   file, so this file does not Require G_Close or G_Top.
   No code is walked here. Each lemma is the restaged release's allocator theorem at B := TfibB:
     lib/AU/YF0w.v:44 tfib_amalloc_realizes, lib/AU/YF0q.v:11 afree_realizes_closed; each is
     `forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> ..._realizes tfibsegs B`.
   The premises and the bridge, each closed:
   - TfibSyms TfibB: YD2l.TfibB_syms (lib/AU/YD2l.v:101).
   - as_dhash TfibB t = tfib_dhash t: TfibB's as_dhash field is tfib_dhash (YD2l.v:61), so `eq_refl`.
   - SEGS: PI_scene's pa_segs is scene_segs (lib/AU/Prog/SceneImg.v:57) = AsanUbsan.M.loaded_segments
     (lib/AU/Prog/SceneCode.v:18), which is tfibsegs (lib/AU/YB1v.v:12); the two are equal by conversion (`change`).
   The rows name no symbol through SIGMA: the malloc / free pcs are fields of as_code B (pc_wrap_malloc,
   pc_malloc_ra0, pc_wrap_free, pc_free_ra0; Tfib_code, lib/AU/YF0l.v:10-11), which TfibSyms fixes. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0f YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import SceneSyms SceneList ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require YB1v YD2l YF0w YF0q.
Open Scope Z_scope.

Lemma scene_AMALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  amalloc_realizes (@pa_segs _ scene_listing PI_scene) YD2l.TfibB.
Proof.
intros rc fx. change (@pa_segs _ scene_listing PI_scene) with YB1v.tfibsegs.
exact (YF0w.tfib_amalloc_realizes YD2l.TfibB YD2l.TfibB_syms (fun _ => eq_refl)).
Qed.

Lemma scene_AFREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  afree_realizes (@pa_segs _ scene_listing PI_scene) YD2l.TfibB.
Proof.
intros rc fx. change (@pa_segs _ scene_listing PI_scene) with YB1v.tfibsegs.
exact (YF0q.afree_realizes_closed YD2l.TfibB YD2l.TfibB_syms (fun _ => eq_refl)).
Qed.
