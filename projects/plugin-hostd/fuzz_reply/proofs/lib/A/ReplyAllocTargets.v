(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyAllocTargets.v, with its module paths and module names changed; 39 of its 51 lines of code are new or changed and 6 lines of the source are left out. *)
(* The TARGET statements of reply's four allocator theorems, at every FP state and RunCeil: what the instance files
   prove (ReplyAllocInst.v malloc, ReplyDeallocInst.v free, ReplyReallocInst.v the two realloc forms) and what the
   image-A composition ReplyATopX.v takes as its Section hypotheses AMALLOC_CF / AFREE_CF / AREALLOC_CF /
   AREALLOC0_CF.  Each target is that hypothesis's text, so ReplyATopX takes it by name; the fit checks below are
   `exact (fun h => h)`, against ReplyATopX's texts and against ReplyDriverCf.reply_tfib_of_top_x_triv's two fx0
   premises (lib/A/ReplyDriverCf.v:224-225).
   amalloc_realizes_cf names the image's CfImg (CfImg_A) and reply's CfParams.
   The free and the live-block realloc targets are PRIMED (route R: Deallocate's secondary free may re-hide shadow,
   and realloc frees the old block inside the call, both re-hide crossings): free is the cf layer's
   YG0dcfR.afree_realizes_cf_rh (the text ReplyDeallocInst.v exports; free(NULL) is inside it, its premise
   `p = PNull \/ In (p, n) (blocks S)`), realloc of a live block is YGcfInstReallocK.arealloc_realizes_cf_k at every
   headroom k; their fit checks are against the same texts, which ReplyATopX's AFREE_CF / AREALLOC_CF and
   ReplyDriverCf's free premise take from here.
   proves no function (kind: interface). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YG0dcfR YGcfInstReallocK.
(* the ASan image's sink instance, as ReplyATopX.v takes it *)
#[local] Existing Instance AE2k.tfib_sink_head.
(* the image's CfImg and reply's CfParams, as ReplyATopX.v takes them (its realloc texts leave both implicit) *)
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_reply.

(* malloc: the allocator's malloc realizes malloc_cf at reply's image *)
Definition amalloc_target_reply : Prop :=
  forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @amalloc_realizes_cf fx rc CfImg_A CfParams_reply tfibsegs TfibB.

(* free: the allocator's free realizes free_cf at reply's image, PRIMED: the run is amreal' over RZ_cf with the leaf
   YG0dcfR.free_leaf_cf_rh; free(NULL) is the same realizer *)
Definition afree_target_reply : Prop :=
  forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @YG0dcfR.afree_realizes_cf_rh fx rc CfImg_A CfParams_reply tfibsegs TfibB.

(* realloc of a live block, at the image's realloc wrapper: the run is amreal' over RZ_cf with the primed leaf
   YG0dcfR.realloc_leaf_cf_rh; at the entry the caller's room ROOM_cf_k S (RK_realloc + k) and the call's hull
   admission cf_hull_adm S n (CfParams), in the post the room ROOM_cf_k (snd r) k realloc keeps *)
Definition arealloc_target_reply : Prop :=
  forall (fx : YK11.FPState) (rc : YM05.RunCeil) (k : nat),
  YGcfInstReallocK.arealloc_realizes_cf_k (fx := fx) (rc := rc) tfibsegs TfibB []
    (@pa_sigma _ fr_prog_listing PB_fr WS_realloc) k.

(* realloc (NULL, n), at the image's realloc wrapper *)
Definition arealloc_null_target_reply : Prop :=
  forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  YGcfRealloc.arealloc_null_realizes_cf (fx := fx) (rc := rc) tfibsegs TfibB []
    (@pa_sigma _ fr_prog_listing PB_fr WS_realloc).

(* FIT CHECKS: ReplyATopX's AMALLOC_CF / AFREE_CF / AREALLOC_CF / AREALLOC0_CF texts, copied verbatim *)
Goal amalloc_target_reply -> forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @amalloc_realizes_cf fx rc CfImg_A CfParams_reply tfibsegs TfibB.
Proof. exact (fun h => h). Qed.
Goal afree_target_reply -> forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @YG0dcfR.afree_realizes_cf_rh fx rc CfImg_A CfParams_reply tfibsegs TfibB.
Proof. exact (fun h => h). Qed.
Goal arealloc_target_reply -> forall (fx : YK11.FPState) (rc : YM05.RunCeil) (k : nat),
  YGcfInstReallocK.arealloc_realizes_cf_k (fx := fx) (rc := rc) tfibsegs TfibB []
    (@pa_sigma _ fr_prog_listing PB_fr WS_realloc) k.
Proof. exact (fun h => h). Qed.
Goal arealloc_null_target_reply -> forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  YGcfRealloc.arealloc_null_realizes_cf (fx := fx) (rc := rc) tfibsegs TfibB []
    (@pa_sigma _ fr_prog_listing PB_fr WS_realloc).
Proof. exact (fun h => h). Qed.
(* ... and ReplyDriverCf.reply_tfib_of_top_x_triv's two premises (ReplyDriverCf.v:224-225), the fx0 instances *)
Goal amalloc_target_reply ->
  (forall (rc : YM05.RunCeil), @amalloc_realizes_cf YK11.fx0 rc CfImg_A CfParams_reply tfibsegs TfibB).
Proof. exact (fun h => h YK11.fx0). Qed.
Goal afree_target_reply ->
  (forall (rc : YM05.RunCeil), @YG0dcfR.afree_realizes_cf_rh YK11.fx0 rc CfImg_A CfParams_reply tfibsegs TfibB).
Proof. exact (fun h => h YK11.fx0). Qed.
