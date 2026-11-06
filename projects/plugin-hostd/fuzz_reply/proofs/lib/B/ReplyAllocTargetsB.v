(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyAllocTargetsB.v, with its module paths and module names changed; 35 of its 50 lines of code are new or changed and 7 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30 (lane W, ReallocPrimary.CfW; a Theorem Labs lane realloc_primary at plugin-hostd/fuzz_reply, image B;
   restated every-fx by ReallocPrimary.RealSegA, WIP 7cd46b734f24; owner a Theorem Labs lane with lib/B/ReplyBTop.v, a Theorem Labs lane's
   ruling 2026-10-30 21:24Z).  No licence lines: its A twin lib/A/ReplyAllocTargets.v has none (adding-a-proof.md req 7).
   rule 24: no function proved (kind: interface; the TARGET statements of reply B's allocator theorems).

   The image-B twins of lib/A/ReplyAllocTargets.v's targets, at EVERY FP state and RunCeil (forall fx rc), as A's
   window text states them: what reply B's instance files prove and what B's composition takes.  Each B target is A's
   text read at image B: CfImg_B (lib/B/CfImgB.v), B's tfibsegs (lib/B/YB1v.v), TfibB (lib/B/YD2l.v), B's listing
   (lib/B/W_listing.v fr_prog_listing, PB_fr, WS_realloc) for the realloc wrapper's pc.  The CfParams record is
   lib/A/CfParamsReply.v's CfParams_reply, the record B top_x's relation ARX names
   (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:167) and every B instance is built over.  The cf image binder ci is named
   (fu1's afree_realizes_cf takes it implicitly).
   The free and the live-block realloc targets are PRIMED (route R), the twins of lib/A/ReplyAllocTargets.v at
   a working branch b0a95ec2ff7c: free is the cf layer's YG0dcfR.afree_realizes_cf_rh (free(NULL)
   is inside it, its premise `p = PNull \/ In (p, n) (blocks S)`), realloc of a live block is
   YGcfInstReallocK.arealloc_realizes_cf_k at every headroom k, at B's wrapper pc.
   Fit checks: textual Goals (`exact (fun h => h)`), and the fx0 instances of malloc / free.  The B driver's free
   premise (ReplyDriverCfB.v replyb_tfib_b_of_top_x / _sec) is the UNPRIMED afree_realizes_cf at this commit; it
   takes the primed text from here as A's ReplyDriverCf does. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YGcfNames YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YD2l CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YG0dcfR YGcfInstReallocK.
(* the image's CfImg and the parameter record, as B's composition takes them (the realloc text leaves both implicit) *)
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_reply.

(* malloc: the allocator's malloc realizes malloc_cf at reply B's image *)
Definition amalloc_target_replyB : Prop :=
  forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @amalloc_realizes_cf fx rc CfImg_B CfParams_reply tfibsegs TfibB.

(* free: the allocator's free realizes free_cf at reply B's image, PRIMED: the run is amreal' over RZ_cf with the
   leaf YG0dcfR.free_leaf_cf_rh; free(NULL) is the same realizer *)
Definition afree_target_replyB : Prop :=
  forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @YG0dcfR.afree_realizes_cf_rh fx rc CfImg_B CfParams_reply tfibsegs TfibB.

(* realloc of a live block, at the image's realloc wrapper: the run is amreal' over RZ_cf with the primed leaf
   YG0dcfR.realloc_leaf_cf_rh; at the entry the caller's room ROOM_cf_k S (RK_realloc + k) and the call's hull
   admission cf_hull_adm S n (CfParams), in the post the room ROOM_cf_k (snd r) k realloc keeps *)
Definition arealloc_target_replyB : Prop :=
  forall (fx : YK11.FPState) (rc : YM05.RunCeil) (k : nat),
  YGcfInstReallocK.arealloc_realizes_cf_k (fx := fx) (rc := rc) tfibsegs TfibB []
    (@pa_sigma _ fr_prog_listing PB_fr WS_realloc) k.

(* realloc (NULL, n), at the image's realloc wrapper *)
Definition arealloc_null_target_replyB : Prop :=
  forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  YGcfRealloc.arealloc_null_realizes_cf (fx := fx) (rc := rc) tfibsegs TfibB []
    (@pa_sigma _ fr_prog_listing PB_fr WS_realloc).

(* FIT CHECKS: the texts, copied verbatim *)
Goal amalloc_target_replyB -> forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @amalloc_realizes_cf fx rc CfImg_B CfParams_reply tfibsegs TfibB.
Proof. exact (fun h => h). Qed.
Goal afree_target_replyB -> forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @YG0dcfR.afree_realizes_cf_rh fx rc CfImg_B CfParams_reply tfibsegs TfibB.
Proof. exact (fun h => h). Qed.
Goal arealloc_target_replyB -> forall (fx : YK11.FPState) (rc : YM05.RunCeil) (k : nat),
  YGcfInstReallocK.arealloc_realizes_cf_k (fx := fx) (rc := rc) tfibsegs TfibB []
    (@pa_sigma _ fr_prog_listing PB_fr WS_realloc) k.
Proof. exact (fun h => h). Qed.
Goal arealloc_null_target_replyB -> forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  YGcfRealloc.arealloc_null_realizes_cf (fx := fx) (rc := rc) tfibsegs TfibB []
    (@pa_sigma _ fr_prog_listing PB_fr WS_realloc).
Proof. exact (fun h => h). Qed.
(* ... and the fx0 instances of malloc / free (the B driver's two allocator premises, once it takes the primed free) *)
Goal amalloc_target_replyB ->
  (forall (rc : YM05.RunCeil), @amalloc_realizes_cf YK11.fx0 rc CfImg_B CfParams_reply tfibsegs TfibB).
Proof. exact (fun h => h YK11.fx0). Qed.
Goal afree_target_replyB ->
  (forall (rc : YM05.RunCeil), @YG0dcfR.afree_realizes_cf_rh YK11.fx0 rc CfImg_B CfParams_reply tfibsegs TfibB).
Proof. exact (fun h => h YK11.fx0). Qed.
