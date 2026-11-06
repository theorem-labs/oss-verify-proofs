(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, reply image B's discharge of the cf-layer unit row ERRB_APART (row
   img-errbapart-B of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record); CF-UNIT-HYPS.md (sha256 77b3f94c95d2; internal record) row ERRB_APART): the error-buffer object misses the
   internal allocator's zone and, at every layout the cf relation admits, the depot zone. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YG0f YM05 YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m YF0x YD2l CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply ImgBaseDG DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DGgi YFfl.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The statement is the cf layer's ERRB_APART (lane F2a, YGcfInstFreePost.v, a working branch) at reply image B:
   B := TfibB (YD2l.v), cf_errbuf_obj := CfImg_B's (CfImgB.v: __asan::error_message_buffer, 0xa5ea8), dg_izone /
   dg_dzone := DImg_reply's (DGif0reply.v: DGgi.IZONE / DGgi.DZONE). The layout guard is the UNFOLDED text of the cf
   layer's LGUARD (YGcfInstFreePost.v @ a3d076d83cd: ly_img_ok B ly /\ im_img_cover ly /\ asyms_ok B) with ly_img_ok
   unfolded (YGcfInstBase.v:140 @ a3d076d83cd: layout_ok ly /\ ly_tsd ly = as_tsd B /\ Forall ...); this tree carries
   neither name yet. *)
Lemma ERRB_APART_B : forall a, @cf_errbuf_obj CfImg_B <= a < @cf_errbuf_obj CfImg_B + 56 ->
  ~ dg_izone a /\
  (forall ly, ((layout_ok ly /\ ly_tsd ly = as_tsd TfibB /\
                Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static TfibB ++ as_zero_shadow TfibB)) /\
               im_img_cover ly /\ asyms_ok TfibB) ->
     ~ dg_dzone ly a).
Proof.
intros a Ha. cbn in Ha. split.
- intros Hz. cbn [dg_izone DImg_reply] in Hz. unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Hz. lia.
- intros ly ((LO & _ & _) & IC & _) Hd. cbn [dg_dzone DImg_reply] in Hd. unfold DGgi.DZONE in Hd.
  cbn [im_img_cover AImg_reply] in IC. unfold img_cover, TFIB_IMG_LO, TFIB_IMG_END in IC.
  (* the nodes and store blocks (owned extents 4 and 5) are apart from the image window (static extent 9), which holds
     the error-buffer object *)
  pose proof (YFfl.pairwise_nth zdisjoint _ 4 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DN.
  pose proof (YFfl.pairwise_nth zdisjoint _ 5 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DS.
  unfold zdisjoint in DN, DS. cbn [fst snd] in DN, DS. unfold kNodesBlockSize, kStoreBlockSize in *. lia.
Qed.

End d.
