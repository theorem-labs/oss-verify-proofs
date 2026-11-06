(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_errbapart.v (commit 4d286b2e618d, file sha256 0e6fe23b0bda) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 1 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: new file, reply image B's discharge of the cf-layer unit row ERRB_APART (row
   img-errbapart-B of a Theorem Labs lane's internal file REPLY-IMG-ROWS.md; the internal file CF-UNIT-HYPS.md row ERRB_APART): the error-buffer object misses the
   internal allocator's zone and, at every layout the cf relation admits, the depot zone. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YG0f YM05 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0m YF0x YD2l. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DGgi. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFfl.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The statement is the cf layer's ERRB_APART (lane F2a, YGcfInstFreePost.v) at reply image B:
   B := TfibB (YD2l.v), cf_errbuf_obj := CfImg_B's (CfImgB.v: __asan::error_message_buffer, 0xaaf68), dg_izone /
   dg_dzone := DImg_reply's (DGif0cgif.v: DGgi.IZONE / DGgi.DZONE). The layout guard is the UNFOLDED text of the cf
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
- intros Hz. cbn [dg_izone DImg_cgif] in Hz. unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Hz. lia.
- intros ly ((LO & _ & _) & IC & _) Hd. cbn [dg_dzone DImg_cgif] in Hd. unfold DGgi.DZONE in Hd.
  cbn [im_img_cover AImg_cgif] in IC. unfold img_cover, TFIB_IMG_LO, TFIB_IMG_END in IC.
  (* the nodes and store blocks (owned extents 4 and 5) are apart from the image window (static extent 9), which holds
     the error-buffer object *)
  pose proof (YFfl.pairwise_nth zdisjoint _ 4 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DN.
  pose proof (YFfl.pairwise_nth zdisjoint _ 5 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DS.
  unfold zdisjoint in DN, DS. cbn [fst snd] in DN, DS. unfold kNodesBlockSize, kStoreBlockSize in *. lia.
Qed.

End d.
