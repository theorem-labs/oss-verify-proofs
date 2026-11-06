(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_errbapart.v (commit eb934de95d13, blob f2ca7d32865f) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them); DImg_A's zone fields are AFgn.IZONE / AFgi.DZONE (A/ADIfaceA.v:54), the same text as reply's DGgi ones, so the unfold after the field's cbn names them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YG0f YM05 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m AF0x AD2l CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGgi AFfl AFgn AFgi.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma ERRB_APART_A : forall a, @cf_errbuf_obj CfImg_A <= a < @cf_errbuf_obj CfImg_A + 56 ->
  ~ dg_izone a /\
  (forall ly, ((layout_ok ly /\ ly_tsd ly = as_tsd TfibB /\
                Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static TfibB ++ as_zero_shadow TfibB)) /\
               im_img_cover ly /\ asyms_ok TfibB) ->
     ~ dg_dzone ly a).
Proof.
intros a Ha. cbn in Ha. split.
- intros Hz. cbn [dg_izone DImg_A] in Hz. unfold AFgn.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in Hz. lia.
- intros ly ((LO & _ & _) & IC & _) Hd. cbn [dg_dzone DImg_A] in Hd. unfold AFgi.DZONE in Hd.
  cbn [im_img_cover AImg_A] in IC. unfold img_cover, TFIB_IMG_LO, TFIB_IMG_END in IC.

  pose proof (AFfl.pairwise_nth zdisjoint _ 4 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DN.
  pose proof (AFfl.pairwise_nth zdisjoint _ 5 9 _ _ (lo_disj _ LO) eq_refl eq_refl ltac:(lia)) as DS.
  unfold zdisjoint in DN, DS. cbn [fst snd] in DN, DS. unfold kNodesBlockSize, kStoreBlockSize in *. lia.
Qed.

End d.
