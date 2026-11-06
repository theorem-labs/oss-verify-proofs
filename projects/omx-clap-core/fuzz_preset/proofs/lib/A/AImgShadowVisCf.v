(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: written for omx-clap-core/fuzz_preset's ASan image A. h-mani-a8's img_shadow_vis_cf
   (lib/Reusable/YGcfAmx2.v, a Definition there) PROVED for image A: the cover check of A's generated lists
   (tfib_img_shadow_cover, A/AImgShadowVis.v, by vm_compute) with lib/Reusable/YImgShadowCoverCf.v's
   img_shadow_vis_cf_of_cover. img_shadow_vis_cf_A asks only the two list equations of an image binding of B;
   tfib_img_shadow_vis_cf takes them from TfibSyms (A/AF0m.v). The bounds are image A's CfImg fields (CfImg_A's
   cf_img_lo / cf_img_top, generated from the pinned image), equal to YImgTop.v's IMG_LO / IMG_TOP by conversion. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfAmx2 YImgShadowCover YImgShadowCoverCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m AImgShadowVis CfImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.

Theorem img_shadow_vis_cf_A : forall segs B,
as_zero_shadow B = Tfib_zero_shadow -> (forall ly, as_const B ly = Tfib_const ly) -> img_shadow_vis_cf (ci := CfImg_A) segs B.
Proof.
intros segs B Ez Ec.
exact (img_shadow_vis_cf_of_cover (ci := CfImg_A) segs B Tfib_zero_shadow Tfib_const_shadow tfib_img_shadow_cover
(tfib_zsh_incl B Ez) (tfib_const_shadow_incl B Ec)).
Qed.

Theorem tfib_img_shadow_vis_cf : forall segs B, TfibSyms B -> img_shadow_vis_cf (ci := CfImg_A) segs B.
Proof. intros segs B HB. exact (img_shadow_vis_cf_A segs B (ts_zsh B HB) (ts_const B HB)). Qed.
End a.

(* img_shadow_vis_xs_A: the same fact at the generic rules' relation of the cf instance, ARxs (YGcallcf.v:214, a Local
   Abbreviation there for ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S; written out here, no Require of YGcallcf),
   by its first conjunct. *)
Section xs. Context {rc : YM05.RunCeil} {cp : CfParams} {ci : CfImg}.
Theorem img_shadow_vis_xs_A : forall segs B, TfibSyms B ->
forall ly S Hp (W : world segs) mem md a,
ARcf (rc := rc) (cp := cp) segs B ly S Hp W mem md /\ xs_placed_cf (rc := rc) ly S ->
@cf_img_lo CfImg_A <= a < @cf_img_top CfImg_A -> aview segs (w_H W) mem (shadow_addr a) <> None.
Proof.
intros segs B HB ly S Hp W mem md a [HAR _] Ha.
exact (img_shadow_vis_cf_at_of_cover (rc := rc) (ci := ci) (cp := cp) segs B Tfib_zero_shadow Tfib_const_shadow
  (@cf_img_lo CfImg_A) (@cf_img_top CfImg_A) tfib_img_shadow_cover (tfib_zsh_incl B (ts_zsh B HB))
  (tfib_const_shadow_incl B (ts_const B HB)) ly S Hp W mem md a HAR Ha).
Qed.
End xs.
