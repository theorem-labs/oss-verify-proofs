(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARcf form of YImgShadowCover.v. ARmcf keeps cgif's zero-shadow field (amc_zshadow) and
   const field (amc_const) verbatim (YG0ncf.v:89-102), so the same reader lemma, shadow_vis_of_cover, gives the shadow
   map of an image range at ARcf from the cover check of the image's lists. img_shadow_vis_cf_of_cover is the
   instance of h-mani-a8's Definition img_shadow_vis_cf (YGcfAmx2.v) for any image whose lists pass the check at
   the image's own CfImg bounds cf_img_lo / cf_img_top. No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfAmx2 YImgShadowCover.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* For any image bounds L, H. *)
Definition img_shadow_vis_cf_at (segs : list Segment) (B : asyms) (L H : Z) : Prop :=
forall ly S Hp (W : world segs) mem md a, ARcf segs B ly S Hp W mem md -> L <= a < H ->
aview segs (w_H W) mem (shadow_addr a) <> None.

Theorem img_shadow_vis_cf_at_of_cover : forall segs B zs cs L H,
img_shadow_cover zs cs L H = true -> incl zs (as_zero_shadow B) -> (forall ly, incl cs (as_const B ly)) ->
img_shadow_vis_cf_at segs B L H.
Proof.
intros segs B zs cs L H Hc Iz Ic ly S Hp W mem md a HAR Ha. destruct HAR as (M & _).
exact (shadow_vis_of_cover B ly _ zs cs L H Hc Iz (Ic ly) (amc_zshadow _ _ _ _ _ M) (amc_const _ _ _ _ _ M) a Ha).
Qed.

(* h-mani-a8's statement (YGcfAmx2.v), at the image's own bounds cf_img_lo / cf_img_top. *)
Theorem img_shadow_vis_cf_of_cover : forall segs B zs cs,
img_shadow_cover zs cs cf_img_lo cf_img_top = true -> incl zs (as_zero_shadow B) -> (forall ly, incl cs (as_const B ly)) ->
img_shadow_vis_cf segs B.
Proof.
intros segs B zs cs Hc Iz Ic. exact (img_shadow_vis_cf_at_of_cover segs B zs cs cf_img_lo cf_img_top Hc Iz Ic).
Qed.
End c.
