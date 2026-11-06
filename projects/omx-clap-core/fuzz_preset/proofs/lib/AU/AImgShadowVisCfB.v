(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: written for omx-clap-core/fuzz_preset's ASan image B (asan-ubsan, #102 pin d663f82d); the twin of
   lib/A/AImgShadowVisCf.v. h-mani-a8's img_shadow_vis_cf (lib/Reusable/YGcfAmx2.v, a Definition there) PROVED for
   image B: the cover check of B's generated lists (tfib_img_shadow_cover_B: the zero-shadow ranges Tfib_zero_shadow
   and the shadow cells Tfib_const_shadow of lib/Reusable/YF0m.v, by vm_compute) with lib/Reusable/YImgShadowCoverCf.v's
   img_shadow_vis_cf_of_cover. img_shadow_vis_cf_B asks only the two list equations of an image binding of B;
   tfib_img_shadow_vis_cf_B takes them from TfibSyms (lib/Reusable/YF0m.v). The bounds are image B's CfImg fields
   (CfImg_B's cf_img_lo / cf_img_top, lib/AU/CfImgB.v, generated from the pinned image), equal to YImgTop.v's
   IMG_LO_B / IMG_TOP_B by conversion. No count of granules, ranges or cells is written here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfAmx2 YImgShadowCover YImgShadowCoverCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The cover check of image B's own lists. *)
Lemma tfib_img_shadow_cover_B : img_shadow_cover Tfib_zero_shadow Tfib_const_shadow IMG_LO_B IMG_TOP_B = true.
Proof. vm_compute. reflexivity. Qed.

(* The two list facts the composition needs from an image binding of B. *)
Lemma tfib_zsh_incl_B : forall B, as_zero_shadow B = Tfib_zero_shadow -> incl Tfib_zero_shadow (as_zero_shadow B).
Proof. intros B E. rewrite E. apply incl_refl. Qed.
Lemma tfib_const_shadow_incl_B : forall B, (forall ly, as_const B ly = Tfib_const ly) ->
forall ly, incl Tfib_const_shadow (as_const B ly).
Proof. intros B E ly. rewrite E. unfold Tfib_const. apply incl_appr, incl_appr, incl_refl. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.

Theorem img_shadow_vis_cf_B : forall segs B,
as_zero_shadow B = Tfib_zero_shadow -> (forall ly, as_const B ly = Tfib_const ly) -> img_shadow_vis_cf (ci := CfImg_B) segs B.
Proof.
intros segs B Ez Ec.
exact (img_shadow_vis_cf_of_cover (ci := CfImg_B) segs B Tfib_zero_shadow Tfib_const_shadow tfib_img_shadow_cover_B
(tfib_zsh_incl_B B Ez) (tfib_const_shadow_incl_B B Ec)).
Qed.

Theorem tfib_img_shadow_vis_cf_B : forall segs B, TfibSyms B -> img_shadow_vis_cf (ci := CfImg_B) segs B.
Proof. intros segs B HB. exact (img_shadow_vis_cf_B segs B (ts_zsh B HB) (ts_const B HB)). Qed.
End b.

(* img_shadow_vis_xs_B: the same fact at the generic rules' relation of the cf instance, ARxs (YGcallcf.v:214, a Local
   Abbreviation there for ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S; written out here, no Require of YGcallcf),
   by its first conjunct. *)
Section xs. Context {rc : YM05.RunCeil} {cp : CfParams} {ci : CfImg}.
Theorem img_shadow_vis_xs_B : forall segs B, TfibSyms B ->
forall ly S Hp (W : world segs) mem md a,
ARcf (rc := rc) (cp := cp) segs B ly S Hp W mem md /\ xs_placed_cf (rc := rc) ly S ->
@cf_img_lo CfImg_B <= a < @cf_img_top CfImg_B -> aview segs (w_H W) mem (shadow_addr a) <> None.
Proof.
intros segs B HB ly S Hp W mem md a [HAR _] Ha.
exact (img_shadow_vis_cf_at_of_cover (rc := rc) (ci := ci) (cp := cp) segs B Tfib_zero_shadow Tfib_const_shadow
  (@cf_img_lo CfImg_B) (@cf_img_top CfImg_B) tfib_img_shadow_cover_B (tfib_zsh_incl_B B (ts_zsh B HB))
  (tfib_const_shadow_incl_B B (ts_const B HB)) ly S Hp W mem md a HAR Ha).
Qed.
End xs.
