(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the INSTANCE facts of pj_parse's image-B' walk (brief item 6): B := YD2l.TfibB (B', the
   generated image binding, TfibB_syms), ARx := ARcf with the error-buffer extents placed (YGcallcf.v's ARxs, the
   ARcfx of the walk lanes), PA := PI_prog_B at the B' listing, cp := CfParamsPreset.CfParams_preset.
   - pjp_inst_laws: the walk's LAWS, YGcallcf.AR_laws_x_xs over a Theorem Labs lane's AR_laws_ok_cf (no image premise).
   - pjp_inst_frame_hull: pjp_g_vis' first conjunct, ARx_frame_hull_vis_cf_ok (no image premise).
   - pjp_inst_img_cover: the cover check of B''s generated lists (YF0m.v Tfib_zero_shadow, Tfib_const_shadow) over the
     instance's own image bounds [IMG_LO_B, IMG_TOP_B) = [pa_lo, pa_hi) of PI_prog_B, by vm_compute (the WITNESS).
   - pjp_inst_img_vis: pjp_g_vis' third conjunct at the instance, from that check (YImgShadowCoverCf.v
     img_shadow_vis_cf_at_of_cover) and TfibB_syms' list equations (ts_zsh, ts_const).
   - pjp_inst_zs_gran / pjp_inst_zs_aligned: pjp_g_vis' second conjunct, every zero-shadow range of B' (YF0m.v
     Tfib_zero_shadow, = as_zero_shadow TfibB by ts_zsh) starts and ends on a granule boundary, by vm_compute (the
     WITNESS).
   So pjp_g_vis holds at the instance with no premise; pj_parse_top.v pj_parse_holds_Bp uses it.
   proves no function (kind: instance witnesses). No address numeral: the bounds are YImgTop.v's names. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfAmx2 YImgShadowCover YImgShadowCoverCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YGcfFsVis YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallcf YG0lawscf YD2l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the cover check of image B''s own generated lists over its own bounds (the vm_compute witness) *)
Lemma pjp_inst_img_cover :
  img_shadow_cover YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow IMG_LO_B IMG_TOP_B = true.
Proof. vm_compute. reflexivity. Qed.

(* every zero-shadow range of image B''s generated list is whole granules (the vm_compute witness) *)
Lemma pjp_inst_zs_gran :
  forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) YF0m.Tfib_zero_shadow = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pjp_inst_zs_aligned : forall q m, In (q, m) (as_zero_shadow YD2l.TfibB) -> q mod 8 = 0 /\ m mod 8 = 0.
Proof.
intros q m Hin. rewrite (YF0m.ts_zsh YD2l.TfibB YD2l.TfibB_syms) in Hin.
pose proof (proj1 (forallb_forall _ _) pjp_inst_zs_gran (q, m) Hin) as W. cbn [fst snd] in W.
apply andb_prop in W as [W1 W2]. apply Z.eqb_eq in W1, W2. exact (conj W1 W2).
Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation ARI :=
  (fun ly S Hp W mem md => ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ xs_placed_cf ly S).

Lemma pjp_inst_laws : AR_laws_x SEGS TB ARI (@cf_head CP).
Proof. exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)). Qed.

Lemma pjp_inst_frame_hull : ARx_frame_hull_vis SEGS TB ARI.
Proof.
intros ly S Hp W mem md cid pos [HA _] Hin.
exact (ARx_frame_hull_vis_cf_ok (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)
  ly S Hp W mem md cid pos HA Hin).
Qed.

Lemma pjp_inst_img_vis : forall ly S Hp W mem md a, ARI ly S Hp W mem md ->
  @pa_lo _ B_prog_listing PA <= a < @pa_hi _ B_prog_listing PA -> aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a [HA _] Ha.
assert (Iz : incl YF0m.Tfib_zero_shadow (as_zero_shadow TB))
  by (rewrite (YF0m.ts_zsh TB YD2l.TfibB_syms); apply incl_refl).
assert (Ic : forall ly0, incl YF0m.Tfib_const_shadow (as_const TB ly0))
  by (intros ly0; rewrite (YF0m.ts_const TB YD2l.TfibB_syms ly0); unfold YF0m.Tfib_const;
      apply incl_appr, incl_appr, incl_refl).
exact (img_shadow_vis_cf_at_of_cover (cp := CP) SEGS TB YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow IMG_LO_B IMG_TOP_B
  pjp_inst_img_cover Iz Ic ly S Hp W mem md a HA Ha).
Qed.
End i.

Print Assumptions pjp_inst_img_cover.
Print Assumptions pjp_inst_laws.
Print Assumptions pjp_inst_frame_hull.
Print Assumptions pjp_inst_img_vis.
Print Assumptions pjp_inst_zs_gran.
Print Assumptions pjp_inst_zs_aligned.
