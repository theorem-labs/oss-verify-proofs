(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30: omx-clap-core/fuzz_preset, image B' (asan-ubsan, #102 pin B' d663f82d7f48, unstripped twin
   c90d4fa54d43): pj_string's B' result AT THE INTERFACE INSTANCE, the relation the B' composition uses
   (PresetCfnB.iface_ARx, lib/AU/PresetCfnB.v:965: ARcf at CfParams_preset /\ xs_placed_cf, over the listing's
   segments), where the callee walks are stated (a Theorem Labs lane's FuzzStrdupB at its ARcfx, the same relation).
   tpj_string_B_preset_iface: the kit's tpj_string_specX (lib/A/PRH_FnPj.v) at CfParams_preset, prh_img_B,
   B_prog_listing, PI_prog_B, YD2l.TfibB and ARx := iface_ARx, for every CTX0; the callee premises MEMSET
   (__asan_memset's m-form) and STRDUP (the kit's tfuzz_strdup_specX) at the same ARx. DERIVED from the ARx-generic walk
   theorem the ARcf top tpj_string_B_preset instantiates (pj_string_top.v tpj_string_B_holds_kit), so no transfer
   between relations is needed; its Section hypotheses at iface_ARx:
   - LAWS: YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (as lib/B/Prog/pj_free_iface.v and
     CheckBoundedAllocBInst.v's check_bounded_alloc_holds_B_inst_xs discharge it at the same relation);
   - PAL: PALibB.exvi_eh_palib (independent of ARx);
   - img_shadow_vis_cf: pj_string_top.v pjs_g_lit_sh_B (the cover check at ARcf) through the first conjunct (the
     hypothesis reads ARx only as a premise);
   - TS: YD2l.TfibB_syms;
   - HULL: pj_string_top.v pjs_hull_preset (a fact about CfParams_preset only, independent of ARx).
   A separate leaf so that the walk's own files and closure stay as landed; this file alone Requires the interface.
   No numeral. rule 24: proves no function (kind: instance of an existing walk at another allocator relation). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YD2l YG0ncf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_string_top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetCfnB.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

Section iface. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
(* the interface's relation (lib/AU/PresetCfnB.v iface_ARx) at the B' listing *)
#[local] Abbreviation ARi := (PresetCfnB.iface_ARx (L := B_prog_listing) (PA := PI_prog_B) TB).
(* the callee texts at the interface instance *)
Hypothesis MEMSET : YGcallMxmn.aintrin_realizes_xm SEGS TB ARi OSet (@pa_sigma _ B_prog_listing PI_prog_B AS___asan_memset).
Hypothesis STRDUP : tfuzz_strdup_specX (cp := CP) (PA := PI_prog_B) TB ARi SK.

(* LAWS at iface_ARx: the cf laws, kept by the conjunction with xs_placed_cf (YGcallcf.AR_laws_x_xs) *)
Lemma pjs_wit_laws_iface : AR_laws_x SEGS TB ARi (@cf_head CP).
Proof.
unfold PresetCfnB.iface_ARx.
exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)).
Qed.

(* the image's shadow map at iface_ARx: pjs_g_lit_sh_B (at ARcf) through the first conjunct *)
Lemma pjs_g_lit_sh_iface : forall ly S Hp (W : world SEGS) mem md a, ARi ly S Hp W mem md ->
  IMG_LO_B <= a < IMG_TOP_B -> aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a [HA _] Ha. exact (pjs_g_lit_sh_B ly S Hp W mem md a HA Ha).
Qed.

(* The kit's tpj_string_specX at the interface instance *)
Theorem tpj_string_B_preset_iface : forall CTX0,
  tpj_string_specX (cp := CP) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) TB ARi SK CTX0.
Proof.
exact (tpj_string_B_holds_kit (cp := CP) TB ARi MEMSET STRDUP pjs_wit_laws_iface PALibB.exvi_eh_palib
  pjs_g_lit_sh_iface YD2l.TfibB_syms pjs_hull_preset).
Qed.
End iface.
