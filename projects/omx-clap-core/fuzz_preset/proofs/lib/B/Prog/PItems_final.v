(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the TOP of parse_items' image-B' walk at the relation ARcfx, with every image fact
   discharged by its instance witness. It is PItems_compose.v's pi_step_PI_TfibBx (VrdUnit's
   step_PI for the kit's f97c tparse_items_specX at B := YD2l.TfibB, ARx := ARcfx = ARcf /\ xs_placed_cf,
   RL := prh_room_live_a8, the B' listing B_prog_listing / PI_prog_B) with the five image premises closed by the
   computation witnesses of PItems_inst.v:
     HSH  pi_hshadow_law  by pii_hsh_x   (YGcfHeadSh.v's ARx_hshadow_law_cf_ok at ARcf, lifted through the conjunction)
     HZS  pi_zs_law       by pii_hzs_x   (TfibB's 18 zero-shadow ranges, vm_compute; no edge premise)
     HIMG pi_img_law      by pii_himg_x  (the const-cell law over [pa_lo, pa_hi) = [0x10000, 0x601000))
     PST  pal_pst_ok      by pii_pst_ok  (the program's statics miss TfibB's owned statics and errno)
     UNP  pal_unpoison    by pii_unpoison (both 0x551e4)
   What stays a premise is a CALLEE CONTRACT or an allocator stand-in, each with its owner:
     AMS  __asan_memset's m-form intrinsic contract (YGcallMxmn.aintrin_realizes_xm)      the frame-class walk
     TGR  the kit's f97c tgrow_specX                                                            the grow lane
     TPS  the kit's f97c tparse_string_specX                                                    the parse_string lane
     AF   the free row in its keep form, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep, and AU aunpoison_realizes_cf
          (fuzz_free_holds_B's own premises)
     PV   the kit's f97c tparse_value_specX at Nat.succ d, below MAXD                            PValueB (VrdUnit's step_PV)
   Rule 24: proves no function in this file (kind: composition); parse_items is proved when PV's owner closes the
   pair through VrdUnit.vrd_parse_items_closed, as PItems_top.v's pi_unit_closed does generically. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YM05 YI16 YC4aP YPsym YGcfNames YG0f YG0n YG0d YD2l YG0ncf YCbqG YA0n YG00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YGcfHp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnReader PRH_FnParse CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_top PItems_compose PItems_inst.
Local Open Scope Z_scope.

Section fin. Context {rc : YM05.RunCeil}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance CfImg_B.
#[local] Notation Lb := B_prog_listing.
#[local] Notation PIb := (@PI_prog_B rc).
#[local] Notation TB := YD2l.TfibB.
#[local] Notation RLa8 := PRH_Base.prh_room_live_a8.
#[local] Notation ARX := (fun ly S Hp W mem md =>
  YG0ncf.ARcf (cp := CfParams_preset) (@pa_segs _ Lb PIb) YD2l.TfibB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

Theorem pi_step_PI_final : forall (SK : YI16.sink_head) (CTX0 CW : list (list Z)),
  (forall fy : YK11.FPState,
     YGcallMxmn.aintrin_realizes_xm (fx := fy) (@pa_segs _ Lb PIb) TB ARX OSet (@pa_sigma _ Lb PIb AS___asan_memset)) ->
  (forall (fy : YK11.FPState) (CTX0' : list (list Z)) ,
     tgrow_specX (fx := fy) (RL := RLa8) (L := Lb) (PA := PIb) TB ARX SK CTX0') ->
  (forall (fy : YK11.FPState) (CTX0' CW' : list (list Z)),
     tparse_string_specX (fx := fy) (RL := RLa8) (L := Lb) (PA := PIb) TB ARX SK CTX0' CW') ->
  (forall fy : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fy) (@pa_segs _ Lb PIb) TB) ->
  (forall fy : YK11.FPState, YGcfHp.aunpoison_realizes_cf (fx := fy) (@pa_segs _ Lb PIb) TB) ->
  forall d,
  ((d < PjGrammar.MAXD)%nat -> pi_PV (RL := RLa8) (L := Lb) (PA := PIb) TB ARX SK CTX0 CW (Nat.succ d)) ->
  pi_PI (RL := RLa8) (L := Lb) (PA := PIb) TB ARX SK CTX0 CW d.
Proof.
intros SK CTX0 CW AMS TGR TPS AF AU.
exact (pi_step_PI_TfibBx SK CTX0 CW pii_hsh_x pii_hzs_x pii_himg_x AMS TGR TPS AF AU pii_pst_ok pii_unpoison).
Qed.

End fin.
