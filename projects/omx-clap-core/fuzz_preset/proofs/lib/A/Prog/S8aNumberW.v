(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 asan pin 1be0f53d96cb9d6c): INSTANCE WITNESSES for the image
   premises of piece 5's ev_number (S8aNumber.v), per the unit ruling of c-omx-hpreset 16:45Z (every Section hypothesis
   that asserts a fact ABOUT THE IMAGE has a lemma closed by computation at the real instance beside it), and
   ev_number_A, ev_number at the real image-A instance (PI := prh_img_A, cp := CfParams_preset, B any asyms with
   TfibSyms B) with every image premise discharged. What stays a premise of ev_number_A is not an image fact: LAWS
   (AR_laws_x of the allocator instance), HOFFB / HOFFF / HBLK32 / HAMEM8 (allocator-layout laws of the ARx instance,
   discharged where ARx := ARcf) and the call texts CPY / CMP / BCMP (their row owners).
   Witnesses: HIMG (prh_img_A's ex_value frame, vm_compute), HHEAD (CfParams_preset's cf_head = 16), Htp / Herrno /
   Hown (h-verbs-1's lib/A/Prog/strtod_row_sat.v strtod_sat_tp_A / strtod_sat_errno_A / strtod_sat_owned_A, computed
   at image A's record AD2l.TfibB, carried to B by TfibSyms' ts_tp / ts_errno / ts_owned: TfibB's fields are TFIB_TP,
   TFIB_ERRNO and Tfib_owned_static), HPST (S1ImgA.v pst_in_img_A, and the seven statics avoid errno by computation),
   HGOTC (the A' binding's const cell, AE22.v canary_cell_in: Tfib_const_abs row 169 by computation, A_GOT_CANARY =
   STRTOD_GOT_GUARD, V_GOT_CANARY = STRTOD_GUARD by computation).
   rule 24: no function proved
   rule 24: proves no function (kind: instance witnesses + an instantiation).
   No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP FCiface YGcallMx YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img CfParamsPreset AF0m AE22.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import strtod_c S1ImgA S8aNumCut S8aNumber.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require strtod_row_sat.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).

Lemma w_himg : @ev_img_ok prh_img_A.
Proof. vm_compute. discriminate. Qed.

Lemma w_hhead : 8 <= @cf_head CfParams_preset.
Proof. vm_compute. discriminate. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.

Lemma w_htp : as_tp B = STRTOD_TP.
Proof. rewrite (ts_tp B HB). exact strtod_row_sat.strtod_sat_tp_A. Qed.

Lemma w_herrno : as_errno B = STRTOD_ERRNO.
Proof. rewrite (ts_errno B HB). exact strtod_row_sat.strtod_sat_errno_A. Qed.

Lemma w_hown : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros a Ha. rewrite (ts_owned B HB). rewrite (ts_errno B HB) in Ha.
exact (strtod_row_sat.strtod_sat_owned_A a Ha).
Qed.

Lemma w_hpst : forall z, Exists (in_zr z) (@prh_pst prh_img_A) ->
  in_img SEGS z /\ ~ (as_errno B <= z < as_errno B + 4).
Proof.
intros z Hz. split; [exact (pst_in_img_A z Hz)|].
assert (Hb : pst_allb (fun a => negb ((TFIB_ERRNO <=? a) && (a <? TFIB_ERRNO + 4))) (@prh_pst prh_img_A) = true)
  by (vm_compute; reflexivity).
pose proof (pst_allb_sound _ _ z Hb Hz) as H. cbv beta in H. rewrite (ts_errno B HB). intros [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. rewrite H1, H2 in H. discriminate H.
Qed.

Lemma w_hgotc : forall ly, In (z8 (ANum STRTOD_GOT_GUARD) STRTOD_GUARD) (as_const B ly).
Proof.
intros ly. replace STRTOD_GOT_GUARD with A_GOT_CANARY by (vm_compute; reflexivity).
replace STRTOD_GUARD with V_GOT_CANARY by (vm_compute; reflexivity).
exact (canary_cell_in B HB ly).
Qed.
End b.

(* ev_number at the real image-A instance: every image premise discharged by its witness *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

Lemma ev_number_A :
  AR_laws_x SEGS B ARx cf_head ->
  S8aNumCut.ev_blk_offimg B ARx strtod_row.strtod_img_A ->
  S8aNumCut.ev_frm_offimg ARx strtod_row.strtod_img_A ->
  (forall fx1, YGcallMxmn.aintrin_realizes_xm (fx := fx1) SEGS B ARx OCpy (pa_sigma AS___asan_memcpy)) ->
  (forall fx1, YGcallMxmn.astrcmp_realizes_xrom (fx := fx1) SEGS B ARx pa_relro_lo pa_relro_hi
     (pa_sigma AS___wrap_strcmp)) ->
  (forall fx1, YGcallMxmn.abcmp_realizes_xm (fx := fx1) SEGS B ARx (pa_sigma AS___wrap_bcmp)) ->
  (forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> n < 2 ^ 32) ->
  (forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
     YGcallMx.amem_range8 p (req_size n)) ->
  S8aIface.ev_number_spec B ARx SK.
Proof.
intros LAWS HOFFB HOFFF CPY CMP BCMP HBLK32 HAMEM8.
exact (ev_number B ARx SK LAWS w_himg w_hhead (w_hpst B HB) (w_htp B HB) (w_herrno B HB) (w_hown B HB)
  HOFFB HOFFF (w_hgotc B HB) CPY CMP BCMP HBLK32 HAMEM8).
Qed.
End i.
