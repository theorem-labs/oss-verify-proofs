(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d7f488d30, twin c90d4fa54d43160b), lane
   PutStringB (h-rw-pre-7): the SATISFIABILITY WITNESS of the snprintf-instance premise text this lane wrote,
   PutStringB_E.ps_snp_inst, at the instance of record (PA := PI_prog_B, B := YD2l.TfibB, ARx := ARcfx = ARcf /\
   xs_placed_cf, ci := CfImgB.CfImg_B, cp := CfParamsPreset.CfParams_preset), AT THE VALUES THE ROW'S OWNER FIXES for
   image B' (h-mani-a8's lib/AU/CfApiPresetB.v:99-105 / CfSnprintfPresetB.v:29-36 / CfImgB.v:60-68 at
   origin/cold/h-mani-a8-alloc102 c0f0b489957b, read by the review SnpInstReview, 2026-10-29 22:2xZ):
   - the format band lo = cf_img_lo = the instance's pa_lo, hi = cf_got_stack_chk_guard = the stack guard's GOT cell
     (YE22.A_GOT_CANARY, B''s generated name);
   - the canary chain gc = that GOT cell, gv = cf_stack_chk_guard = the guard object (YE22.V_GOT_CANARY);
   - the image range img_lo / img_hi = cf_img_lo / cf_img_top = the instance's pa_lo / pa_hi;
   - cr = snp_cr segs, every non-writable segment of the image (psn_cr below, the same list by its definition);
   - the walk's own window Kp := STK_RT_PRINTF (the owner's K = snp_K_B = 8160 is below it).
   rule 24: no function proved (kind: instance discharge of a premise text).
   ps_snp_inst's state clauses are universally quantified over ARcfx states and proved here for EVERY such state, so
   no meter and no start state enter (the witness is not at a chosen state, and not at ameter_triv); its closed
   clauses are decided by vm_compute on closed goals. Citations: YG0ncf.amc_const + YE22.canary_cell_in (the GOT
   cell is a const cell of TfibB holding the guard's address, at every ARcf state); YE36.rdword_img_some +
   YE2y.val_mem_of_rdword (the guard object's 8 bytes are image bytes, readable at every state); PSstrRo.rom_view_B_cf
   (the read-only segments are viewed as the ROM wherever arodata_okP holds); YCbqG.img_band_x / frm_above_band_x
   with LAWS (PutStringB_Wit.psw_laws) (every live fake frame lies at or above the image's top).
   Numerals: 8 (LENGTH: a word, the canary cell width); 2608 + 5552 (LENGTH: the owner's snp_K_B, CfSnprintfPresetB.v:36,
   in psn_K_le only). No image ADDRESS is typed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FMsnprintfShared.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx YGcallMxmn YGcallSnp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallSnpCk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YB1v YE22 YE36 YE2y YD2l YG0ncf YP08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB PSstrRo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PutStringB_E PutStringB_Wit PutStringB_Inst.
From Stdlib Require Import List Bool.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {ci : CfImg}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance PRH_Base.prh_room_live_a8.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation RLO := (@pa_relro_lo _ B_prog_listing PI_prog_B).
#[local] Abbreviation RHI := (@pa_relro_hi _ B_prog_listing PI_prog_B).
#[local] Abbreviation PLO := (@pa_lo _ B_prog_listing PI_prog_B).
#[local] Abbreviation PHI := (@pa_hi _ B_prog_listing PI_prog_B).
#[local] Abbreviation ARcfx := (fun ly S Hp (W : world SEGS) mem md =>
  YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

(* the owner's cr: every non-writable segment of the image, as (base, size) (a8's snp_cr segs) *)
Definition psn_cr : list (Z * Z) :=
  map (fun sg => (Z.of_N (seg_base sg), Z.of_N (seg_size sg))) (filter (fun sg => negb (seg_writable sg)) SEGS).

(* the image's segments are the generated image's (YB1v.tfibsegs), by conversion *)
Lemma psn_segs : SEGS = YB1v.tfibsegs.
Proof. reflexivity. Qed.

(* the stack guard's GOT cell holds the guard object's address at every ARcf state (a const cell of TfibB) *)
Lemma psn_got_canary : forall ly S Hp W mem md, YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md ->
  val_mem SEGS (mrestrict (w_H W) mem) YE22.A_GOT_CANARY 8 YE22.V_GOT_CANARY.
Proof.
intros ly S Hp W mem md (M & _).
pose proof (proj1 (Forall_forall _ _) (YG0ncf.amc_const _ _ _ _ _ M) _ (YE22.canary_cell_in TB YD2l.TfibB_syms ly)) as C.
unfold cell_holds in C. cbn [c_at c_val c_w z8 c8 aeval] in C.
intros k Hk. pose proof (C k Hk) as Ck. unfold aview in Ck.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (YE22.A_GOT_CANARY + Z.of_nat k)) as [b|]; [|discriminate Ck].
cbn [option_map] in Ck. injection Ck as Ck. f_equal. apply bv_eq. rewrite Ck, Z_to_bv_unsigned.
do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). clear - Hk; lia.
Qed.

(* the guard object's 8 bytes are image bytes, so readable at every state *)
Lemma psn_guard_readable : forall (W : world SEGS) mem,
  exists cval, val_mem SEGS (mrestrict (w_H W) mem) YE22.V_GOT_CANARY 8 cval.
Proof.
intros W mem.
destruct (YE36.rdword_img_some (w_H W) mem YE22.V_GOT_CANARY ltac:(vm_compute; reflexivity)) as (cv & Hcv & _).
exists cv. exact (YE2y.val_mem_of_rdword (w_H W) mem _ _ Hcv).
Qed.

(* every range of the owner's cr is a non-writable segment, of positive size *)
Lemma psn_cr_seg : forall r, In r psn_cr ->
  exists sg, In sg SEGS /\ seg_writable sg = false /\ r = (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) /\
    0 < Z.of_N (seg_size sg).
Proof.
assert (P : forallb (fun sg => 0 <? Z.of_N (seg_size sg)) (filter (fun sg => negb (seg_writable sg)) SEGS) = true)
  by (vm_compute; reflexivity).
intros r Hr. unfold psn_cr in Hr. apply in_map_iff in Hr as (sg & <- & Hsg).
pose proof (proj1 (forallb_forall _ _) P sg Hsg) as Hp. apply Z.ltb_lt in Hp.
apply filter_In in Hsg as (Hsg & Hw). apply negb_true_iff in Hw.
exists sg. split; [exact Hsg|]. split; [exact Hw|]. split; [reflexivity | exact Hp].
Qed.

(* THE WITNESS *)
Theorem ps_snp_inst_B :
  PutStringB_E.ps_snp_inst (PA := PI_prog_B) TB ARcfx STK_RT_PRINTF PLO YE22.A_GOT_CANARY YE22.A_GOT_CANARY
    YE22.V_GOT_CANARY PLO PHI psn_cr.
Proof.
unfold PutStringB_E.ps_snp_inst.
(* the window: ESTACK <= STK_RT_PRINTF <= STK_RT_PRINTF *)
split; [split; apply Z.leb_le; vm_compute; reflexivity|].
(* the two formats lie in the band [cf_img_lo, the GOT cell) *)
split; [apply Z.leb_le; vm_compute; reflexivity|].
split; [apply Z.leb_le; vm_compute; reflexivity|].
split; [apply Z.leb_le; vm_compute; reflexivity|].
split; [apply Z.leb_le; vm_compute; reflexivity|].
(* the canary cells are image bytes *)
split.
{ intros j Hj. split.
  - apply (PutStringB_Wit.psw_img_range_sound SEGS YE22.A_GOT_CANARY 8 ltac:(vm_compute; reflexivity)).
    cbn. clear - Hj; lia.
  - apply (PutStringB_Wit.psw_img_range_sound SEGS YE22.V_GOT_CANARY 8 ltac:(vm_compute; reflexivity)).
    cbn. clear - Hj; lia. }
(* at every ARcfx state: the canary chain, and the read-only ranges viewed as the ROM wherever arodata_okP holds *)
split.
{ intros ly S Hp W mem md (HAR & _). split.
  - destruct (psn_guard_readable W mem) as (cv & Hcv).
    exists cv. split; [exact (psn_got_canary ly S Hp W mem md HAR) | exact Hcv].
  - intros HRO a Ha.
    pose proof (PSstrRo.rom_view_B_cf TB YD2l.TfibB_syms RLO RHI ly S Hp W mem md HAR HRO) as RV.
    apply RV. apply Exists_exists in Ha as (r & Hr & Hz).
    destruct (psn_cr_seg r Hr) as (sg & Hsg & Hw & -> & _).
    unfold in_zr in Hz. cbn [fst snd] in Hz.
    exists sg. split; [exact Hsg|]. split; [exact Hw | exact Hz]. }
(* the ranges of cr: positive and in the image *)
split.
{ apply Forall_forall. intros r Hr. destruct (psn_cr_seg r Hr) as (sg & Hsg & _ & -> & Hpos).
  cbn [fst snd]. split; [exact Hpos|]. intros a Ha. exists sg. split; [exact Hsg | exact Ha]. }
(* every live fake frame lies at or above the image's top (LAWS field 17, at the last segment's end) *)
intros ly S Hp W mem md cid pos HAR Hin. left.
assert (HL : exists sg, In sg SEGS /\ Z.of_N (seg_base sg) <= PLO).
{ assert (E : existsb (fun sg => Z.of_N (seg_base sg) <=? PLO) SEGS = true) by (vm_compute; reflexivity).
  apply existsb_exists in E as (sg & Hsg & E). exists sg. split; [exact Hsg | apply Z.leb_le; exact E]. }
assert (HH : exists sg, In sg SEGS /\ PHI <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg)).
{ assert (E : existsb (fun sg => PHI <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) SEGS = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in E as (sg & Hsg & E). exists sg. split; [exact Hsg | apply Z.leb_le; exact E]. }
apply (YCbqG.frm_above_band_x SEGS TB ARcfx PutStringB_Wit.psw_laws ly S Hp W mem md PHI cid pos HAR); [|exact Hin].
exact (proj2 (YCbqG.img_band_x SEGS TB ARcfx PutStringB_Wit.psw_laws ly S Hp W mem md PLO PHI HAR HL HH)).
Qed.

(* the owner's K = snp_K_B = 2608 + 5552 (CfSnprintfPresetB.v:36) fits the walk's window: the theorem's K <= Kp *)
Lemma psn_K_le : 2608 + 5552 <= STK_RT_PRINTF.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
End s.

(* ---- the theorem with the snprintf premise AT THE OWNER'S VALUES: ps_snp_inst discharged by ps_snp_inst_B, so the
   only snprintf premise left is the owner's row text itself (any K within the walk's window) ---- *)
Section c. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {ci : CfImg}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance PRH_Base.prh_room_live_a8.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).
#[local] Abbreviation RLO := (@pa_relro_lo _ B_prog_listing PI_prog_B).
#[local] Abbreviation RHI := (@pa_relro_hi _ B_prog_listing PI_prog_B).
#[local] Abbreviation PLO := (@pa_lo _ B_prog_listing PI_prog_B).
#[local] Abbreviation PHI := (@pa_hi _ B_prog_listing PI_prog_B).
#[local] Abbreviation ARcfx := (fun ly S Hp (W : world SEGS) mem md =>
  YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

Theorem put_string_holds_B_owner : forall (CTX0 : list (list Z)),
  (forall fz : YK11.FPState, tput_specX (fx := fz) (ci := CfImgB.CfImg_B) (cp := CP) (PI := prh_img_B)
     (RL := PRH_Base.prh_room_live_a8) (L := B_prog_listing) (PA := PI_prog_B) TB ARcfx SK CTX0) ->
  (forall fz : YK11.FPState, astack_malloc_realizes_xm (fx := fz) SEGS TB ARcfx 0) ->
  (forall fz : YK11.FPState, aintrin_realizes_xm (fx := fz) SEGS TB ARcfx OCpy (SIGMA AS___asan_memcpy)) ->
  (* __wrap_snprintf's row text at the owner's B' values (format band [cf_img_lo, the guard's GOT cell), canary chain
     GOT cell -> guard object, image range [cf_img_lo, cf_img_top), cr = the read-only segments), any K <= the window *)
  forall K, K <= STK_RT_PRINTF ->
  (forall fz : YK11.FPState, asnprintf_realizes_xrom (fx := fz) SEGS TB ARcfx RLO RHI
     (YGcallSnpCk.FF_esc PLO YE22.A_GOT_CANARY) K YE22.A_GOT_CANARY YE22.V_GOT_CANARY PLO PHI psn_cr
     (SIGMA AS___wrap_snprintf)) ->
  forall fe : YK11.FPState,
  tput_string_specX (fx := fe) (ci := CfImgB.CfImg_B) (cp := CP) (PI := prh_img_B) (RL := PRH_Base.prh_room_live_a8)
    (L := B_prog_listing) (PA := PI_prog_B) TB ARcfx SK CTX0.
Proof.
intros CTX0 PUT ASM0 AMCPY K HK ASNP fe.
refine (PutStringB_Inst.put_string_holds_B CTX0 PUT ASM0 AMCPY _ fe).
exists K, STK_RT_PRINTF, PLO, YE22.A_GOT_CANARY, YE22.A_GOT_CANARY, YE22.V_GOT_CANARY, PLO, PHI, psn_cr.
split; [exact HK|]. split; [|exact ASNP].
exact ps_snp_inst_B.
Qed.
End c.

Locate ps_snp_inst_B. Print Assumptions ps_snp_inst_B.
Locate put_string_holds_B_owner. Print Assumptions put_string_holds_B_owner.
