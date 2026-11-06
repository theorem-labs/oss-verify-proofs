(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane; asked by a Theorem Labs lane 15:05Z for its A' driver top). fuzz_preset, image A' (asan #102):
   six premises of S8aTop.ex_value_A that had no lemma at the binding of record, each stated at that binding:
   B := AD2l.TfibB, PA := PI_prog_A, L := A_prog_listing, cp := CfParamsPreset.CfParams_preset and
   ARx := ARcf /\ xs_placed_cf over PI_prog_A's segments (YGcallcf.v's ARxs). Each lemma's text is S8aTop.v's Section
   hypothesis of the same name at that binding. Proves nothing about the program (no function walked).
   - s8i_ASM1 (ASM1): lib/A/FCm01xm.v stack_malloc1_contract_xm at ARcf tfibsegs TfibB (fs_iface from
     FCifaceCf.fs_iface_ARcf of YG0lawscf.AR_laws_ok_cf), lifted to ARxs by YGcallMxmn.astack_malloc_realizes_xm_conj
     (xs_placed_cf is kept by set_fs: YGcallScf.xs_placed_cf_set_fs); the image-A twin of lib/AU/FCxmCfxB.v's
     stack_malloc1_contract_xm_cfx_B;
   - s8i_UAR_CELL (UAR_CELL): computed from the record (AD2l.v as_uar_cell, PAImg_prog.v A_prog_val), as
     lib/B/Prog/ExvB_ImgFacts.v exvi_eh_uar_cell at B';
   - s8i_HOFFF (HOFFF): a live fake frame lies above ly_img (AR_laws_x field alx_img, YCbqG.frm_above_band_x), and
     ly_img ends at or above the A' image's last segment (ALedger_cf's alc_img on Asan_segment_003, as
     FuzzFree.ff_blk_off_img), which ends at or above strtod_img_A's si_globals_top (by computation);
   - s8i_HBLK32 (HBLK32): YGcfBlockRange.ablock_n_lt_max_cf, with cf_malloc_max < 2 ^ 32 at CfParams_preset by
     computation, as ExvB_ImgFacts.v exvi_eh_blk32;
   - s8i_HAMEM8 (HAMEM8, the req_size form) and s8i_HAM8 (HAM8, the k-form): YGcfBlockRange.block_amem_range8_cf through
     ablocks = map (sptr_addr ..) blocks, as ExvB_ImgFacts.v exvi_eh_blk_amem8.
   rule 24: no function proved (kind: closed instance facts at preset's image A' binding). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface FCifaceCf YG0ncf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallScf YGcallcf YGcfBlockRange YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB1v AD2l AF0m FCm01xm CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require strtod_row S8aNumCut.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := AD2l.TfibB.

Section a. Context {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
(* the binding's allocator relation (YGcallcf.v ARxs at TfibB, preset's CfParams) *)
#[local] Abbreviation ARX := (fun ly S Hp (W : world SEGS) mem md =>
  ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ xs_placed_cf ly S).

(* ASM1 (S8aEntry.v:135) at the binding *)
Corollary s8i_ASM1 : forall fx1 : YK11.FPState, @YGcallMxmn.astack_malloc_realizes_xm fx1 SEGS TB ARX 1.
Proof.
intros fx1. change SEGS with AB1v.tfibsegs.
exact (astack_malloc_realizes_xm_conj (fx := fx1) AB1v.tfibsegs TB (ARcf (cp := CP) AB1v.tfibsegs TB)
  (fun ly S => xs_placed_cf ly S) 1 YGcallScf.xs_placed_cf_set_fs
  (FCm01xm.stack_malloc1_contract_xm (fx := fx1) TB (ARcf (cp := CP) AB1v.tfibsegs TB)
    (fs_iface_ARcf (cp := CP) AB1v.tfibsegs TB (AR_laws_ok_cf (cp := CP) AB1v.tfibsegs TB)) AD2l.TfibB_syms)).
Qed.

(* UAR_CELL (S8aEntry.v:153) at the binding: the record's values *)
Lemma s8i_UAR_CELL :
  4096 <= as_uar_cell TB /\ as_uar_cell TB + 4 <= kLowMemEnd /\
  (as_uar_cell TB + 4 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= as_uar_cell TB) /\
  (as_uar_cell TB + 4 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= as_uar_cell TB) /\
  (as_uar_cell TB + 4 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= as_uar_cell TB).
Proof.
let v := eval vm_compute in (as_uar_cell TB) in assert (U : as_uar_cell TB = v) by (vm_compute; reflexivity).
let v := eval vm_compute in (VAL (A_OBJ 0)) in assert (V0 : VAL (A_OBJ 0) = v) by (vm_compute; reflexivity).
let v := eval vm_compute in (VAL (A_OBJ 1)) in assert (V1 : VAL (A_OBJ 1) = v) by (vm_compute; reflexivity).
let v := eval vm_compute in (VAL (A_OBJ 12)) in assert (V12 : VAL (A_OBJ 12) = v) by (vm_compute; reflexivity).
rewrite U, V0, V1, V12. unfold kLowMemEnd. lia.
Qed.

(* HBLK32 (S8aNumber.v:90) at the binding *)
Lemma s8i_HBLK32 : forall ly S Hp W mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TB ly S) -> n < 2 ^ 32.
Proof.
intros ly S Hp W mem md p n [HA _] Hin.
destruct (YGcfBlockRange.ablock_n_lt_max_cf (cp := CP) SEGS TB ly S Hp W mem md p n HA Hin) as [_ Hn].
assert (Hmax : @cf_malloc_max CP < 2 ^ 32) by (vm_compute; reflexivity). lia.
Qed.

(* HAM8 (S8aStr.v:133) at the binding: the k-form *)
Lemma s8i_HAM8 : forall ly S Hp W mem md p n k, ARX ly S Hp W mem md -> In (p, n) (ablocks TB ly S) -> 0 <= k <= n ->
  YGcallMx.amem_range8 p (k + 1).
Proof.
intros ly S Hp W mem md p n k [HA _] Hin Hk. unfold ablocks in Hin.
apply in_map_iff in Hin as ([p0 n0] & E & Hin). cbn [fst snd] in E. injection E as <- <-.
exact (YGcfBlockRange.block_amem_range8_cf (cp := CP) SEGS TB ly S Hp W mem md p0 n0 k HA Hin Hk).
Qed.

(* HAMEM8 (S8aNumber.v:94) at the binding: the req_size form (req_size n = n + 1 - 1 for 0 < n, 1 for n = 0) *)
Lemma s8i_HAMEM8 : forall ly S Hp W mem md p n, ARX ly S Hp W mem md -> In (p, n) (ablocks TB ly S) ->
  YGcallMx.amem_range8 p (req_size n).
Proof.
intros ly S Hp W mem md p n HA Hin.
destruct HA as [HA0 _]. unfold ablocks in Hin.
apply in_map_iff in Hin as ([p0 n0] & E & Hin). cbn [fst snd] in E. injection E as <- <-.
destruct (YGcfBlockRange.block_user_range_cf (cp := CP) SEGS TB ly S Hp W mem md p0 n0 HA0 Hin) as (Hn & _).
unfold req_size. destruct (Z.eqb_spec n0 0) as [-> | Hne].
- exact (YGcfBlockRange.block_amem_range8_cf (cp := CP) SEGS TB ly S Hp W mem md p0 0 0 HA0 Hin ltac:(lia)).
- pose proof (YGcfBlockRange.block_amem_range8_cf (cp := CP) SEGS TB ly S Hp W mem md p0 n0 (n0 - 1) HA0 Hin
    ltac:(lia)) as H8.
  replace (n0 - 1 + 1) with n0 in H8 by lia. exact H8.
Qed.

(* HOFFF (S8aNumber.v:75) at the binding *)
Lemma s8i_HOFFF : S8aNumCut.ev_frm_offimg ARX strtod_row.strtod_img_A.
Proof.
intros ly S Hp W mem md cid pos HAR Hin.
pose proof HAR as ((_ & LG & _) & _).
pose proof (alc_img _ _ _ _ LG Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ C2].
cbn in C2.
let v := eval vm_compute in (YStrtodRowX.si_globals_top strtod_row.strtod_img_A) in
  assert (G : YStrtodRowX.si_globals_top strtod_row.strtod_img_A = v) by (vm_compute; reflexivity).
rewrite G.
pose proof (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (AR_laws_ok_cf (cp := CP) SEGS TB)) as LW.
apply (YCbqG.frm_above_band_x SEGS TB ARX LW ly S Hp W mem md _ cid pos HAR); [lia | exact Hin].
Qed.
End a.
