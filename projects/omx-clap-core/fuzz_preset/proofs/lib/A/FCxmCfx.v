(* Theorem Labs, 2026-10: the frame-area contracts with the memnorm keep of fuzz_preset's ASan image A in the form the
   #102 A' walks take them: at ARcfx (ARcf with the error-buffer extents placed, YGcallcf.v ARxs) over the A' program
   instance PAImg_prog.PI_prog_A, for any B with TfibSyms B. These are the texts of the Section hypotheses
   Cno102A_EC.v:77 ASM3 (CN_CID = 3, Cno102A_Base.v:122) and Cno102A_FE.v SS5M (c-omx-hpreset's cno A' top, R7-5) at
   SEGS := pa_segs PI_prog_A and SIGMA := pa_sigma PI_prog_A; the A' instance (Cno102A_TopA.v) takes B := AD2l.TfibB and
   TfibSyms from proj2 AD2l.TfibB_pair.
   - stack_malloc3_contract_xm_cfx: FCm3xm.stack_malloc3_contract_xm at ARx := ARcf tfibsegs B (fs_iface from
     FCifaceCf.fs_iface_ARcf of YG0lawscf.AR_laws_ok_cf), lifted to ARcfx by YGcallMxmn.astack_malloc_realizes_xm_conj
     (xs_placed_cf is kept by set_fs: YGcallScf.xs_placed_cf_set_fs), as PvB_Inst.v pvI_asm0 lifts class 0;
   - set_shadow_f5_contract_xm_cfx: FCf5xm.set_shadow_f5_contract_xm the same way, lifted by
     YGcallMxmn.aset_shadow_realizes_xm_conj (the text keeps S, so no law on xs_placed_cf is needed).
   pa_segs PI_prog_A is lib/A/Img0.v rsegs, the same term as AB1v.tfibsegs (Asan.M.loaded_segments), and
   pa_sigma PI_prog_A AS___asan_set_shadow_f5 is FCimg.SET_SHADOW_F5: both by conversion (change below).
   This file Requires PAImg_prog.v, whose certificate checks the #102 A' bytes: it builds on the pins102 route only.
   Numerals: 3 (the class), 245 (= 0xf5, the shadow value of the text). No ADDRESS. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YGcfNames YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface FCifaceCf YG0ncf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m FCimg Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require FCm3xm FCf5xm.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
#[local] Abbreviation SEGS := (@pa_segs rc A_prog_listing PI_prog_A).
#[local] Abbreviation SIGMA := (@pa_sigma rc A_prog_listing PI_prog_A).

Corollary stack_malloc3_contract_xm_cfx : forall B, TfibSyms B ->
  astack_malloc_realizes_xm (fx := fx) SEGS B
    (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S) 3.
Proof.
  intros B TB. change SEGS with tfibsegs.
  exact (astack_malloc_realizes_xm_conj tfibsegs B (ARcf tfibsegs B) (fun ly S => xs_placed_cf ly S) 3
    YGcallScf.xs_placed_cf_set_fs
    (FCm3xm.stack_malloc3_contract_xm B (ARcf tfibsegs B) (fs_iface_ARcf tfibsegs B (AR_laws_ok_cf tfibsegs B)) TB)).
Qed.

Corollary set_shadow_f5_contract_xm_cfx : forall B, TfibSyms B -> forall fz : YK11.FPState,
  @aset_shadow_realizes_xm fz SEGS B
    (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S) (SIGMA AS___asan_set_shadow_f5) 245.
Proof.
  intros B TB fz. change SEGS with tfibsegs. change (SIGMA AS___asan_set_shadow_f5) with SET_SHADOW_F5.
  exact (aset_shadow_realizes_xm_conj (fx := fz) tfibsegs B (ARcf tfibsegs B) (fun ly S => xs_placed_cf ly S)
    SET_SHADOW_F5 0xf5
    (FCf5xm.set_shadow_f5_contract_xm (fx := fz) B (ARcf tfibsegs B)
      (fs_iface_ARcf tfibsegs B (AR_laws_ok_cf tfibsegs B)) TB)).
Qed.

End a.
