(* Theorem Labs, 2026-10: the image-B twin of lib/A/FCxmCfx.v: the frame-area contracts with the memnorm keep of
   fuzz_preset's ASan-UBSan image B at ARcfx (ARcf with the error-buffer extents placed, YGcallcf.v ARxs) over the B'
   program instance lib/B/PAImg_prog.v PI_prog_B, for any B with TfibSyms B (the B' instance takes B := YD2l.TfibB and
   TfibSyms from proj2 YD2l.TfibB_pair). Hand-written by the module map that gen_fc_b.py applies (lib/AU/FCf5xm.v:1; A<x> -> Y<x>,
   FCimg -> FCimgB, lib.A FCm3xm / FCf5xm -> lib.AU) plus the program instance A -> B (lib.A Listing_prog / PAImg_prog -> lib.B,
   A_prog_listing / PI_prog_A -> B_prog_listing / PI_prog_B), which the generator has no rule for, plus the _B suffix on both corollaries
   (:41, :51) and the added class-1 corollary stack_malloc1_contract_xm_cfx_B (:64-81, with its Requires YD2l / Img0 / CfParamsPreset /
   FCm01xm, :28, :32-34); no other code change. The texts are those of the Section hypotheses ASM3 (class 3) and SS5M (__asan_set_shadow_f5,
   value 245) of the A' walks (lib/A/Prog/Cno102A_EC.v:80, Cno102A_FE.v:276), at SEGS := pa_segs PI_prog_B and SIGMA := pa_sigma PI_prog_B.
   - stack_malloc3_contract_xm_cfx_B: lib/AU/FCm3xm.v stack_malloc3_contract_xm at ARx := ARcf tfibsegs B (fs_iface from
     FCifaceCf.fs_iface_ARcf of YG0lawscf.AR_laws_ok_cf), lifted to ARcfx by YGcallMxmn.astack_malloc_realizes_xm_conj
     (xs_placed_cf is kept by set_fs: YGcallScf.xs_placed_cf_set_fs);
   - set_shadow_f5_contract_xm_cfx_B: lib/AU/FCf5xm.v set_shadow_f5_contract_xm the same way, lifted by
     YGcallMxmn.aset_shadow_realizes_xm_conj.
   pa_segs PI_prog_B is lib/B/Img0.v rsegs, the same term as YB1v.tfibsegs (AsanUbsan.M.loaded_segments), and
   pa_sigma PI_prog_B AS___asan_set_shadow_f5 is FCimgB.SET_SHADOW_F5: both by conversion (change below).
   - stack_malloc1_contract_xm_cfx_B: the class-1 contract in the form ex_value B' takes it, the text of HSM1 of
     lib/B/Prog/ExvB_Inst.v:69 / :140 (:70 / :141 at bd31252bee60, as history): at rsegs (lib/B/Img0.v),
     B := YD2l.TfibB and its ARXS (ARcf at cp := CfParamsPreset.CfParams_preset, with xs_placed_cf), for every fx.
     It is lib/AU/FCm01xm.v stack_malloc1_contract_xm at ARx := ARcf tfibsegs TfibB, TfibSyms from
     proj2 YD2l.TfibB_pair, lifted by YGcallMxmn.astack_malloc_realizes_xm_conj as above.
   This file Requires lib/B/PAImg_prog.v, whose certificate checks the #102 B' bytes: it builds on the pins102 route
   only. Numerals: 1 and 3 (the classes), 245 (= 0xf5, the shadow value of the text). No ADDRESS. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YGcfNames YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface FCifaceCf YG0ncf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallScf YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import FCimgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require FCm01xm FCm3xm FCf5xm.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
#[local] Abbreviation SEGS := (@pa_segs rc B_prog_listing PI_prog_B).
#[local] Abbreviation SIGMA := (@pa_sigma rc B_prog_listing PI_prog_B).

Corollary stack_malloc3_contract_xm_cfx_B : forall B, TfibSyms B ->
  astack_malloc_realizes_xm (fx := fx) SEGS B
    (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S) 3.
Proof.
  intros B TB. change SEGS with tfibsegs.
  exact (astack_malloc_realizes_xm_conj tfibsegs B (ARcf tfibsegs B) (fun ly S => xs_placed_cf ly S) 3
    YGcallScf.xs_placed_cf_set_fs
    (FCm3xm.stack_malloc3_contract_xm B (ARcf tfibsegs B) (fs_iface_ARcf tfibsegs B (AR_laws_ok_cf tfibsegs B)) TB)).
Qed.

Corollary set_shadow_f5_contract_xm_cfx_B : forall B, TfibSyms B -> forall fz : YK11.FPState,
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

(* lib/B/Img0.v's rsegs, fully qualified (the short name may resolve to the PLAIN lib/Img0.v) *)
#[local] Abbreviation RSEGS_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
Section h. Context {rc : YM05.RunCeil} {ci : CfImg}.

Corollary stack_malloc1_contract_xm_cfx_B : forall fx : YK11.FPState,
  astack_malloc_realizes_xm (fx := fx) RSEGS_B YD2l.TfibB
    (fun ly S Hp W mem md => ARcf (cp := CP) RSEGS_B YD2l.TfibB ly S Hp W mem md /\ xs_placed_cf ly S) 1.
Proof.
  intros fx. change RSEGS_B with tfibsegs.
  exact (astack_malloc_realizes_xm_conj (fx := fx) tfibsegs YD2l.TfibB (ARcf (cp := CP) tfibsegs YD2l.TfibB)
    (fun ly S => xs_placed_cf ly S) 1 YGcallScf.xs_placed_cf_set_fs
    (FCm01xm.stack_malloc1_contract_xm (fx := fx) YD2l.TfibB (ARcf (cp := CP) tfibsegs YD2l.TfibB)
      (fs_iface_ARcf (cp := CP) tfibsegs YD2l.TfibB (AR_laws_ok_cf (cp := CP) tfibsegs YD2l.TfibB))
      (proj2 YD2l.TfibB_pair))).
Qed.

End h.
