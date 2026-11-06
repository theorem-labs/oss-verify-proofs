(* Theorem Labs, 2026-10: fuzz_preset, image B' (asan-ubsan, #102 pin d663f82d7f48, unstripped twin c90d4fa54d43):
   check_reject_clean at the B' live instance (CrcBInstLive.v check_reject_clean_holds_B_inst_live, the kit's text
   tcheck_reject_clean_specX at the cut 7cdbb61b5fa0) with the bcmp row CITED (lead's order 14:4xZ; row of
   a Theorem Labs lane).
   rule 24: no function proved. rule 24: proves no function (kind: instance corollary citing a proved row).
   Instance (CrcBInstLive.v's): B := YD2l.TfibB, PA := PI_prog_B (L := B_prog_listing), PI := prh_img_B,
   RL := prh_room_live_a8, cp := CfParams_preset, ARx := ARcf /\ xs_placed_cf over PI_prog_B's segments.
   - BCMP (abcmp_realizes_xm at the listing's __wrap_bcmp): a Theorem Labs lane's lib/AU/PRowCmp.v pr_bcmp_xm_B_pc (any ARx
     with its laws, at pc_wrap_bcmp (as_code B)), LAWS by YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (the term
     CrcBInstLive.v passes), TfibSyms by YD2l.TfibB_syms; the pc is the listing's __wrap_bcmp by cbi_bcmp_pc
     (vm_compute on a CLOSED goal over lib/Reusable/YF0l.v Tfib_code and PAImg_prog.B_prog_sigma), the segments are
     lib/Reusable/YB1v.v tfibsegs by conversion (cbi_segs: PI_prog_B's segments ARE lib/B/Img0's rsegs).
   The one premise left: cr_img_shadow_vis_B at ARcf (CrcB.v; owner a Theorem Labs lane, as in CrcBInstLive.v).
   NAME GUARD: the instance's listing, segments and sigma are FULLY QUALIFIED (IMG_*_B; never an image-A module).
   No numeral; no ADDRESS typed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YCbqG YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YGcallcf YG0lawscf YD2l YF0l YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PRowCmp CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require CrcB CrcBInstLive.
Open Scope Z_scope.

(* the #102 B' listing, segments, sigma and code record, FULLY QUALIFIED *)
#[local] Notation IMG_SEGS_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.
#[local] Notation IMG_LST_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Listing_prog.B_prog_listing.
#[local] Notation IMG_PI_B := (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_prog.PI_prog_B).
#[local] Notation IMG_SIGMA_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_prog.B_prog_sigma.
#[local] Notation IMG_CODE_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YF0l.Tfib_code.
#[local] Notation IMG_TFIBSEGS_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YB1v.tfibsegs.
#[local] Notation CP := CfParamsPreset.CfParams_preset.

(* ---- closed check (vm_compute on a closed goal) ---- *)
(* the bcmp trampoline of TfibB's code record is the listing's __wrap_bcmp *)
Lemma cbi_bcmp_pc : pc_wrap_bcmp IMG_CODE_B = IMG_SIGMA_B AS___wrap_bcmp.
Proof. vm_compute. reflexivity. Qed.

Section L. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs rc IMG_LST_B (IMG_PI_B rc)).
#[local] Notation ARcfx := (fun ly S Hp W mem md =>
  @ARcf rc CfImgB.CfImg_B CP (@pa_segs rc IMG_LST_B (IMG_PI_B rc)) YD2l.TfibB ly S Hp W mem md /\ @xs_placed_cf rc ly S).

(* THE GUARD: PI_prog_B's segments ARE lib/B/Img0's rsegs (the #102 B' image) *)
Lemma cbi_segs : SEGS = IMG_SEGS_B.
Proof. reflexivity. Qed.

(* BCMP: the bcmp row at ARcf /\ xs_placed_cf (PRowCmp.pr_bcmp_xm_B_pc) *)
Lemma cbi_bcmp :
  YGcallMxmn.abcmp_realizes_xm (fx := fx) SEGS YD2l.TfibB ARcfx (@pa_sigma rc IMG_LST_B (IMG_PI_B rc) AS___wrap_bcmp).
Proof.
change (@pa_sigma rc IMG_LST_B (IMG_PI_B rc) AS___wrap_bcmp) with (IMG_SIGMA_B AS___wrap_bcmp).
rewrite <- cbi_bcmp_pc.
change IMG_CODE_B with (as_code YD2l.TfibB).
change SEGS with IMG_TFIBSEGS_B.
exact (PRowCmp.pr_bcmp_xm_B_pc (fx := fx) YD2l.TfibB _ _
  (YGcallcf.AR_laws_x_xs (cp := CP) IMG_TFIBSEGS_B YD2l.TfibB (YG0lawscf.AR_laws_ok_cf (cp := CP) IMG_TFIBSEGS_B YD2l.TfibB))
  YD2l.TfibB_syms).
Qed.

(* the crc B' live instance, the bcmp row cited: cr_img_shadow_vis_B stays (owner a Theorem Labs lane) *)
Theorem check_reject_clean_holds_B_inst_bcmp : forall SK : YI16.sink_head,
  CrcB.cr_img_shadow_vis_B (fun ly S Hp W mem md => @ARcf rc CfImgB.CfImg_B CP SEGS YD2l.TfibB ly S Hp W mem md) ->
  tcheck_reject_clean_specX (cp := CP) (PI := prh_img_B) (RL := prh_room_live_a8 (cp := CP)) (L := IMG_LST_B)
    (PA := IMG_PI_B rc) YD2l.TfibB ARcfx SK.
Proof.
intros SK IV.
exact (CrcBInstLive.check_reject_clean_holds_B_inst_live (fx := fx) (rc := rc) SK cbi_bcmp IV).
Qed.
End L.

Print Assumptions check_reject_clean_holds_B_inst_bcmp.
(* the wrong-image check: every PA / L / PI argument names image B' (PI_prog_B, B_prog_listing, prh_img_B) *)
Set Printing Implicit.
Unset Printing Notations.
Check @check_reject_clean_holds_B_inst_bcmp.
Set Printing Notations.
Unset Printing Implicit.
