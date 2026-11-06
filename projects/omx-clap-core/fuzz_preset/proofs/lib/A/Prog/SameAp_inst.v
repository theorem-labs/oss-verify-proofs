(* Theorem Labs, 2026-10: fuzz_preset, image A' (asan #102 pin 1be0f53d96cb, unstripped twin bff8519bbe3e), same:
   the walk at the instance of record (SameAp_final.v same_holds_Ap_TfibBx, the kit's text tsame_specX at the cut
   7cdbb61b5fa0) with its TWO runtime rows CITED, so no premise is left (owner order 14:33Z; rows of a Theorem Labs lane).
   rule 24: no function proved. rule 24: proves no function (kind: instance corollary citing proved rows).
   Instance: B := AD2l.TfibB, PA := PI_prog_A, RL := prh_room_live_a8, cp := CfParams_preset,
   ARx := ARcf /\ xs_placed_cf over lib/A/Img0's rsegs (SameAp_final.v's ARX / Cno102A_TopA.v's ARcfx).
   - HSTR (astrcmp_realizes_xrom at A_prog_relro_lo / A_prog_relro_hi, pc SMA_STRCMP): a Theorem Labs lane's lib/A/PSstrRo.v
     ps_strcmp_xrom_xs_A at AD2l.TfibB (TfibSyms AD2l.TfibB_syms), stated over lib/A/AB1v.v tfibsegs at
     cf_pc_strcmp CfImg_A: the pc is SMA_STRCMP by sai_strcmp_pc, the segments are the same by conversion.
   - HBCMP (abcmp_realizes_xm, pc SMA_BCMP): a Theorem Labs lane's lib/A/PRowCmp.v pr_bcmp_xm_A_pc (any ARx with its laws,
     at pc_wrap_bcmp (as_code B)), LAWS by YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf; the pc is SMA_BCMP by
     sai_bcmp_pc.
   Both pc facts are vm_compute on CLOSED goals over lib/A/CfImgA.v / lib/A/AF0l.v Tfib_code and
   PAImg_prog.A_prog_sigma (SameAp_defs.v SMA_STRCMP / SMA_BCMP).
   Two tops: same_holds_Ap_inst (every depth n, every sink head), and same_holds_Ap_HSAME_fit_s, the HSAME premise of
   Cno102A_Top.v in SameAp_final.v's fit form (same_holds_Ap_HSAME_fit) with no premise left.
   No numeral; no ADDRESS typed; no image-B module. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Img Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import SameAp_defs.
(* the instance and the rows: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset AD2l AF0l AB1v CfImgA PSstrRo PRowCmp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require SameAp_final.
Local Open Scope Z_scope.

(* the #102 A' segments, sigma, code record and CfImg, FULLY QUALIFIED (never the plain lib/Img0.v) *)
#[local] Notation IMG_SEGS_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs.
#[local] Notation IMG_LST_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Listing_prog.A_prog_listing.
#[local] Notation IMG_PI_A := (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_prog.PI_prog_A).
#[local] Notation IMG_CODE_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AF0l.Tfib_code.
#[local] Notation IMG_TFIBSEGS_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AB1v.tfibsegs.
#[local] Notation IMG_CFIMG_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.CfImgA.CfImg_A.
#[local] Notation CP := CfParamsPreset.CfParams_preset.

(* ---- closed checks (vm_compute on closed goals) ---- *)
(* CfImg_A's strcmp trampoline is the listing's __wrap_strcmp (SMA_STRCMP) *)
Lemma sai_strcmp_pc : @cf_pc_strcmp IMG_CFIMG_A = SMA_STRCMP.
Proof. vm_compute. reflexivity. Qed.
(* TfibB's bcmp trampoline is the listing's __wrap_bcmp (SMA_BCMP) *)
Lemma sai_bcmp_pc : pc_wrap_bcmp IMG_CODE_A = SMA_BCMP.
Proof. vm_compute. reflexivity. Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation ARX := (fun ly S Hp W mem md =>
  @YG0ncf.ARcf rc CfImgA.CfImg_A CP IMG_SEGS_A AD2l.TfibB ly S Hp W mem md /\ @YG0ncf.xs_placed_cf rc ly S).

(* THE GUARD: PI_prog_A's segments ARE lib/A/Img0's rsegs (the #102 A' image) *)
Lemma sai_segs : @pa_segs rc IMG_LST_A (IMG_PI_A rc) = IMG_SEGS_A.
Proof. reflexivity. Qed.

(* HSTR: the strcmp row at ARcf /\ xs_placed_cf (PSstrRo.ps_strcmp_xrom_xs_A) *)
Lemma sai_hstr : @astrcmp_realizes_xrom fx IMG_SEGS_A AD2l.TfibB ARX A_prog_relro_lo A_prog_relro_hi SMA_STRCMP.
Proof.
rewrite <- sai_strcmp_pc.
change IMG_SEGS_A with IMG_TFIBSEGS_A.
exact (PSstrRo.ps_strcmp_xrom_xs_A (fx := fx) (rc := rc) (cp := CP) AD2l.TfibB AD2l.TfibB_syms
  A_prog_relro_lo A_prog_relro_hi).
Qed.

(* HBCMP: the bcmp row at ARcf /\ xs_placed_cf (PRowCmp.pr_bcmp_xm_A_pc) *)
Lemma sai_hbcmp : @abcmp_realizes_xm fx IMG_SEGS_A AD2l.TfibB ARX SMA_BCMP.
Proof.
rewrite <- sai_bcmp_pc.
change IMG_CODE_A with (as_code AD2l.TfibB).
change IMG_SEGS_A with IMG_TFIBSEGS_A.
exact (PRowCmp.pr_bcmp_xm_A_pc (fx := fx) AD2l.TfibB _ _
  (YGcallcf.AR_laws_x_xs (cp := CP) IMG_TFIBSEGS_A AD2l.TfibB (YG0lawscf.AR_laws_ok_cf (cp := CP) IMG_TFIBSEGS_A AD2l.TfibB))
  AD2l.TfibB_syms).
Qed.

(* same's top at the A' instance, both runtime rows cited: no premise left (the relation spelled over PI_prog_A's
   segments, as the consumers spell it; = ARX by sai_segs) *)
Theorem same_holds_Ap_inst : forall (SK : YI16.sink_head) (n : nat),
  @tsame_specX fx rc CP prh_img_A (@prh_room_live_a8 CP) IMG_LST_A (IMG_PI_A rc) AD2l.TfibB
    (fun ly S Hp W mem md =>
       @YG0ncf.ARcf rc CfImgA.CfImg_A CP (@pa_segs rc IMG_LST_A (IMG_PI_A rc)) AD2l.TfibB ly S Hp W mem md /\
       @YG0ncf.xs_placed_cf rc ly S)
    SK n.
Proof.
intros SK n.
exact (@SameAp_final.same_holds_Ap_TfibBx fx rc CfImgA.CfImg_A SK sai_hstr sai_hbcmp n).
Qed.
End i.

(* ---- the HSAME fit (SameAp_final.v same_holds_Ap_HSAME_fit, Cno102A_Top.v's HSAME at Cno102A_TopA.v's instance, the
   segments spelled SEGS := pa_segs of PI_prog_A, every FPState) with both rows cited: no premise left ---- *)
Section fit. Context {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs rc IMG_LST_A (IMG_PI_A rc)).
#[local] Notation ARcfx := (fun ly S Hp W mem md =>
  @YG0ncf.ARcf rc CfImgA.CfImg_A CP SEGS AD2l.TfibB ly S Hp W mem md /\ @YG0ncf.xs_placed_cf rc ly S).

Example same_holds_Ap_HSAME_fit_s : forall (SK : YI16.sink_head) (n : nat) (fz : YK11.FPState),
  @tsame_specX fz rc CP prh_img_A (@prh_room_live_a8 CP) IMG_LST_A (IMG_PI_A rc) AD2l.TfibB ARcfx SK n.
Proof.
intros SK n fz.
exact (@SameAp_final.same_holds_Ap_HSAME_fit rc CfImgA.CfImg_A SK (fun fy => @sai_hstr fy rc) (fun fy => @sai_hbcmp fy rc) n fz).
Qed.
End fit.

Print Assumptions same_holds_Ap_inst.
Print Assumptions same_holds_Ap_HSAME_fit_s.
(* the wrong-image check: every PA / L / PI argument names image A' (PI_prog_A, A_prog_listing, prh_img_A) *)
Set Printing Implicit.
Unset Printing Notations.
Check @same_holds_Ap_inst.
Check @same_holds_Ap_HSAME_fit_s.
Set Printing Notations.
Unset Printing Implicit.
