(* Theorem Labs, 2026-10: fuzz_preset, image A' (asan #102 pin 1be0f53d96cb, unstripped twin bff8519bbe3e): put's walk
   (S7a_put.v put_holds, the kit's text tput_specX at the cut 7cdbb61b5fa0) AT THE A' INSTANCE, with the __asan_memcpy row
   CITED (owner order 14:33Z; a Theorem Labs lane's row of record).
   rule 24: no function proved. rule 24: proves no function (kind: instance corollary citing proved rows).
   put_holds_A_inst is put_holds at
   - PA := PI_prog_A (L := A_prog_listing), PI := prh_img_A, B := AD2l.TfibB (the #102 A' runtime symbol record),
     cp := CfParams_preset, RL := prh_room_live_a8;
   - ARx := ARcf /\ xs_placed_cf over PI_prog_A's segments (YGcallcf.ARxs, the relation of record of the A' consumers,
     Cno102A_TopA.v's ARcfx);
   with:
   - LAWS by YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (put_laws_A);
   - TL by PALibA.palib_A;
   - AMC by a Theorem Labs lane's lib/A/PRowCpy.v prow_asan_memcpy_xm_A (any ARx with its laws, at pc_asan_memcpy (as_code B)),
     its TfibSyms by AD2l.TfibB_syms; the pc is the listing's __asan_memcpy by put_A_memcpy_pc (vm_compute on a CLOSED
     goal over lib/A/AF0l.v Tfib_code and PAImg_prog.A_prog_sigma), the segments are lib/A/AB1v.v tfibsegs by
     conversion (put_inst_segs: PI_prog_A's segments ARE lib/A/Img0's rsegs);
   - Hent / Hobj / HPST / HW / HPSTRO / HZSA / HPAB by S7a_put_wit.v's s7p_ent_A / s7p_obj_A / s7p_pst_A /
     s7p_head_wide / s7p_pstro_A / s7p_zs_aligned_A / s7p_pab_A;
   - HCAP (the instance's hull caps are at least preset's) at cp := CfParams_preset by reflexivity.
   The texts are lib/A/PRH_FnAlloc.v's and lib/A/PRH_FnWriter.v's after the re-hiding move.
   The three premises left, by name: HREAL (the kit's tfuzz_realloc_specX at this instance; the realloc walk), HIMGSH
   (ARx_img_shadow_vis) and HFRSH (ARx_frame_hull_vis) at this relation.
   NAME GUARD: the instance's listing, segments and sigma are FULLY QUALIFIED (IMG_*_A; the short Img0 may resolve to
   the PLAIN image). No numeral; no ADDRESS typed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop YK1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset CfImgA AF0l AD2l AB1v PALibA PRowCpy
  PRH_FnAlloc PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_HShadow S7a_put S7a_put_wit.
Open Scope Z_scope.

(* the #102 A' listing, segments, sigma and code record, FULLY QUALIFIED (never the plain lib/Img0.v / plain listing) *)
#[local] Notation IMG_SEGS_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs.
#[local] Notation IMG_LST_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Listing_prog.A_prog_listing.
#[local] Notation IMG_PI_A := (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_prog.PI_prog_A).
#[local] Notation IMG_SIGMA_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_prog.A_prog_sigma.
#[local] Notation IMG_CODE_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AF0l.Tfib_code.
#[local] Notation IMG_TFIBSEGS_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AB1v.tfibsegs.
#[local] Notation CP := CfParamsPreset.CfParams_preset.

(* ---- closed check (vm_compute on a closed goal) ---- *)
(* the __asan_memcpy entry of TfibB's code record is the listing's __asan_memcpy *)
Lemma put_A_memcpy_pc : pc_asan_memcpy IMG_CODE_A = IMG_SIGMA_A AS___asan_memcpy.
Proof. vm_compute. reflexivity. Qed.

Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Notation SEGS_A := (@pa_segs rc IMG_LST_A (IMG_PI_A rc)).
(* ARcf takes the image's CfImg (the Section's ci) before cp *)
#[local] Notation ARCFX := (fun ly S Hp W mem md =>
  @YG0ncf.ARcf rc CfImgA.CfImg_A CP (@pa_segs rc IMG_LST_A (IMG_PI_A rc)) AD2l.TfibB ly S Hp W mem md /\
  @YG0ncf.xs_placed_cf rc ly S).
#[local] Notation RL_A := (@prh_room_live_a8 CP).

(* THE GUARD: the instance's segments ARE lib/A/Img0's rsegs (the #102 A' image) *)
Lemma put_inst_segs : SEGS_A = IMG_SEGS_A.
Proof. reflexivity. Qed.

(* LAWS at ARcf /\ xs_placed_cf *)
Lemma put_laws_A : AR_laws_x SEGS_A AD2l.TfibB ARCFX (@cf_head CP).
Proof. exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS_A AD2l.TfibB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS_A AD2l.TfibB)). Qed.

(* AMC: the __asan_memcpy row at ARcf /\ xs_placed_cf (PRowCpy.prow_asan_memcpy_xm_A) *)
Lemma put_amc_A :
  YGcallMxmn.aintrin_realizes_xm (fx := fx) SEGS_A AD2l.TfibB ARCFX OCpy
    (@pa_sigma rc IMG_LST_A (IMG_PI_A rc) AS___asan_memcpy).
Proof.
change (@pa_sigma rc IMG_LST_A (IMG_PI_A rc) AS___asan_memcpy) with (IMG_SIGMA_A AS___asan_memcpy).
rewrite <- put_A_memcpy_pc.
change IMG_CODE_A with (as_code AD2l.TfibB).
change SEGS_A with IMG_TFIBSEGS_A.
exact (PRowCpy.prow_asan_memcpy_xm_A (fx := fx) AD2l.TfibB _ _
  (YGcallcf.AR_laws_x_xs (cp := CP) IMG_TFIBSEGS_A AD2l.TfibB (YG0lawscf.AR_laws_ok_cf (cp := CP) IMG_TFIBSEGS_A AD2l.TfibB))
  AD2l.TfibB_syms).
Qed.

(* put's top at the A' instance: AMC cited, HCAP by reflexivity; HREAL, HIMGSH, HFRSH stay premises *)
Theorem put_holds_A_inst : forall (CTX0 : list (list Z)),
  @PRH_FnAlloc.tfuzz_realloc_specX fx rc ci CP prh_img_A RL_A IMG_LST_A (IMG_PI_A rc) AD2l.TfibB ARCFX SK ->
  PRW_HShadow.ARx_img_shadow_vis SEGS_A ARCFX ->
  PRW_HShadow.ARx_frame_hull_vis SEGS_A ARCFX ->
  @PRH_FnWriter.tput_specX fx rc ci CP prh_img_A RL_A IMG_LST_A (IMG_PI_A rc) AD2l.TfibB ARCFX SK CTX0.
Proof.
intros CTX0 HREAL HIMGSH HFRSH.
exact (@S7a_put.put_holds fx rc ci CP RL_A SK (IMG_PI_A rc) AD2l.TfibB ARCFX put_laws_A PALibA.palib_A
  S7a_put_wit.s7p_ent_A S7a_put_wit.s7p_obj_A CTX0 HREAL put_amc_A HIMGSH HFRSH
  S7a_put_wit.s7p_pst_A S7a_put_wit.s7p_head_wide S7a_put_wit.s7p_pstro_A S7a_put_wit.s7p_zs_aligned_A
  S7a_put_wit.s7p_pab_A (conj (Z.le_refl _) (Z.le_refl _))).
Qed.
End inst.

Print Assumptions put_holds_A_inst.
(* the wrong-image check: every PA / L / PI argument names image A' (PI_prog_A, A_prog_listing, prh_img_A) *)
Set Printing Implicit.
Unset Printing Notations.
Check @put_holds_A_inst.
Set Printing Notations.
Unset Printing Implicit.
