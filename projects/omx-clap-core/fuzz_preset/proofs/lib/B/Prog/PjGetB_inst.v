(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B' (asan-ubsan, #102 pin d663f82d7f48, unstripped twin c90d4fa54d43):
   pj_get and pj_get_str at the unit's image instance (PjGetB.v pj_get_holds_B_top / pj_get_str_holds_B_top, the kit's
   texts tpj_get_specX / tpj_get_str_specX at the cut 7cdbb61b5fa0) with the strcmp row CITED, so no premise is left
   (owner order 14:33Z; row of a Theorem Labs lane).
   rule 24: no function proved. rule 24: proves no function (kind: instance corollary citing a proved row).
   Instance (the tops'): B := YD2l.TfibB, PA := PI_prog_B (L := B_prog_listing), PI := prh_img_B,
   cp := CfParams_preset, ARx := plain ARcf over PI_prog_B's segments (the tops' ARI).
   - ASC (astrcmp_realizes_xrom at PI_prog_B's relro bounds, pc pa_sigma AS___wrap_strcmp of PI_prog_B): a Theorem Labs lane's
     lib/AU/PSstrRo.v ps_strcmp_xrom_B at YD2l.TfibB (TfibSyms YD2l.TfibB_syms), stated over lib/Reusable/YB1v.v
     tfibsegs at cf_pc_strcmp CfImg_B: the pc is the listing's __wrap_strcmp by pgi_strcmp_pc (vm_compute on a CLOSED
     goal over lib/AU/CfImgB.v and PAImg_prog.B_prog_sigma), the segments are PI_prog_B's by conversion (pgi_segs:
     PI_prog_B's segments ARE lib/B/Img0's rsegs).
   NAME GUARD: the instance's listing, segments and sigma are FULLY QUALIFIED (IMG_*_B; never an image-A module).
   No numeral; no ADDRESS typed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnPj CfParamsPreset.
(* the instance and the row: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB PSstrRo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PjGetB.
Local Open Scope Z_scope.

(* the #102 B' listing, segments, sigma and CfImg, FULLY QUALIFIED *)
#[local] Notation IMG_SEGS_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.
#[local] Notation IMG_LST_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Listing_prog.B_prog_listing.
#[local] Notation IMG_PI_B := (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_prog.PI_prog_B).
#[local] Notation IMG_SIGMA_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_prog.B_prog_sigma.
#[local] Notation IMG_TFIBSEGS_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YB1v.tfibsegs.
#[local] Notation IMG_CFIMG_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.CfImgB.CfImg_B.
#[local] Notation CP := CfParamsPreset.CfParams_preset.

(* ---- closed check (vm_compute on a closed goal) ---- *)
(* CfImg_B's strcmp trampoline is the listing's __wrap_strcmp *)
Lemma pgi_strcmp_pc : @cf_pc_strcmp IMG_CFIMG_B = IMG_SIGMA_B AS___wrap_strcmp.
Proof. vm_compute. reflexivity. Qed.

Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive}.
#[local] Notation SEGSB := (@pa_segs rc IMG_LST_B (IMG_PI_B rc)).
#[local] Notation ARI := (@YG0ncf.ARcf rc CfImgB.CfImg_B CP (@pa_segs rc IMG_LST_B (IMG_PI_B rc)) YD2l.TfibB).

(* THE GUARD: PI_prog_B's segments ARE lib/B/Img0's rsegs (the #102 B' image) *)
Lemma pgi_segs : SEGSB = IMG_SEGS_B.
Proof. reflexivity. Qed.

(* ASC: the strcmp row at plain ARcf (PSstrRo.ps_strcmp_xrom_B) *)
Lemma pgi_asc :
  @astrcmp_realizes_xrom fx SEGSB YD2l.TfibB ARI (@pa_relro_lo rc IMG_LST_B (IMG_PI_B rc))
    (@pa_relro_hi rc IMG_LST_B (IMG_PI_B rc)) (@pa_sigma rc IMG_LST_B (IMG_PI_B rc) AS___wrap_strcmp).
Proof.
change (@pa_sigma rc IMG_LST_B (IMG_PI_B rc) AS___wrap_strcmp) with (IMG_SIGMA_B AS___wrap_strcmp).
rewrite <- pgi_strcmp_pc.
change SEGSB with IMG_TFIBSEGS_B.
exact (PSstrRo.ps_strcmp_xrom_B (fx := fx) (rc := rc) (cp := CP) YD2l.TfibB YD2l.TfibB_syms
  (@pa_relro_lo rc IMG_LST_B (IMG_PI_B rc)) (@pa_relro_hi rc IMG_LST_B (IMG_PI_B rc))).
Qed.

(* the two tops at the B' instance, the strcmp row cited: no premise left *)
Theorem pj_get_holds_B_inst_c : forall (SK : YI16.sink_head),
  @tpj_get_specX fx rc CP prh_img_B RL IMG_LST_B (IMG_PI_B rc) YD2l.TfibB ARI SK.
Proof. intros SK. exact (@PjGetB.pj_get_holds_B_top fx rc CfImgB.CfImg_B RL SK pgi_asc). Qed.
Theorem pj_get_str_holds_B_inst_c : forall (SK : YI16.sink_head),
  @tpj_get_str_specX fx rc CP prh_img_B RL IMG_LST_B (IMG_PI_B rc) YD2l.TfibB ARI SK.
Proof. intros SK. exact (@PjGetB.pj_get_str_holds_B_top fx rc CfImgB.CfImg_B RL SK pgi_asc). Qed.
End inst.

Print Assumptions pj_get_holds_B_inst_c.
Print Assumptions pj_get_str_holds_B_inst_c.
(* the wrong-image check: every PA / L / PI argument names image B' (PI_prog_B, B_prog_listing, prh_img_B) *)
Set Printing Implicit.
Unset Printing Notations.
Check @pj_get_holds_B_inst_c.
Check @pj_get_str_holds_B_inst_c.
Set Printing Notations.
Unset Printing Implicit.
