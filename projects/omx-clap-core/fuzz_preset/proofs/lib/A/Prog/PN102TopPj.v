(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/PN102TopPj.v, with its module paths changed; 28 of its 78 lines of code are new or changed and 1 line of the source is left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44): the top of the walk of parse_noting (row N10-PNA,
   lib/A/Prog/PN102Top.v tparse_noting_specX_A_TfibB) with its callee text HPJ (the batch kit's tpj_parse_specX at every CW)
   DISCHARGED by a Theorem Labs lane's A' walk of pj_parse, lib/A/Prog/PjParseA_top.v pj_parse_holds_A: first on the kit's cut
   (a working branch afb1875e8b36), here as re-fit to the kit's repaired prh_cw_pj
   (a working branch part 1 2c6f778a5d66, merged by sha: PjParseA_vac.v pjz_vac_cw_A re-fit,
   PjParseA_top.v comments only; the 10 lib/B/Prog/pj_free_*.v as on afb1875e8b36 and a17c5f0738fc). POST-BATCH,
   on a working branch f29626eb1667; not for the cut landing.
   FORM CHECK: pj_parse_holds_A concludes `@tpj_parse_specX fx rc CfImgA.CfImg_A CfParams_preset prh_img_A
   (@prh_room_live_a8 CfParams_preset) A_prog_listing (@PI_prog_A rc) AD2l.TfibB (ARcf .. AD2l.TfibB .. /\
   xs_placed_cf ..) SK CTX0 CW` for every CTX0 CW; HPJ of tparse_noting_specX_A_TfibB is that same constant at the same
   arguments for every CW, at ci := CfImgA.CfImg_A (PN102Top.v leaves ci a Context variable; the consumer's ci is
   CfImg_A, PresetD2pAPf.v:99-101). So this corollary is at ci := CfImgA.CfImg_A.
   OPEN PREMISES of the corollary: the three pj_parse_holds_A premises in HPJ's place, each with its owner -
     AF   forall fy, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fuzz_free's free row, re-hide + memnorm keep) a Theorem Labs lane
     AU   forall fy, YGcfHp.aunpoison_realizes_cf (fuzz_free's unpoison row)                 two Theorem Labs lanes
     TPV  forall CW fy CTX, the batch kit's tparse_value_specX 0 at the instance                      a Theorem Labs lane
          (pj_parse_holds_A takes it at its own CW; HPJ is at every CW, so TPV is at every CW). PROVED on combine6:
          a Theorem Labs lane's lib/A/VrdTop.v vrd_parse_value_holds (a working branch f40eca0736e0, this
          branch's base), discharged in the second corollary below, tparse_noting_specX_A_TfibB_pjv.
   and the walk's other three callee texts, unchanged: HLIVE tfuzz_alloc_live_specX (a Theorem Labs lane), HRO forall fy
   tfuzz_alloc_ran_out_specX (a Theorem Labs lane), HCRC forall fy tcheck_reject_clean_specX (the kit owner). TB is discharged
   (pn_top_TB_witness) inside tparse_noting_specX_A_TfibB.
   THE SECOND COROLLARY tparse_noting_specX_A_TfibB_pjv: the first with TPV := fun CW fy CTX =>
   vrd_parse_value_holds CTX0 CW AREAL_cf AMALLOC AF fy 0 CTX.
   FORM CHECK, argument for argument (VrdTop.v:1262-1264, Section top at :1047-1060): vrd_parse_value_holds concludes
   `@tparse_value_specX fx rc CfImgA.CfImg_A CfParams_preset prh_img_A (@prh_room_live_a8 CfParams_preset)
   A_prog_listing (@PI_prog_A rc) AD2l.TfibB vt_ARA SK d CTX CTX0 CW` for every CTX0 CW fx d CTX, with its Section's
   rc and SK; TPV here is that constant at the same fx (fy), rc, ci, cp, PI, RL, L, PA, B, SK, CTX, CTX0, CW and d := 0.
   ARx: VrdTop.vt_ARA (:867-868) is `fun ly S Hp W mem md => YG0ncf.ARcf SEGS AD2l.TfibB ly S Hp W mem md /\
   YG0ncf.xs_placed_cf ly S` at cp := CfParams_preset, which is ARcA below by delta: the same constant YG0ncf.ARcf of
   THIS tree, combine6's (YG0ncf.v 6748bee76f02, whose abudget_ok_cf carries cls1_band_vis_cf; the cut's is
   9c48a1a860d6). Every statement in this file and in PN102Top.v is over combine6's ARcf: the walk is re-built here.
   Its open premises, in VrdTop's Section top forms: AF (shared: vrd_parse_value_holds's AFREE, `forall fxA,
   YGcfMallocComposeKeep.afree_realizes_cf_rh_keep SEGS TfibB`, is the same Prop as pj_parse_holds_A's AF), AU,
   AREAL_cf (forall fxA Hp k, YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep at realloc's wrapper, ci := CfImg_A as
   VrdTop's Section top binds it by instance; a Theorem Labs lane), AMALLOC (forall fxA,
   YGcfMallocComposeKeep.amalloc_realizes_cf_keep at ci := CfImg_A likewise; a Theorem Labs lane), and HLIVE, HRO, HCRC as above.
   rule 24: proves function parse_noting (reuse search: `proof-index parse_noting` exit 4 at 2026-10-30 07:2xZ,
   index v5 06:36:24Z: 0 named / 0 by address / 0 related / 0 released; the unreleased hits are this lane's own N10-PNA
   files and the plain / UBSan / B' twins; own signed walk 13970867e0c9 re-bound). This file: a corollary of its top.
   NUMERALS: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YG0ncf YG0dcf YGcfRoomPre YGcfRoomKeep YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfHp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep YGcfInstReallocKKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnParse PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PN102Top PjParseA_top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require VrdTop.
Import ListNotations.
Local Open Scope Z_scope.
(* the driver's image instance (lib/A/PresetD2pAPf.v: ci := CfImg_A), as PSnpRowA.v declares it, so ARcf and
   afree_realizes_cf below elaborate at it *)
#[local] Existing Instance CfImgA.CfImg_A.

Section P. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation CI := CfImgA.CfImg_A.
#[local] Abbreviation PA := (@PI_prog_A rc).
#[local] Abbreviation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Abbreviation RLa8 := (prh_room_live_a8 (cp := CP)).
#[local] Abbreviation ARcA := (fun ly S Hp (W : world SEGS) mem md =>
  ARcf (cp := CP) SEGS AD2l.TfibB ly S Hp W mem md /\ xs_placed_cf ly S).

Theorem tparse_noting_specX_A_TfibB_pj : forall CTX0,
  tfuzz_alloc_live_specX (fx := fx) (cp := CP) (PI := prh_img_A) (RL := RLa8) (PA := PA) AD2l.TfibB ARcA SK ->
  (forall fy : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fy) (cp := CP) SEGS AD2l.TfibB) ->
  (forall fy : YK11.FPState, YGcfHp.aunpoison_realizes_cf (fx := fy) (ci := CI) (cp := CP) SEGS AD2l.TfibB) ->
  (forall (CW : list (list Z)) (fy : YK11.FPState) (CTX : list (list Z)),
     tparse_value_specX (fx := fy) (ci := CI) (cp := CP) (PI := prh_img_A) (RL := RLa8) (L := A_prog_listing)
       (PA := PA) AD2l.TfibB ARcA SK 0%nat CTX CTX0 CW) ->
  (forall fy : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fy) (cp := CP) (PI := prh_img_A) (RL := RLa8)
    (PA := PA) AD2l.TfibB ARcA SK) ->
  (forall fy : YK11.FPState, tcheck_reject_clean_specX (fx := fy) (cp := CP) (PI := prh_img_A) (RL := RLa8)
    (PA := PA) AD2l.TfibB ARcA SK) ->
  tparse_noting_specX (fx := fx) (ci := CI) (cp := CP) (PI := prh_img_A) (RL := RLa8) (PA := PA)
    AD2l.TfibB ARcA SK CTX0.
Proof.
intros CTX0 HL AF AU TPV HR HC.
exact (@PN102Top.tparse_noting_specX_A_TfibB fx rc CI SK CTX0 HL
  (fun CW => @PjParseA_top.pj_parse_holds_A fx rc SK AF AU CTX0 CW (TPV CW)) HR HC).
Qed.

(* TPV discharged by a Theorem Labs lane's parse_value top on combine6 (header: the form check and the premises) *)
Theorem tparse_noting_specX_A_TfibB_pjv : forall CTX0,
  tfuzz_alloc_live_specX (fx := fx) (cp := CP) (PI := prh_img_A) (RL := RLa8) (PA := PA) AD2l.TfibB ARcA SK ->
  (forall fy : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fy) (cp := CP) SEGS AD2l.TfibB) ->
  (forall fy : YK11.FPState, YGcfHp.aunpoison_realizes_cf (fx := fy) (ci := CI) (cp := CP) SEGS AD2l.TfibB) ->
  (forall (fxA : YK11.FPState) (Hp : list Z) (k : nat),
    YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fxA) (cp := CP) SEGS AD2l.TfibB Hp
      (@pa_sigma rc A_prog_listing PA AS___wrap_realloc) k) ->
  (forall fxA : YK11.FPState, YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fxA) (cp := CP)
    SEGS AD2l.TfibB) ->
  (forall fy : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fy) (cp := CP) (PI := prh_img_A) (RL := RLa8)
    (PA := PA) AD2l.TfibB ARcA SK) ->
  (forall fy : YK11.FPState, tcheck_reject_clean_specX (fx := fy) (cp := CP) (PI := prh_img_A) (RL := RLa8)
    (PA := PA) AD2l.TfibB ARcA SK) ->
  tparse_noting_specX (fx := fx) (ci := CI) (cp := CP) (PI := prh_img_A) (RL := RLa8) (PA := PA)
    AD2l.TfibB ARcA SK CTX0.
Proof.
intros CTX0 HL AF AU AREAL_cf AMALLOC HR HC.
exact (tparse_noting_specX_A_TfibB_pj CTX0 HL AF AU
  (fun CW fy CTX => @VrdTop.vrd_parse_value_holds rc SK CTX0 CW AREAL_cf AMALLOC AF fy 0%nat CTX) HR HC).
Qed.
End P.

(* THE CHECKS: the elaborated statement with every implicit argument shown; the closure. *)
Set Printing Implicit. Unset Printing Notations.
Check @tparse_noting_specX_A_TfibB_pj.
Check @tparse_noting_specX_A_TfibB_pjv.
Check @PjParseA_top.pj_parse_holds_A.
Check @VrdTop.vrd_parse_value_holds.
Print VrdTop.vt_ARA.
Check @PN102Top.tparse_noting_specX_A_TfibB.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions tparse_noting_specX_A_TfibB_pj.
Print Assumptions tparse_noting_specX_A_TfibB_pjv.
