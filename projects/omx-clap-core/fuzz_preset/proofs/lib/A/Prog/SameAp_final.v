(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (asan #102 pin 1be0f53d96cb, unstripped twin bff8519bbe3e), same:
   THE WALK AT THE INSTANCE OF RECORD. lib/A/Prog/SameAp_walk.v's same_holds_Ap, the batch kit's text tsame_specX itself
   (lib/A/PRH_FnEx.v :353 at the cut 7cdbb61b5fa0, with its GUARDED live-stack premise
   `spZ regs <= pa -> YGcallStackUp.astack_up_x segs ly W (spZ regs) mem` after fpre), at B := AD2l.TfibB (image A's
   generated record), RL := prh_room_live_a8, PA := PI_prog_A. PAL := PALibA.palib_A; SMA_CF (ARx refines ARcf) the
   identity / proj1. The A' twin of a Theorem Labs lane's image-B' lib/B/Prog/SameB_final.v (a working branch
   e95b6ce78e87), with the same argument order. Two tops:
   - same_holds_Ap_TfibBx at the relation of record ARxs = ARcf /\ xs_placed_cf (YGcallcf.ARxs; LAWS :=
     YGcallcf.AR_laws_x_xs);
   - same_holds_Ap_TfibB at plain ARcf (LAWS := PALibA.palib_laws_A, the A' twin of PALibB.exvi_eh_laws).
   FIT CHECK (same_holds_Ap_HSAME_fit below): the HSAME premise of lib/A/Prog/Cno102A_Top.v (check_no_overread A',
   a working branch d4661e0cd87a, :139-140, `forall fz : YK11.FPState, @tsame_specX fz rc CP
   prh_img_A prh_room_live_a8 A_prog_listing PA B ARcfx SK DOC_D`), at the instance Cno102A_TopA.v gives it
   (PA := PI_prog_A, B := AD2l.TfibB, SEGS := pa_segs of PI_prog_A, ARcfx := ARcf SEGS B /\ xs_placed_cf), restated
   here for every depth n, closed by plain exact from same_holds_Ap_TfibBx.
   What stays open, by name: the two runtime rows, MARKED TEXTS (strcmp: YGcallMxmn.astrcmp_realizes_xrom, OWNER
   a Theorem Labs lane; bcmp: YGcallMxmn.abcmp_realizes_xm, OWNER a Theorem Labs lane), as the B' twin takes them. No numeral; no image-B
   module. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Img Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import SameAp_defs SameAp_walk.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset AD2l PALibA.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_A.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := AD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) rsegs TB).

Theorem same_holds_Ap_TfibB : forall (SK : YI16.sink_head),
  astrcmp_realizes_xrom rsegs TB ARI A_prog_relro_lo A_prog_relro_hi SMA_STRCMP ->
  abcmp_realizes_xm rsegs TB ARI SMA_BCMP ->
  forall n, tsame_specX (cp := CP) (RL := @prh_room_live_a8 CP) (PA := PI_prog_A) TB ARI SK n.
Proof.
intros SK HSTR HBCMP n.
exact (@same_holds_Ap fx rc ci CP (@prh_room_live_a8 CP) TB ARI SK PALibA.palib_laws_A PALibA.palib_A HSTR HBCMP
  (fun _ _ _ _ _ _ H => H) n).
Qed.

(* ---- AT THE RELATION OF RECORD for the image-A TFIB closure: ARx := ARcfx = (ARcf rsegs TfibB /\ xs_placed_cf), the
   relation the A' consumers cite (Cno102A_Top.v's ARcfx). LAWS by YGcallcf.AR_laws_x_xs rsegs TfibB
   (YG0lawscf.AR_laws_ok_cf rsegs TfibB), unconditional; PAL by PALibA.palib_A (PALib does not mention ARx); SMA_CF by
   proj1. The two runtime rows stay MARKED TEXTS, now at ARcfx. ---- *)
#[local] Abbreviation ARX := (fun ly S Hp W mem md =>
  YG0ncf.ARcf (cp := CP) rsegs TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

Theorem same_holds_Ap_TfibBx : forall (SK : YI16.sink_head),
  astrcmp_realizes_xrom rsegs TB ARX A_prog_relro_lo A_prog_relro_hi SMA_STRCMP ->
  abcmp_realizes_xm rsegs TB ARX SMA_BCMP ->
  forall n, tsame_specX (cp := CP) (RL := @prh_room_live_a8 CP) (PA := PI_prog_A) TB ARX SK n.
Proof.
intros SK HSTR HBCMP n.
exact (@same_holds_Ap fx rc ci CP (@prh_room_live_a8 CP) TB ARX SK
  (YGcallcf.AR_laws_x_xs (cp := CP) rsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) rsegs TB))
  PALibA.palib_A HSTR HBCMP (fun _ _ _ _ _ _ H => proj1 H) n).
Qed.
End f.

(* ---- FIT CHECK: Cno102A_Top.v's HSAME (d4661e0cd87a :139-140) at Cno102A_TopA.v's instance, for every depth n
   (DOC_D is one of them), with the segments as Cno102A_Top.v spells them (SEGS := pa_segs of PA), closed by plain exact.
   The runtime rows are taken at every FPState, as HSAME quantifies over fz. ---- *)
Section fit. Context {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Notation SEGS := (@pa_segs rc A_prog_listing (@PI_prog_A rc)).
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md =>
  @YG0ncf.ARcf rc ci CP SEGS AD2l.TfibB ly S Hp W mem md /\ @YG0ncf.xs_placed_cf rc ly S).

Example same_holds_Ap_HSAME_fit : forall (SK : YI16.sink_head),
  (forall fz : YK11.FPState,
     astrcmp_realizes_xrom (fx := fz) rsegs AD2l.TfibB ARcfx A_prog_relro_lo A_prog_relro_hi SMA_STRCMP) ->
  (forall fz : YK11.FPState, abcmp_realizes_xm (fx := fz) rsegs AD2l.TfibB ARcfx SMA_BCMP) ->
  forall n, forall fz : YK11.FPState,
    @tsame_specX fz rc CP prh_img_A (@prh_room_live_a8 CP) A_prog_listing (@PI_prog_A rc) AD2l.TfibB ARcfx SK n.
Proof.
intros SK HSTR HBCMP n fz.
exact (@same_holds_Ap_TfibBx fz rc ci SK (HSTR fz) (HBCMP fz) n).
Qed.
End fit.

Set Printing Implicit.
Check same_holds_Ap_TfibBx.
Check same_holds_Ap_TfibB.
Check same_holds_Ap_HSAME_fit.
Unset Printing Implicit.
Print Assumptions same_holds_Ap_TfibB.
Print Assumptions same_holds_Ap_TfibBx.
Print Assumptions same_holds_Ap_HSAME_fit.
