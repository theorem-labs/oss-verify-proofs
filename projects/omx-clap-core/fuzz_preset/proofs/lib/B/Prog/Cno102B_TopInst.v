(* fuzz_preset, image B' (asan-ubsan, harness fix #102: pin sha256 d663f82d7f488d30, twin c90d4fa54d43160b): the cno B'
   top AT THE INSTANCE. cnb_B_top_inst is lib/B/Prog/Cno102B_Top.v's cnb_B_top (the kit's tcheck_no_overread_specX at the
   cut 7cdbb61b5fa0, PRH_FnCheck.v c40cf3fdcd2a :738-823) taken at PA := PI_prog_B, B := YD2l.TfibB, ARx := the cf
   relation at TfibB,
   with every STATIC-LAYOUT fact discharged by its instance witness:
     PAL  = Cno102B_Wit.cnbw_pal  (a Theorem Labs lane's PALibB.exvi_eh_palib, lib/B/PALibB.v 5baa19c890f7)
     IMG  = Cno102B_Img.cnb_img_inst (a Theorem Labs lane's, lib/B/Prog/Cno102B_Img.v 42e69f3b8fb6, re-fit to the cut; YCej 71ae24321ba4)
     SM3  = Cno102B_Wit.cnbw_sm3  (closed computation)
     ISV  = Cno102B_Wit.cnbw_isv  (over PI_prog_B's [pa_lo, pa_hi) = CfImg_B's [cf_img_lo, cf_img_top): cnbw_band_cf)
     HTOP = Cno102B_Wit.cnbw_htop (segment AsanUbsan_segment_003 reaches IMG_TOP_B; cnbw_segs_B pins the segments)
   leaving as hypotheses ONLY the state premises (the callee texts and runtime rows, at every float state; the free
   row is the primed row with the memnorm keep, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep, the form CB8
   takes). The instance's CfImg is CfImgB.CfImg_B, the one the witnesses are stated at.
   The cut closed PJF-TIE inside CB8 (Cno102B_F.v's cnb_fo), so no inner named premise is left. Row R7-7
   (a Theorem Labs lane; family lead a Theorem Labs lane). Template: lib/B/Prog/Caw102B_Img.v caw_B_top_inst
   (a working branch db029676dbf7).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma; the composition at the instance).
   PA is passed EXPLICITLY at every use (wrong-image trap: instance search can also find PI_prog_A in this closure).
   No numeral. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YG0p YCbqG YGcfNames YP0b YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YGcallx YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_PjOrder PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Cno102B_Top Cno102B_Wit Cno102B_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance prh_room_live_a8.
#[local] Abbreviation PAB := (@PI_prog_B rc).
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PAB).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PAB).
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARcfxB := (fun ly S Hp W mem md => ARcf SEGS TB ly S Hp W mem md /\ xs_placed_cf ly S).

(* the top at the instance: its premises the callee texts and the runtime rows only; its conclusion the kit's restated
   text *)
Theorem cnb_B_top_inst : forall (CTX0 : list (list Z)),
  (forall fz : YK11.FPState,
     YGcallMxmn.astack_malloc_realizes_xm (fx := fz) SEGS TB (fun ly S Hp W mem md => ARcf SEGS TB ly S Hp W mem md)
       CNB_CID) ->
  (forall fz : YK11.FPState, YGcallMxmn.aintrin_realizes_xm (fx := fz) SEGS TB ARcfxB OSet (SIGMA AS___asan_memset)) ->
  (forall fz : YK11.FPState, tpadded_specX (fx := fz) (L := B_prog_listing) (PA := PAB) TB ARcfxB SK CTX0) ->
  (forall fz : YK11.FPState, tparse_noting_specX (fx := fz) (L := B_prog_listing) (PA := PAB) TB ARcfxB SK CTX0) ->
  (forall fz : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fz) (L := B_prog_listing) (PA := PAB) TB ARcfxB SK) ->
  (forall fz : YK11.FPState, tsame_specX (fx := fz) (L := B_prog_listing) (PA := PAB) TB ARcfxB SK DOC_D) ->
  (forall fz : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fz) SEGS TB) ->
  (forall fz : YK11.FPState, tpj_free_specX (fx := fz) (L := B_prog_listing) (PA := PAB) TB ARcfxB SK CTX0 DOC_D) ->
  (forall fz : YK11.FPState,
     YGcallMxmn.aset_shadow_realizes_xm (fx := fz) SEGS TB ARcfxB (SIGMA AS___asan_set_shadow_f5) 245) ->
  tcheck_no_overread_specX (fx := fx) (L := B_prog_listing) (PA := PAB) TB ARcfxB SK CTX0.
Proof.
intros CTX0 ASM3 AMEMSET HPAD HPN HRO HSAME AFREE HPJF ASETSH.
eapply (@Cno102B_Top.cnb_B_top fx rc CfImgB.CfImg_B SK PAB TB CTX0).
all: first [ exact Cno102B_Wit.cnbw_pal | exact (Cno102B_Img.cnb_img_inst rc) | exact Cno102B_Wit.cnbw_sm3
           | exact Cno102B_Wit.cnbw_isv | exact Cno102B_Wit.cnbw_htop | exact ASM3 | exact AMEMSET | exact HPAD
           | exact HPN | exact HRO | exact HSAME | exact AFREE | exact HPJF | exact ASETSH ].
Qed.
End w.

Set Printing Implicit.
About cnb_B_top_inst.
Print Assumptions cnb_B_top_inst.
