(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_parse of fuzz_preset's asan image A' (#102 pin 1be0f53d96cb, unstripped twin bff8519bbe3e;
   A' 0x85e20, 60 instructions; preset_file.c :296-309) on the kit's cwpj-fix f29626eb1667: the kit's tpj_parse_specX
   (lib/A/PRH_FnPj.v blob 38a83863585f :592-738) VERBATIM at image A', composed from the segment files over the cuts
   of lib/A/Prog/PjParseA_defs.v. NO twin: the walk never reads the kit's cursor-set premise prh_cw_pj (PjParseA_defs.v's
   header; the one cursor lemma is pjp_cw_entry_A there), so the kit's repair of prh_cw_pj (PRH_Base.v blob ae260e28900e
   :1521-1527, the code-word disjunct removed) touches only the vacuity witness.
   PORTED from the image-B' walk (the version pj_parse_top.v (sha256 1f2378f99422; internal record) of
   lib/B/Prog/pj_parse_top.v): the composition is the B' one; the segments are re-walked on A' (the commit message has
   the instruction compare and the per-segment map).
   VACUITY at B := AD2l.TfibB: lib/A/Prog/PjParseA_vac.v (the closure at the driver's context, pjz_vac_univ_A by the kit's
   PRH_Witness.prh_univ_closure_witness_A; at every entry state a cursor set meeting the kit's repaired prh_cw_pj on A' -
   parse_items' arm at the cursor end t0 + len, parse_string's at pj_parse's slot word - whose room holds at the
   start depot, pjz_vac_cw_A); printed below.
   pjp_compose turns the entry segment into the text; pj_parse_holds_A0 chains the segment files (entry -> C1 ->
   C2ok (with the inline skip_ws loop, PjParseA_skip.v) / C2ref -> C3 -> epilogue), the glue file and the two pure
   model lemmas (PjParseA_live.v pjl_live_evs, PjParseA_frees.v pjf_frees_same) at image A', for any B and ARx.
   Callee texts (pjp_texts): the batch kit's parse_value (tparse_value_specX 0, every CTX), pj_free (tpj_free_specX CTX0 DOC_D),
   __asan_memset (YGcallMxmn.aintrin_realizes_xm). No skip_ws: inlined on A' and walked.
   THE INSTANCE pj_parse_holds_A (B := AD2l.TfibB, ARx := ARcf /\ xs_placed_cf, cp := CfParams_preset, ci := CfImg_A,
   RL := prh_room_live_a8, PI := prh_img_A, PA := PI_prog_A): LAWS, pjp_g_vis and the callee rows by PjParseA_inst.v
   (the pjp_inst lemmas); prh_head16 by reflexivity; PALib by lib/A/PALibA.v palib_A; __asan_memset BY CITATION of
   lib/A/PRowSet.v prow_asan_memset_xm_A_lit; pj_free BY CITATION of the S6 A' walk
   lib/A/Prog/S6PjFreeTop.v pj_free_holds (a Theorem Labs lane's S6 on the kit's cut, by path from 0bda57e5972c); the fuzz_free row
   pj_free takes BY CITATION of the cut's A' walk lib/A/Prog/FuzzFree.v fuzz_free_holds (PAL by palib_A, pal_pst_ok by
   lib/A/Prog/FuzzAllocAccInst102.v acc_pal_pst_ok_A, TB by AD2l.TfibB_syms). What remains are NAMED callee rows (the
   theorem's premises):
     TPV  the kit's tparse_value_specX 0 at the instance (every fy, every CTX); lib/A/VrdUnit.v has the depth induction,
          and pj_parse_holds_A_tpv below discharges it by lib/A/VrdTop.v
     AF   YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fuzz_free's free-wrapper row, primed, with the
          memnorm keep at its leaf; FuzzFree reads the keep)
     AU   aunpoison_realizes_cf (fuzz_free's unpoison row, YGcfHp.v); lib/A/CfPoison102.v preset_aunpoison_cf102
          proves it, citing CfApiPreset.poison_next_vis_cf
   TPV DISCHARGED: pj_parse_holds_A_tpv (after pj_parse_holds_A, which stays as stated) is pj_parse_holds_A with TPV
   given by the parse_value A' proof VrdTop.vrd_parse_value_holds at d = 0 (lib/A/VrdTop.v and the lib/A/Vrd*.v files
   it Requires). Its premises are VrdTop's: AREAL_cf (realloc's wrapper row, the keep form at every ghost set and
   headroom, YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep), AMALLOC (fuzz_malloc's wrapper row, the keep form
   YGcfMallocComposeKeep.amalloc_realizes_cf_keep), and AF passed as VrdTop's AFREE as it is, with AU.
   No numeral in this file. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YGcfHp YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjParseA_defs PjParseA_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import
PjParseA_seg_ent PjParseA_seg_c1 PjParseA_seg_c2ok PjParseA_seg_c2ref PjParseA_seg_ep PjParseA_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PjParseA_live PjParseA_frees PjParseA_vac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset CfImgA AD2l PALibA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require VrdTop.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_A.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation PA := PI_prog_A.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* the entry segment is the kit's text: its premises are pjp_pre of the entry record (the text's order with the last two
   moved: pjp_pre's note; the hull budget last in both), its post is pjp_FIN; both conclude SRr' segs RZ_cf *)
Theorem pjp_compose : forall CTX0 CW, pjp_seg_entry B ARx CTX0 CW -> tpj_parse_specX (PA := PA) B ARx SK CTX0 CW.
Proof.
intros CTX0 CW SEG most own ly S Hp W regs mem md ch d t0 len out tl Lam peak cnt fail ran
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29.
exact (SEG (MkPjpEnt ly S Hp W regs mem md ch d t0 len out tl Lam peak cnt fail ran most own)
  (conj H1 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12 (conj H13
   (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21 (conj H22 (conj H23 (conj H25 (conj H26
   (conj H2 (conj H27 (conj H28 (conj H14 (conj H24 H29))))))))))))))))))))))))))))).
Qed.

(* pj_parse on image A', from its callees' batch-kit texts (pjp_texts). Hypotheses beyond the callee texts: the allocator laws
   at the harness head (LAWS), the image library facts PALib (TL: the GOT word of the shadow base), the image shadow
   facts pjp_g_vis, and CFHEAD-16 (prh_head16); all four are proved at the instance (pj_parse_holds_A). *)
Theorem pj_parse_holds_A0 (LAWS : AR_laws_x SEGS B ARx cf_head) (TL : PALib (L := A_prog_listing) (PI := PA) B)
  (VIS : pjp_g_vis B ARx) (HH : prh_head16) :
  forall CTX0 CW, pjp_texts B ARx CTX0 CW -> tpj_parse_specX (PA := PA) B ARx SK CTX0 CW.
Proof.
intros CTX0 CW TX.
destruct (@pjp_glue_holds cp) as (Gfd & Gnode & Gdep & Grun & Gfin & Gnor & Gcal & Gfa & Grest & Gab).
pose proof (pjp_g_univ_holds B) as GU.
pose proof (pjp_frame_kept_holds (SK := SK) B ARx LAWS) as KEPT.
pose proof (pjp_seg_C3_holds (SK := SK) B ARx LAWS CTX0 CW) as S3.
pose proof (pjp_seg_C2ref_holds (SK := SK) B ARx LAWS Grun Gnor Gcal Gfa Gab HH PjParseA_frees.pjf_frees_same
  CTX0 CW TX KEPT S3) as S2R.
pose proof (pjp_seg_C2ok_holds (SK := SK) B ARx CTX0 CW S3 S2R HH LAWS Gdep Grun Gfin Gnor Gcal Gfa Grest Gab) as S2OK.
pose proof (pjp_seg_C1_holds (SK := SK) B ARx LAWS GU VIS HH (@PjParseA_live.pjl_live_evs cp)
  CTX0 CW TX S2OK S2R) as S1.
pose proof (pjp_seg_entry_holds (SK := SK) B ARx cf_head LAWS TL CTX0 CW TX S1) as SE.
exact (pjp_compose CTX0 CW SE).
Qed.
End c.

(* ---- THE INSTANCE: B := AD2l.TfibB (A'), ARx := ARcf with the error buffer placed (ARcfx), cp := CfParams_preset,
   ci := CfImg_A, RL := prh_room_live_a8, PI := prh_img_A, PA := PI_prog_A. LAWS, pjp_g_vis by PjParseA_inst.v, TL by
   PALibA.palib_A, prh_head16 by reflexivity; __asan_memset by S6ImgWit.s6w_aim; pj_free by S6PjFreeTop.pj_free_holds
   (its image premises by S6ImgWit.v), fuzz_free by FuzzFree.fuzz_free_holds. The premises are the NAMED callee rows of
   the header, verbatim as FuzzFree.v and the kit's PRH_FnParse.v state them. ---- *)
Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Existing Instance prh_room_live_a8.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := AD2l.TfibB.
#[local] Abbreviation PA := PI_prog_A.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation ARI :=
  (fun ly S Hp W mem md => YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).
#[local] Abbreviation RLa8 := (prh_room_live_a8 (cp := CP)).

Theorem pj_parse_holds_A
  (AF : forall fy : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fy) SEGS TB)
  (AU : forall fy : YK11.FPState, YGcfHp.aunpoison_realizes_cf (fx := fy) SEGS TB) :
  forall CTX0 CW,
  (forall (fy : YK11.FPState) (CTX : list (list Z)),
     tparse_value_specX (fx := fy) (ci := CfImgA.CfImg_A) (cp := CP) (PI := prh_img_A) (RL := RLa8)
       (L := A_prog_listing) (PA := PA) TB ARI SK 0%nat CTX CTX0 CW) ->
  tpj_parse_specX (fx := fx) (ci := CfImgA.CfImg_A) (cp := CP) (PI := prh_img_A) (RL := RLa8) (L := A_prog_listing)
    (PA := PA) TB ARI SK CTX0 CW.
Proof.
intros CTX0 CW TPV.
apply (pj_parse_holds_A0 (ci := CfImgA.CfImg_A) (cp := CP) (RL := RLa8) (SK := SK) TB ARI
  pjp_inst_laws PALibA.palib_A (conj pjp_inst_frame_hull (conj pjp_inst_zs_aligned pjp_inst_img_vis)) eq_refl
  CTX0 CW).
(* pjp_texts at the instance: parse_value = the named row TPV; pj_free = the S6 A' walk (pjp_inst_pf, which takes
   fuzz_free from the cut's A' walk with the rows AF / AU); __asan_memset = the PRowSet.v row (pjp_inst_ams) *)
split; [exact TPV|].
split; [intros fy; exact (pjp_inst_pf (SK := SK) AF AU fy CTX0 DOC_D) | exact (pjp_inst_ams fx)].
Qed.

(* TPV discharged: VrdTop.vrd_parse_value_holds (the parse_value A' proof) at d = 0, for every fy and CTX. Its
   relation VrdTop.vt_ARA is ARcf /\ xs_placed_cf at CfParams_preset, that is ARI (equal by unfolding). Its premises
   take TPV's place, in VrdTop's order and forms: AREAL_cf (realloc's wrapper row at SEGS / TfibB, the keep form at
   every ghost set Hp and headroom k; VrdTop derives grow's callee tfuzz_realloc_specX from it), AMALLOC (fuzz_malloc's
   wrapper row, the keep form) and AFREE, which is AF (the keep form VrdTop reads). *)
Theorem pj_parse_holds_A_tpv
  (AREAL_cf : forall (fxA : YK11.FPState) (Hp : list Z) (k : nat),
     YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fxA) SEGS TB Hp
       (@pa_sigma _ A_prog_listing PA AS___wrap_realloc) k)
  (AMALLOC : forall fxA : YK11.FPState, YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fxA) SEGS TB)
  (AF : forall fy : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fy) SEGS TB)
  (AU : forall fy : YK11.FPState, YGcfHp.aunpoison_realizes_cf (fx := fy) SEGS TB) :
  forall CTX0 CW,
  tpj_parse_specX (fx := fx) (ci := CfImgA.CfImg_A) (cp := CP) (PI := prh_img_A) (RL := RLa8) (L := A_prog_listing)
    (PA := PA) TB ARI SK CTX0 CW.
Proof.
intros CTX0 CW.
exact (pj_parse_holds_A AF AU CTX0 CW
  (fun fy CTX => VrdTop.vrd_parse_value_holds (rc := rc) (SK := SK) CTX0 CW AREAL_cf AMALLOC AF fy 0%nat CTX)).
Qed.
End inst.

(* the top as stated, with implicit arguments (the A' instance: PI_prog_A, prh_img_A, CfImg_A, CfParams_preset), and
   its closure *)
Set Printing Implicit. Unset Printing Notations.
Check pj_parse_holds_A.
Check pj_parse_holds_A_tpv.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions pj_parse_holds_A.
Print Assumptions pj_parse_holds_A_tpv.
Print Assumptions PjParseA_vac.pjz_vac_univ_A.
Print Assumptions PjParseA_vac.pjz_vac_cw_A.
