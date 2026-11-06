(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_parse of fuzz_preset's asan-ubsan image B' (pin d663f82d7f488d30, twin c90d4fa54d43; B'
   0x862ec, 36 instructions; preset_file.c :296-309) on the kit's cwpj-fix f29626eb1667: the kit's tpj_parse_specX ITSELF
   the kit's tpj_parse_specX ITSELF (lib/A/PRH_FnPj.v (sha256 35457d119ddb; internal record) :592-738) at image B', composed from the segment files
   lib/B/Prog/pj_parse_defs.v. NO twin: the kit's repaired PRH_Base.prh_cw_pj (blob ae260e28900e :1521-1527, each cursor
   arm's FIRST disjunct only) is word for word the B' cursor set the cut's walk proved under its twin prh_cw_pjB /
   tpj_parse_specX_B_FIX (lib/B/Prog/pj_parse_defs.v (sha256 2b4f7e6bc93e; internal record)), so the twin, its bridge pjz_cwB_cw and the lemma that derived the twin from the kit's text are deleted.
   VACUITY (below, at B := YD2l.TfibB): the premises the batch kit put where the f97c walk's two DW memberships were have
   witnesses - the closure at the driver's context (pjz_vac_univ_B, the kit's prh_univ_closure_witness_B) and, at every
   entry state, a cursor set meeting the kit's prh_cw_pj (parse_noting's pn_cw shape) with its room at the start depot
   (pjz_vac_cw_B, YCbqGwild.wild_room_cw_init with WildRoomInstB.B_wmax).
   pjp_compose turns the entry segment into the target text; pj_parse_holds_B chains the segment files (entry -> C1 ->
   C2ok / C2ref -> C3 -> epilogue), the glue file and the two pure model lemmas (pj_parse_live.v pjl_live_evs: pj_parse's
   live sum bounds parse_value's per-event live room; pj_parse_frees.v pjf_frees_same: pj_free's order list under the
   reading's outcomes is the all-granted one when the reading is) into it at image B'.
   Callee texts (pjp_texts): the batch kit's parse_value (tparse_value_specX 0, every CTX), skip_ws (tskip_ws_specX, DISCHARGED in
   pj_parse_holds_B_sk by the B' skip_ws_holds, lib/B/Prog/skip_ws_mn.v blob 44c3f9442988 on the cut), pj_free
   (tpj_free_specX CTX0 DOC_D) and __asan_memset (YGcallMxmn.aintrin_realizes_xm).
   THE INSTANCE pj_parse_holds_Bp (B := YD2l.TfibB, ARx := ARcf /\ xs_placed_cf, cp := CfParams_preset, ci := CfImg_B,
   RL := prh_room_live_a8): LAWS, PALibCore, pjp_g_vis are proved (pj_parse_inst.v); CFHEAD-16 (prh_head16) by
   reflexivity; parse_value BY CITATION of the closed pair lib/B/Prog/PItems_PvPair.v pv_pi_closed (parse_value /
   parse_items B', PROVED on this base); pj_free BY CITATION of
   lib/B/Prog/pj_free_iface.v tpj_free_specX_B_preset_iface (the B' walk at the interface instance;
   its relation PresetCfnB.iface_ARx IS ARcf /\ xs_placed_cf at CfParams_preset, by conversion); the
   fuzz_free row pj_free takes BY CITATION of the cut's B' walk at the same relation ARcfx: lib/B/Prog/FuzzFreeB.v
   fuzz_free_holds_B, its image stand-ins (pal_pst_ok, pal_unpoison, PALib, TS) by PItems_inst.v (f087cf022ab4),
   PALibB.v and YD2l.TfibB_syms. The fuzz_malloc row stays NAMED: the cut's B' walk FuzzMallocB_p102_holds.v
   (9c1e95fa623a) does not compile on the cut (:416, `Not an inductive goal with 2 constructors`). What remains are
   the NAMED callee rows, each with its owner (the theorem's premises; the names are pv_pi_closed's, pj_free_iface's
   and FuzzFreeB's):
     AMS      __asan_memset's m-form intrinsic row at ARcfx                   the frame-class proofs / the allocator proofs
     TGR      the batch kit's tgrow_specX                                              the grow lane
     TPS      the batch kit's tparse_string_specX                                      the parse_string lane
     AF       YGcfMallocComposeKeep.afree_realizes_cf_rh_keep, the free row in its keep form (FuzzFreeB reads the keep)
     AU       aunpoison_realizes_cf                                            fuzz_free's unpoison row
     TLIT     the kit's tliteral_specX                                              literal's lane
     ASM0     frame class 0's m-form contract at ARcf                          the frame-class proofs
     FMALLOC  the kit's tfuzz_malloc_specX at ARcfx                                 S1MallocB's lane (FuzzMallocB_p102_holds.v)
     CPY      __asan_memcpy's m-form row at ARcf                               the allocator proofs
   Pins (B' listing lib/B/Listing_prog.v, PAImg_prog.v; B_entry_pj_parse 0x862ec, slot 4872): the calls at +0x40 /
   +0x4c / +0x58 / +0x6c (__asan_memset, parse_value, skip_ws, pj_free), the cuts +0x4c / +0x54 / +0x68 / +0x74. No
   ADDRESS numeral in this file. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YGcfHp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_parse_defs pj_parse_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
pj_parse_seg_ent pj_parse_seg_c1 pj_parse_seg_c2ok pj_parse_seg_c2ref pj_parse_seg_ep pj_parse_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require pj_parse_live pj_parse_frees.
(* skip_ws B', proved by a Theorem Labs lane (lib/B/Prog/skip_ws_mn.v blob 44c3f9442988 on the cut: skip_ws_holds, the kit's
   tskip_ws_specX) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import skip_ws_mn.
(* the closed parse_value / parse_items pair at the instance (PItems_PvPair.v pv_pi_closed) and pj_free B' at the
   interface instance (pj_free_iface.v tpj_free_specX_B_preset_iface) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_PvPair pj_free_iface.
(* the B' fuzz_free walk on the cut, cited for the fuzz_free row: FuzzFreeB.fuzz_free_holds_B at ARcfx (= ARI); its
   image stand-ins by PItems_inst.v's pii_pst_ok / pii_unpoison, PALibB.exvi_eh_palib and YD2l.TfibB_syms *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzFreeB PItems_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require WildRoomInstB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Witness.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- VACUITY CHECK at the instance B := YD2l.TfibB (B'): the premises the batch kit put where the two DW memberships were are
   jointly met - the closure at the driver's context [[0x815c8]] (the kit's PRH_Witness.prh_univ_closure_witness_B), and
   for EVERY entry state a cursor set CW meeting the kit's prh_cw_pj (the shape of parse_noting's pn_cw: one trace per
   cursor free site, from the cursor end t0 + len and from the word at pj_parse's slot) whose room holds at the start
   depot (YCbqGwild.wild_room_cw_init: |CW| = 2 <= u_wmax = 3926, WildRoomInstB.B_wmax) ---- *)
Section v. Context {rc : YM05.RunCeil}.
Lemma pjz_vac_univ_B : @prh_univ_closure PRH_ImgB.prh_img_B YD2l.TfibB CfImgB.CfImg_B [[0x815c8]].
Proof. exact (PRH_Witness.prh_univ_closure_witness_B YD2l.TfibB eq_refl eq_refl). Qed.

Lemma pjz_vac_cw_B : forall (W : world (@pa_segs _ B_prog_listing PI_prog_B)) (mem : word -> option byte)
  (regs : bvmap 5 word) (t0 len : Z),
  exists CW, prh_cw_pj (PI := PRH_ImgB.prh_img_B) (PA := PI_prog_B) YD2l.TfibB CW W mem regs t0 len /\
    YCbqGwild.wild_room (as_universe YD2l.TfibB) CW 0 (st_depot init_state).
Proof.
intros W mem regs t0 len.
assert (E2 : (length (@prh_free_sites PRH_ImgB.prh_img_B F_parse_items) +
              length (@prh_free_sites PRH_ImgB.prh_img_B F_parse_string) = 2)%nat) by (vm_compute; reflexivity).
assert (HW : forall w0, YCbqGwild.wild_room (as_universe YD2l.TfibB)
  (map (fun r => prh_trace (pc_free_ra0 (as_code YD2l.TfibB)) r [t0 + len]) (@prh_free_sites PRH_ImgB.prh_img_B F_parse_items) ++
   map (fun r => prh_trace (pc_free_ra0 (as_code YD2l.TfibB)) r [w0]) (@prh_free_sites PRH_ImgB.prh_img_B F_parse_string))
  0 (st_depot init_state)).
{ intros w0. apply YCbqGwild.wild_room_cw_init. rewrite length_app, !length_map, E2.
  change (as_universe YD2l.TfibB) with YCej.Tfib_universe. rewrite WildRoomInstB.B_wmax. lia. }
destruct (rdword (aview (@pa_segs _ B_prog_listing PI_prog_B) (w_H W) mem)
  (spZ regs - @pi_frame PRH_ImgB.prh_img_B F_pj_parse)) as [w0|] eqn:Ew.
- exists (map (fun r => prh_trace (pc_free_ra0 (as_code YD2l.TfibB)) r [t0 + len])
           (@prh_free_sites PRH_ImgB.prh_img_B F_parse_items) ++
         map (fun r => prh_trace (pc_free_ra0 (as_code YD2l.TfibB)) r [w0])
           (@prh_free_sites PRH_ImgB.prh_img_B F_parse_string)).
  split; [unfold prh_cw_pj; split|exact (HW w0)].
  + intros r Hr. apply in_or_app. left. apply in_map_iff. exists r. split; [reflexivity | exact Hr].
  + intros r Hr w Hw. pose proof (eq_trans (eq_sym Ew) Hw) as Ew'. injection Ew' as <-.
    apply in_or_app. right. apply in_map_iff. exists r. split; [reflexivity | exact Hr].
- exists (map (fun r => prh_trace (pc_free_ra0 (as_code YD2l.TfibB)) r [t0 + len])
           (@prh_free_sites PRH_ImgB.prh_img_B F_parse_items) ++
         map (fun r => prh_trace (pc_free_ra0 (as_code YD2l.TfibB)) r [0])
           (@prh_free_sites PRH_ImgB.prh_img_B F_parse_string)).
  split; [unfold prh_cw_pj; split|exact (HW 0)].
  + intros r Hr. apply in_or_app. left. apply in_map_iff. exists r. split; [reflexivity | exact Hr].
  + intros r Hr w Hw. pose proof (eq_trans (eq_sym Ew) Hw) as Ew'. discriminate Ew'.
Qed.
End v.

#[local] Existing Instance prh_img_B.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation PA := PI_prog_B.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* the entry segment is the target text: its premises are pjp_pre of the entry record (the earlier walk's 26 positions,
   then the kit's two new premises, then the hull budget; pjp_pre's note), its post is pjp_FIN (the kit's tpjP_Q); both
   conclude SRr' SEGS RZ_cf *)
Theorem pjp_compose : forall CTX0 CW, pjp_seg_entry B ARx CTX0 CW -> tpj_parse_specX (PA := PA) B ARx SK CTX0 CW.
Proof.
intros CTX0 CW SEG most own ly S Hp W regs mem md ch d t0 len out tl Lam peak cnt fail ran
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29.
exact (SEG (MkPjpEnt ly S Hp W regs mem md ch d t0 len out tl Lam peak cnt fail ran most own)
  (conj H1 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12 (conj H13
   (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21 (conj H22 (conj H23 (conj H25 (conj H26
   (conj H2 (conj H27 (conj H28 (conj H14 (conj H24 H29))))))))))))))))))))))))))))).
Qed.

(* pj_parse on image B', from its callees' batch-kit texts (pjp_texts). Hypotheses beyond the callee texts: the allocator laws
   at the harness head (LAWS), the image shadow facts pjp_g_vis, and CFHEAD-16 (prh_head16); all three are proved at
   the instance (pj_parse_holds_Bp). The glue facts and the two pure model lemmas are proved. *)
Theorem pj_parse_holds_B (LAWS : AR_laws_x SEGS B ARx cf_head) (VIS : pjp_g_vis B ARx) (HH : prh_head16) :
  forall CTX0 CW, pjp_texts B ARx CTX0 CW -> tpj_parse_specX (PA := PA) B ARx SK CTX0 CW.
Proof.
intros CTX0 CW TX.
destruct (@pjp_glue_holds cp) as (Gfd & Gnode & Gdep & Grun & Gfin & Gnor & Gcal & Gfa & Grest & Gab).
pose proof (pjp_g_univ_holds B) as GU.
pose proof (pjp_frame_kept_holds (SK := SK) B ARx LAWS) as KEPT.
pose proof (pjp_seg_C3_holds (SK := SK) B ARx LAWS CTX0 CW) as S3.
pose proof (pjp_seg_C2ref_holds (SK := SK) B ARx LAWS Grun Gnor Gcal Gfa Gab HH pj_parse_frees.pjf_frees_same
  CTX0 CW TX KEPT S3) as S2R.
pose proof (pjp_seg_C2ok_holds (SK := SK) B ARx CTX0 CW TX KEPT S3 S2R HH LAWS VIS Gdep Grun Gfin Gnor Gcal Gfa
  Grest Gab) as S2OK.
pose proof (pjp_seg_C1_holds (SK := SK) B ARx LAWS GU VIS HH (@pj_parse_live.pjl_live_evs cp)
  CTX0 CW TX KEPT S2OK S2R) as S1.
pose proof (pjp_seg_entry_holds (SK := SK) B ARx cf_head LAWS CTX0 CW TX S1) as SE.
exact (pjp_compose CTX0 CW SE).
Qed.

(* the same with skip_ws's text discharged by skip_ws_holds (lib/B/Prog/skip_ws_mn.v), which takes the
   image-B' library fact PALibCore at the whole-range instance PI_prog_B (TLP; PALibB.exvi_eh_palib at the instance) *)
Theorem pj_parse_holds_B_sk (LAWS : AR_laws_x SEGS B ARx cf_head) (VIS : pjp_g_vis B ARx) (HH : prh_head16)
  (TLP : PALibCore (L := B_prog_listing) (PI := PA) B) :
  forall CTX0 CW,
  (forall (fy : YK11.FPState) (CTX : list (list Z)),
     tparse_value_specX (fx := fy) (PA := PA) B ARx SK 0%nat CTX CTX0 CW) ->
  (forall fy : YK11.FPState, tpj_free_specX (fx := fy) (PA := PA) B ARx SK CTX0 DOC_D) ->
  YGcallMxmn.aintrin_realizes_xm SEGS B ARx OSet (pa_sigma AS___asan_memset) ->
  tpj_parse_specX (PA := PA) B ARx SK CTX0 CW.
Proof.
intros CTX0 CW PV PF AM. apply (pj_parse_holds_B LAWS VIS HH CTX0 CW).
split; [exact PV|]. split; [|split; [exact PF | exact AM]].
intros fy. exact (skip_ws_holds (fx := fy) SK B ARx LAWS TLP).
Qed.
End c.

(* ---- THE INSTANCE: B := YD2l.TfibB (B'), ARx := ARcf with the error buffer placed (ARcfx), cp := CfParams_preset,
   ci := CfImg_B (B', generated from c90d4fa54d43), RL := prh_room_live_a8. LAWS, TLP and pjp_g_vis are proved at the
   instance (pj_parse_inst.v; PALibB.exvi_eh_palib), prh_head16 by reflexivity; parse_value by pv_pi_closed, pj_free
   by tpj_free_specX_B_preset_iface; fuzz_free by the cut's B' walk FuzzFreeB.fuzz_free_holds_B. The premises are the
   NAMED callee rows of the header, verbatim as pv_pi_closed (PItems_PvPair.v), pj_free_iface.v and FuzzFreeB take
   them. ---- *)
Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance prh_room_live_a8.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation PA := PI_prog_B.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation ARI :=
  (fun ly S Hp W mem md => YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).
#[local] Abbreviation RLa8 := (prh_room_live_a8 (cp := CP)).

Theorem pj_parse_holds_Bp
  (AMS : forall fy : YK11.FPState,
     YGcallMxmn.aintrin_realizes_xm (fx := fy) SEGS TB ARI OSet (@pa_sigma _ B_prog_listing PA AS___asan_memset))
  (TGR : forall (fy : YK11.FPState) (CTX0' : list (list Z)),
     tgrow_specX (fx := fy) (RL := RLa8) (L := B_prog_listing) (PA := PA) TB ARI SK CTX0')
  (TPS : forall (fy : YK11.FPState) (CTX0' CW' : list (list Z)),
     tparse_string_specX (fx := fy) (RL := RLa8) (L := B_prog_listing) (PA := PA) TB ARI SK CTX0' CW')
  (AF : forall fy : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fy) SEGS TB)
  (AU : forall fy : YK11.FPState, YGcfHp.aunpoison_realizes_cf (fx := fy) SEGS TB)
  (TLIT : forall fy : YK11.FPState,
     tliteral_specX (fx := fy) (RL := RLa8) (PI := prh_img_B) (PA := PA) TB ARI SK)
  (ASM0 : forall fy : YK11.FPState,
     YGcallMxmn.astack_malloc_realizes_xm (fx := fy) SEGS TB (YG0ncf.ARcf (cp := CP) SEGS TB) 0)
  (CPY : forall fx1 : YK11.FPState,
     YGcallMxmn.aintrin_realizes_xm (fx := fx1) SEGS TB (YG0ncf.ARcf (cp := CP) SEGS TB) OCpy
       (@pa_sigma _ B_prog_listing PA AS___asan_memcpy))
  (FMALLOC : forall fy : YK11.FPState,
     PRH_FnAlloc.tfuzz_malloc_specX (fx := fy) (cp := CP) (RL := RLa8) (PI := prh_img_B) (PA := PA) TB ARI SK) :
  forall CTX0 CW,
  tpj_parse_specX (fx := fx) (ci := CfImgB.CfImg_B) (cp := CP) (RL := RLa8) (PA := PA) TB ARI SK CTX0 CW.
Proof.
intros CTX0 CW.
(* fuzz_free at every float state: the cut's B' walk FuzzFreeB.fuzz_free_holds_B at ARcfx (its callee rows AF / AU,
   its image stand-ins by PItems_inst.v, PALibB.v and YD2l.TfibB_syms) *)
assert (XFF : forall fy : YK11.FPState, PRH_FnAlloc.tfuzz_free_specX (fx := fy) (cp := CP) (PA := PA) TB ARI SK).
{ intros fy. eapply FuzzFreeB.fuzz_free_holds_B;
    first [exact (AF fy) | exact (AU fy) | exact PALibB.exvi_eh_palib | exact PItems_inst.pii_pst_ok
          | exact PItems_inst.pii_unpoison | exact YD2l.TfibB_syms]. }
apply (pj_parse_holds_B_sk (ci := CfImgB.CfImg_B) (cp := CP) (RL := RLa8) (SK := SK) TB ARI
  pjp_inst_laws (conj pjp_inst_frame_hull (conj pjp_inst_zs_aligned pjp_inst_img_vis)) eq_refl
  (YC1fP.palib_core TB PALibB.exvi_eh_palib) CTX0 CW).
- (* parse_value at depth 0, every float state and entry context: the closed pair *)
  intros fy CTX.
  exact (proj1 (PItems_PvPair.pv_pi_closed (rc := rc) SK AMS TGR TPS AF AU TLIT ASM0 FMALLOC CPY 0%nat) fy CTX CTX0 CW).
- (* pj_free at DOC_D, every float state: pj_free_iface.v's B' walk at the interface relation (= ARI by conversion) *)
  intros fy.
  exact (pj_free_iface.tpj_free_specX_B_preset_iface (fx := fy) (SK := SK) (XFF fy) (AMS fy) CTX0 DOC_D).
- exact (AMS fx).
Qed.
End inst.

(* the top as stated, with implicit arguments (the B' instance: PI_prog_B, prh_img_B, CfImg_B, CfParams_preset), and
   its closure *)
Set Printing Implicit. Unset Printing Notations.
Check pj_parse_holds_Bp.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions pj_parse_holds_Bp.
Print Assumptions pjz_vac_univ_B.
Print Assumptions pjz_vac_cw_B.
