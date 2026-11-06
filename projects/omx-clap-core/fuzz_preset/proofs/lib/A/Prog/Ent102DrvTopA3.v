(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102DrvTopA3.v, with its module paths and module names changed; 405 of its 495 lines of code are new or changed and 40 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102 pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4): THE THIRD
   COMPOSED TOP of the A' driver. The second composed top Ent102DrvTopA2.TFIB_T_closed_A_walked2
   (lib/A/Prog/Ent102DrvTopA2.v) with its Section hypotheses DISCHARGED BY CITATION of theorems already proved on
   the kit's cut 7cdbb61b5fa0, on the named branch of a file taken by path, or in the int102 base this line merges
   (a working branch 26d8d53a1503) - nothing re-proved - and its two
   Section variables instantiated, all in ONE composition, TFIB_T_room_all_A_walked3 (section 2): the driver's room
   form with walked2's citations and walked's values, from which walked3 and the halts top both follow:
     H_txt_check_no_overread_A        a Theorem Labs lane's Cno102A_TopA.check_no_overread_holds_A_inst (lib/A/Prog/Cno102A_TopA.v;
                                      lib/A/Prog/Cno102A_*.v taken BY PATH from a working branch
                                      d4661e0cd87a, Cno102A_TopA.v, Cno102A_ImgA.v and SameAp_inst.v from its fast-forward
                                      d9b656d95780, where every callee text is at the walk's own CTX0 and HSAME is
                                      a Theorem Labs lane's premise-free fit of the A' same walk
                                      SameAp_inst.same_holds_Ap_HSAME_fit_s (its strcmp and bcmp rows discharged in that
                                      file; SameAp_*.v taken BY PATH from a working branch
                                      2df643bd333c) at CTX0 := iface_ctx0: HPN walked2's parse_noting walk at
                                      drv3_pj_parse_A below, HPJFREE drv3_pj_free_A below, HRO the driver's ran_out citation,
                                      AMALLOC / AFREE the shared rows;
     H_txt_check_as_written_A         a Theorem Labs lane's Caw102A_Top.caw_A_top (lib/A/Prog/Caw102A_Top.v:156; Caw102A_Base.v,
                                      Caw102A_Top.v, Caw102A_WA0..6.v taken BY PATH from
                                      a working branch d089ac67e34b) at PA := PI_prog_A,
                                      B := TfibB, CTX0 := iface_ctx0; CWI Caw102A_Img.caw_img_A (lib/A/Prog/Caw102A_Img.v:81),
                                      PAL PALibA.palib_A, AFREE the shared drv3_afree_A, HRANOUT the driver's
                                      ran_out citation; AMALLOC and HEXV below;
     H_txt_check_reject_clean_starved_A
                                      a Theorem Labs lane's CrsTopAp.crs_holds_Ap (lib/A/Prog/CrsTopAp.v:499; its files taken BY PATH
                                      from a working branch d664902eef28) at CTX0 := iface_ctx0: check_reject_clean
                                      and fuzz_alloc_live by walked2's citations, ran_out by the driver's, fuzz_alloc_count
                                      / fail by
                                      PwAllocSurf.fuzz_alloc_count_holds / fuzz_alloc_fail_holds (lib/A/Prog/PwAllocSurf.v:808,
                                      :812, PST_unowned by PwAllocSurfSat.PST_unowned_at_TfibB), pj_parse by drv3_pj_parse_A
                                      below at every cursor set, the class-1 frame row
                                      drv3_asmr1_A below (FCm01xm.stack_malloc1_contract_xm kept by xs_placed_cf, as
                                      lib/AU/FCxmCfxB.v:69 does at B'), pj_write drv3_pj_write_A, fuzz_free
                                      drv3_fuzz_free_A and fuzz_free_null drv3_fuzz_free_null_A below;
     H_txt_pj_free_A                  a Theorem Labs lane's S6PjFreeTop.pj_free_holds (lib/A/Prog/S6PjFreeTop.v:161; S6PjFree*.v
                                      taken BY PATH from a working branch 0bda57e5972c) at
                                      ARx := iface_ARx: LAWS YGcallcf.AR_laws_x_xs, TL PALibA.palib_A, VISF drv3_pjf_visf_A
                                      below (YGcfFsVis.ARx_frame_hull_vis_cf_ok through the first conjunct), the image
                                      facts S6ImgWit.s6w_* (lib/A/Prog/S6ImgWit.v), AIM S6ImgWit.s6w_aim; FREE
                                      drv3_fuzz_free_A below;
     H_txt_pj_parse_A                 PjParseA_top.pj_parse_holds_A (lib/A/Prog/PjParseA_top.v:133; lib/A/Prog/PjParseA_*.v
                                      at the version whose AF is the keep row
                                      YGcfMallocComposeKeep.afree_realizes_cf_rh_keep) at CTX0 := iface_ctx0, every CW:
                                      AF the shared drv3_afree_A;
                                      AU drv3_aunpoison_A and TPV drv3_parse_value_A below;
     XM_LIB, XN_LIB                   := fun _ => 0: they occur neither in TFIB_T_closed_A nor in any remaining hypothesis.
   drv3_pj_write_A (crs_holds_Ap's HT_pj_write) is a Theorem Labs lane's PRW_pj_write.pjw_holds_lc (lib/A/Prog/PRW_pj_write.v:2537;
   PRW_pj_write.v, PRW_S7bWit.v, PRW_S7bLitWit.v and their closure taken BY PATH from a working branch
   f75b9f6e6fa6) at ARx := iface_ARx, CTX0 := iface_ctx0, n := DOC_D: LAWS YGcallcf.AR_laws_x_xs, segs_low the class
   field pa_segs_low, the image facts PRW_S7bWit.s7bw_* and PRW_S7bLitWit.s7bl_pjw_hlit, AMS S6ImgWit.s6w_aim, S9_CF by
   projection, HFREE drv3_fuzz_free_A; its argument pjw_ARGCNT (the class-24 bound at its fuzz_free call,
   from a model-run position) by a Theorem Labs lane's PresetRoomCounts.counts_of_room_pos_rl (lib/Spec/PresetRoomCounts.v:60);
   HWV drv3_write_value_A and HPUT drv3_put_A below.
   drv3_put_A is a Theorem Labs lane's S7a_put.put_holds (lib/A/Prog/S7a_put.v:3060; S7a_put.v, S7a_put_wit.v taken BY PATH from
   a working branch 51391f2ec30d), drv3_indent_A its S7a_indent.indent_holds (S7a_indent.v,
   S7a_indent_wit.v taken BY PATH from a working branch a8d2be84a39d), drv3_put_string_A its
   PRW_put_string.put_string_holds and drv3_write_value_A its PRW_write_value.write_value_holds (PRW_put_string*.v taken
   BY PATH from a working branch f75b9f6e6fa6), each at ARx := iface_ARx, CTX0 := iface_ctx0, every
   image fact by a citation of an existing witness file (S7a_put_wit, S7a_indent_wit, PRW_S7bWit, PRW_S7bLitWit), the
   frame laws by YGcallcf / YGcallScf, the rows memcpy (Cno102A_TopA.cn_memcpy_A_inst), strlen (drv3_strlen_A), class-0
   frame (drv3_asmr0_A); write_value's jump-table fact HJT by drv3_wv_hjt_A below (one closed boolean per table word, the
   route of the B' twin WriteValueB_Wit.wvw_hjt).
   drv3_fuzz_free_A (crs_holds_Ap's HT_fuzz_free, pj_free_holds' FREE, pjw_holds_lc's HFREE) is a Theorem Labs lane's
   FuzzFree.fuzz_free_holds (lib/A/Prog/FuzzFree.v:953, on the cut) through PjParseA_inst.pjp_inst_ff (PAL
   PALibA.palib_A, pal_pst_ok FuzzAllocAccInst102.acc_pal_pst_ok_A), its rows AFREE the shared drv3_afree_A and
   AUNPOISON drv3_aunpoison_A below.
   THE UNPOISON / POISON ROWS drv3_aunpoison_A / drv3_apoison_A are a Theorem Labs lane's CfPoison102.preset_aunpoison_cf102 /
   preset_apoison_cf102 (lib/A/CfPoison102.v, int102's POISONSWAP blob 361400873424 = a working branch
   415c6c3e2969, which cites a Theorem Labs lane's lemma CfApiPreset.poison_next_vis_cf INSIDE the file and has NO
   poison_next_vis_cf Section hypothesis), at the ARcf laws YG0lawscf.AR_laws_ok_cf and AD2l.TfibB_syms (two args, no
   stand-in). int102 carries poisonswap and its VrdTop (below) cites it, so both images cite the rows one way.
   drv3_fuzz_realloc_A (S7a_put.put_holds' HREAL) is a Theorem Labs lane's FuzzReallocAp.fuzz_realloc_holds_Ap
   (lib/A/Prog/FuzzReallocAp.v:2322, taken BY PATH from a working branch 9d68c8d85aa0) at
   B := TfibB, ARcfx = iface_ARx: PAL PALibA.palib_A; its static set PST := FuzzReallocAp.ra_cells with PST_cells
   FuzzReallocAp.ra_cell_in and PST_ok / PST_errno / MOST_ok / OWN_ok / PST_sub / PST_own_out / PST_most_out by
   computation at TfibB (drv3_ra_* below, the route of a Theorem Labs lane's AllocTopsA102.v at_*, a working branch
   d6bfa1b28502, a file not on this line); FMALLOC drv3_fuzz_malloc_A below; AUNPOISON / APOISON drv3_aunpoison_A /
   drv3_apoison_A; CF_unpoison / CF_poison by computation; the RELRO image rows by lib/A/CfAroPresetA.v
   (relro_seg_preset_A, errno_relro_preset_A, relro_top_preset_A, ro_reads_nw_preset_A, the range equation by
   computation) and PST_aro by drv3_ra_pst_aro below; AREAL_cf drv3_arealloc_A below (the keep _k form).
   drv3_fuzz_malloc_A is a Theorem Labs lane's FuzzMalloc.fuzz_malloc_holds (lib/A/Prog/FuzzMalloc.v, taken BY PATH from
   a working branch 2ba86cb8bc30, the kit's batch text with the outcome conjunct): PAL PALibA.palib_A,
   pal_pst_ok FuzzAllocAccInst102.acc_pal_pst_ok_A, AMALLOC the shared drv3_amalloc_A, APOISON drv3_apoison_A.
   drv3_parse_value_A (pj_parse_holds_A's TPV) is VrdTop.vrd_parse_value_holds (lib/A/VrdTop.v:1356) at
   CTX0 := iface_ctx0, depth 0: its Section top names the three allocator rows in their keep forms, so AREAL_cf is the
   row drv3_arealloc_A and AMALLOC / AFREE the shared keep rows, each as it is (the realloc text is VrdTop's
   own citation of FuzzReallocAp). VrdTop.v and its closure (lib/A/Vrd*.v, the callee walks lib/A/Prog/S4_Ps*.v,
   PwGrow*.v, ExUtf8W*.v, hex4_x.v, hex4_mn.v) are cited at that version, the one whose Section top takes the keep rows.
   drv3_snprintf_A (put_string_holds' SNP) is a Theorem Labs lane's PSnpRowA.snprintf_row_A_inst (lib/A/Prog/PSnpRowA.v,
   taken BY PATH from a working branch b83b4e86aa29), stated at this premise's instance.
   drv3_aread_check_A (walked2's H_aread_check_stmt_cf_A) is a Theorem Labs lane's AD2mcfh.tfib_ARDCHK at TfibB (its TfibSyms by
   AD2l.TfibB_syms; the cfh set taken BY PATH from a working branch eb2778ca6e2f).
   THE SECTION HYPOTHESES OF THIS TOP: none. caw_A_top's HEXV is drv3_ex_value_A, S8aTopClosed.ex_value_A_inst_drv
   (cited, no premise). walked2's check_round_trip text is drv3_check_round_trip_A,
   Crt102TopInstA.crt102_top_TfibA_inst, with its tx_value premise ATxValueInst.tx_value_A_inst (both cited).
   fuzz_realloc_holds_Ap's and VrdTop's AREAL_cf is drv3_arealloc_A, AllocAssembleA.arealloc_realizes_cf_A (the same
   statement, cited). walked2's free row is drv3_afree_A, CfFreeKeepA.afree_realizes_cf_rh_keep_A (the same statement,
   cited). walked2's malloc row, at every float state, is drv3_amalloc_A,
   CfMallocKeepA.amalloc_realizes_cf_keep_closed_A (the same statement, cited).
   The live real stack (#102) is no premise: walked2 has none (the driver walk proves it from main's entry).
   rule 24: no function proved (kind: composition by citation). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK11 YM05 YG0d YG0f YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn FCifaceCf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallScf YGcfFsVis YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB1v AD2l CfImgA CfParamsPreset Img0 PALibA CfAroPresetA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetCfnA PresetD1preA PresetD1pA PresetD2pA PresetD2pAPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetD2oA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base PRH_FnAlloc PRH_FnCheck PRH_FnPj PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnWriter PRH_FnParse Ent102InstA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfHp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Listing_prog PAImg_prog FCm01xm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Ent102DrvTopA2 Ent102SeamA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
(* the cited theorems' files (Required; cited by full path below) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Caw102A_Img Caw102A_Top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require CrsTopAp FuzzFreeNull.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S6ImgWit S6PjFreeTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PwAllocSurf PwAllocSurfSat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Cno102A_TopA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_pj_write PRW_S7bWit PRW_S7bLitWit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PjParseA_inst PjParseA_top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S7a_put S7a_put_wit S7a_indent S7a_indent_wit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_put_string PRW_put_string_e PRW_write_value.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_HShadow.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AImgShadowVisCf PSstrRo AImgCells.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfPoison102 CfApiPreset VrdTop AD2mcfh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require FuzzReallocAp FuzzMalloc FuzzAllocAccInst102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgA S1ImgCheck PSnpRowA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AllocAssembleA CfFreeKeepA CfMallocKeepA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102TopInstA ATxValueInst S8aTopClosed.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI04 YG0n YP0b YP08 YImgTop YGcallSnp YGcallSnpCk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
(* the image-free checkers of the B' twin's HJT witness (cited, not restated) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require WriteValueB_Wit.
From Stdlib Require Import Lia.
From Stdlib Require Bool.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation PIc := PresetCfnA.preset_prh_img.
#[local] Abbreviation RLc := (@PRH_Base.prh_room_live_a8 CfParamsPreset.CfParams_preset).
#[local] Abbreviation SKc := PresetCfnA.preset_sink_head.
#[local] Abbreviation C0 := PresetCfnA.iface_ctx0.
#[local] Abbreviation TA := AD2l.TfibB.
#[local] Abbreviation PAr rc := (@PAImg_prog.PI_prog_A rc).
#[local] Abbreviation ARi rc :=
  (@PresetCfnA.iface_ARx rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB).
(* the driver's instances (lib/A/PresetD2pAPf.v: ci := CfImg_A, cp := CfParams_preset, RL := prh_room_live_a8), so the
   callee texts below elaborate at them *)
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance PRH_Base.prh_room_live_a8.

(* pjw_ARGCNT, pj_write's one ruled argument (lib/A/Prog/PRW_pj_write.v:1326, the B' twin's the same): at every state
   pj_write's journal reaches with a model-run position, the class-24 live count is at most L24 + DRV. That is the
   second conjunct of PresetRoomCounts.counts_of_room_pos_rl at that position. *)
Ltac drv3_argcnt :=
  intros; hnf; intros;
  lazymatch goal with |- YGcfRoomLive.ccnt24 ?S' <= _ =>
    match goal with Hp : PresetRoomPos.iface_room_pos _ _ _ _ _ _ S' |- _ =>
      exact (proj2 (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ _ Hp)) end end.

(* ---------------------------------------------------------------------- *)
(* 1. The discharges that need no Section hypothesis. *)

(* the class-1 frame-area row at ARcf /\ xs_placed_cf (crs_holds_Ap's HX_asmr): a Theorem Labs lane's
   FCm01xm.stack_malloc1_contract_xm (lib/A/FCm01xm.v:32) at ARcf, kept across the conjunct by
   YGcallMxmn.astack_malloc_realizes_xm_conj, as lib/AU/FCxmCfxB.v:69 states the B' twin *)
Lemma drv3_asmr1_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.astack_malloc_realizes_xm (fx := fx) AB1v.tfibsegs TA
    (fun ly S Hp W mem md => YG0ncf.ARcf (rc := rc) (cp := CP) AB1v.tfibsegs TA ly S Hp W mem md /\
       YG0ncf.xs_placed_cf (rc := rc) ly S) 1.
Proof.
intros rc fx.
exact (YGcallMxmn.astack_malloc_realizes_xm_conj (fx := fx) AB1v.tfibsegs TA (YG0ncf.ARcf (rc := rc) (cp := CP) AB1v.tfibsegs TA)
  (fun ly S => YG0ncf.xs_placed_cf (rc := rc) ly S) 1 YGcallScf.xs_placed_cf_set_fs
  (FCm01xm.stack_malloc1_contract_xm (fx := fx) TA (YG0ncf.ARcf (rc := rc) (cp := CP) AB1v.tfibsegs TA)
    (FCifaceCf.fs_iface_ARcf (cp := CP) AB1v.tfibsegs TA (YG0lawscf.AR_laws_ok_cf (cp := CP) AB1v.tfibsegs TA))
    AD2l.TfibB_syms)).
Qed.

(* crs_holds_Ap's HT_fuzz_alloc_count / HT_fuzz_alloc_fail: a Theorem Labs lane's accessor walks at TfibB *)
Lemma drv3_fuzz_alloc_count_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_alloc_count_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TA (ARi rc) SKc.
Proof. intros rc fx. exact (PwAllocSurf.fuzz_alloc_count_holds (fx := fx) (rc := rc) (SK := SKc) TA). Qed.
Lemma drv3_fuzz_alloc_fail_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_alloc_fail_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TA (ARi rc) SKc.
Proof.
intros rc fx.
exact (PwAllocSurf.fuzz_alloc_fail_holds (fx := fx) (rc := rc) (SK := SKc) TA PwAllocSurfSat.PST_unowned_at_TfibB).
Qed.

(* pj_free_holds' VISF at iface_ARx: the cf instance's frame-hull visibility through the first conjunct (as
   lib/B/Prog/pj_free_iface.v pf_wit_visf_iface does at B') *)
Lemma drv3_pjf_visf_A : forall rc : YM05.RunCeil,
  YGcfFsVis.ARx_frame_hull_vis (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (PAr rc)) TA (ARi rc).
Proof.
intros rc ly S Hp W mem md cid pos [HA _] Hin.
exact (YGcfFsVis.ARx_frame_hull_vis_cf_ok _ TA (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TA) ly S Hp W mem md cid pos HA Hin).
Qed.

(* the class-0 frame-area row at ARcf /\ xs_placed_cf (PRW_put_string's ASM0): a Theorem Labs lane's
   FCm01xm.stack_malloc0_contract_xm (lib/A/FCm01xm.v:24) at ARcf, kept across the conjunct, as drv3_asmr1_A *)
Lemma drv3_asmr0_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.astack_malloc_realizes_xm (fx := fx) AB1v.tfibsegs TA
    (fun ly S Hp W mem md => YG0ncf.ARcf (rc := rc) (cp := CP) AB1v.tfibsegs TA ly S Hp W mem md /\
       YG0ncf.xs_placed_cf (rc := rc) ly S) 0.
Proof.
intros rc fx.
exact (YGcallMxmn.astack_malloc_realizes_xm_conj (fx := fx) AB1v.tfibsegs TA (YG0ncf.ARcf (rc := rc) (cp := CP) AB1v.tfibsegs TA)
  (fun ly S => YG0ncf.xs_placed_cf (rc := rc) ly S) 0 YGcallScf.xs_placed_cf_set_fs
  (FCm01xm.stack_malloc0_contract_xm (fx := fx) TA (YG0ncf.ARcf (rc := rc) (cp := CP) AB1v.tfibsegs TA)
    (FCifaceCf.fs_iface_ARcf (cp := CP) AB1v.tfibsegs TA (YG0lawscf.AR_laws_ok_cf (cp := CP) AB1v.tfibsegs TA))
    AD2l.TfibB_syms)).
Qed.

(* the image's shadow bytes are mapped (S7a_put's and PRW_put_string's HIMGSH) at iface_ARx: a Theorem Labs lane's
   AImgShadowVisCf.tfib_img_shadow_vis_cf (lib/A/AImgShadowVisCf.v:32) through the first conjunct, at CfImg_A's bounds
   (YImgTop's IMG_LO / IMG_TOP by conversion), as Cno102A_TopA.v cn_imgsh_A does at ARcf *)
Lemma drv3_imgsh_A : forall rc : YM05.RunCeil,
  PRW_HShadow.ARx_img_shadow_vis (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (PAr rc)) (ARi rc).
Proof.
intros rc ly S Hp W mem md a [HA _] Ha.
exact (AImgShadowVisCf.tfib_img_shadow_vis_cf (cp := CP) _ TA AD2l.TfibB_syms ly S Hp W mem md a HA Ha).
Qed.

(* the __wrap_strlen row (write_value_holds' STRLEN, PRW_put_string's ASTRLEN): a Theorem Labs lane's
   PSstrRo.ps_strlen_xrom_xs_A (lib/A/PSstrRo.v:77) at CfImg_A's strlen pc, the listing's by computation on the closed
   terms *)
Lemma drv3_strlen_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.astrlen_realizes_xrom (fx := fx) (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (PAr rc)) TA (ARi rc)
    (@YC4aP.pa_relro_lo rc Listing_prog.A_prog_listing (PAr rc)) (@YC4aP.pa_relro_hi rc Listing_prog.A_prog_listing (PAr rc))
    (@YC4aP.pa_sigma rc Listing_prog.A_prog_listing (PAr rc) YPsym.AS___wrap_strlen).
Proof.
intros rc fx.
pose proof (PSstrRo.ps_strlen_xrom_xs_A (fx := fx) (rc := rc) (cp := CP) TA AD2l.TfibB_syms
  (@YC4aP.pa_relro_lo rc Listing_prog.A_prog_listing (PAr rc)) (@YC4aP.pa_relro_hi rc Listing_prog.A_prog_listing (PAr rc)))
  as H.
match type of H with YGcallMxmn.astrlen_realizes_xrom _ _ _ _ _ ?p =>
  replace (@YC4aP.pa_sigma rc Listing_prog.A_prog_listing (PAr rc) YPsym.AS___wrap_strlen) with p;
  [exact H | apply Z.eqb_eq; vm_compute; reflexivity] end.
Qed.

(* write_value_holds' HJT (lib/A/Prog/PRW_write_value.v:1229-1241): the seven table words of the tag switch, one
   closed boolean each, by the B' twin's route (lib/B/Prog/WriteValueB_Wit.v wvw_jt_b / wvw_jt_all / wvw_hjt, its
   image-free checkers wvw_vm_b / wvw_ro_byte_b and their soundness lemmas cited), at PI_prog_A / TfibB *)
Section jt. Context {rc : YM05.RunCeil}.
#[local] Abbreviation SEGS := (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (PAr rc)).
#[local] Abbreviation VAL := (@YC4aP.pa_val rc Listing_prog.A_prog_listing (PAr rc)).
#[local] Abbreviation RLO := (@YC4aP.pa_relro_lo rc Listing_prog.A_prog_listing (PAr rc)).
#[local] Abbreviation RHI := (@YC4aP.pa_relro_hi rc Listing_prog.A_prog_listing (PAr rc)).
#[local] Abbreviation JTW k := (PRW_write_value.WV_JTW (rc := rc) (PA := PAr rc) k).
#[local] Abbreviation JA k := (VAL (YP0b.A_OBJ 2) + PRW_write_value.WV_JT + 4 * Z.of_nat k).
Definition drv3_wv_jt_b (k : nat) : bool :=
  WriteValueB_Wit.wvw_vm_b SEGS (JA k) 4 (JTW k) && (0 <=? JTW k) && (JTW k <=? 2 ^ 31 - 1) && (0 <=? JA k) &&
  (JA k + 4 <=? YG0f.kLowMemEnd) &&
  ((JA k + 4 <=? VAL (YP0b.A_OBJ 0)) || (VAL (YP0b.A_OBJ 0) + 8 <=? JA k)) &&
  ((JA k + 4 <=? VAL (YP0b.A_OBJ 12)) || (VAL (YP0b.A_OBJ 12) + 8 <=? JA k)) &&
  YP08.zallb (WriteValueB_Wit.wvw_ro_byte_b SEGS RLO RHI TA) (JA k) 4.
Lemma drv3_wv_jt_all : forallb drv3_wv_jt_b (seq 0 7) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma drv3_wv_hjt_A : forall k : nat, (k < 7)%nat ->
  YI04.val_mem SEGS (fun _ => None) (JA k) 4 (JTW k) /\ 0 <= JTW k <= 2 ^ 31 - 1 /\ 0 <= JA k /\
  JA k + 4 <= YG0f.kLowMemEnd /\
  (JA k + 4 <= VAL (YP0b.A_OBJ 0) \/ VAL (YP0b.A_OBJ 0) + 8 <= JA k) /\
  (JA k + 4 <= VAL (YP0b.A_OBJ 12) \/ VAL (YP0b.A_OBJ 12) + 8 <= JA k) /\
  (forall i, 0 <= i < 4 -> YG0d.in_img SEGS (JA k + i) /\ PresetRodata.in_roP SEGS RLO RHI (JA k + i) /\
     ~ Exists (YG0n.in_zr (JA k + i)) (YG0f.as_owned_static TA) /\
     ~ (YG0f.as_errno TA <= JA k + i < YG0f.as_errno TA + 4)).
Proof.
intros k Hk.
assert (H : drv3_wv_jt_b k = true).
{ pose proof drv3_wv_jt_all as A. rewrite List.forallb_forall in A. apply A. apply List.in_seq. lia. }
unfold drv3_wv_jt_b in H.
apply andb_prop in H as [H Hro]. apply andb_prop in H as [H Hd12]. apply andb_prop in H as [H Hd0].
apply andb_prop in H as [H Hlow]. apply andb_prop in H as [H Ha0]. apply andb_prop in H as [H Hv1].
apply andb_prop in H as [Hvm Hv0].
apply Z.leb_le in Hv0. apply Z.leb_le in Hv1. apply Z.leb_le in Ha0. apply Z.leb_le in Hlow.
split; [exact (WriteValueB_Wit.wvw_vm_sound _ _ _ _ Hvm)|].
split; [split; [exact Hv0 | exact Hv1]|].
split; [exact Ha0|]. split; [exact Hlow|].
split; [apply Bool.orb_true_iff in Hd0 as [D|D]; apply Z.leb_le in D; [left|right]; exact D|].
split; [apply Bool.orb_true_iff in Hd12 as [D|D]; apply Z.leb_le in D; [left|right]; exact D|].
exact (WriteValueB_Wit.wvw_ro_range_sound _ _ _ _ _ 4 Hro).
Qed.
End jt.

(* the unpoison / poison rows at TfibB (header): CfPoison102's rows, poison_next_vis_cf by CfApiPreset's lemma *)
Lemma drv3_aunpoison_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @YGcfHp.aunpoison_realizes_cf fx rc CfImgA.CfImg_A CfParamsPreset.CfParams_preset AB1v.tfibsegs AD2l.TfibB.
Proof.
intros rc fx.
exact (CfPoison102.preset_aunpoison_cf102 (fx := fx) (rc := rc) TA (YG0lawscf.AR_laws_ok_cf (cp := CP) AB1v.tfibsegs TA)
  AD2l.TfibB_syms).
Qed.
Lemma drv3_apoison_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @YGcfHp.apoison_realizes_cf fx rc CfImgA.CfImg_A CfParamsPreset.CfParams_preset AB1v.tfibsegs AD2l.TfibB.
Proof.
intros rc fx.
exact (CfPoison102.preset_apoison_cf102 (fx := fx) (rc := rc) TA (YG0lawscf.AR_laws_ok_cf (cp := CP) AB1v.tfibsegs TA)
  AD2l.TfibB_syms).
Qed.

(* fuzz_realloc_holds_Ap's static-set stand-ins at TfibB, by computation (header): PST := FuzzReallocAp.ra_cells; the
   image-free checkers S1ImgCheck.pst_allb (a range list inside another) and FuzzAllocAccInst102.acc_dj (a range list
   off a range), each with its soundness lemma *)
Definition drv3_mem_b (a : Z) (P : list (Z * Z)) : bool :=
  List.existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) P.
Lemma drv3_mem_b_sound : forall a P, drv3_mem_b a P = true -> List.Exists (YG0n.in_zr a) P.
Proof.
intros a P H. unfold drv3_mem_b in H. apply List.existsb_exists in H as [r [Hr Hb]].
apply List.Exists_exists. exists r. split; [exact Hr|]. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold YG0n.in_zr. lia.
Qed.
Lemma drv3_sub_ok : forall P Q, S1ImgCheck.pst_allb (fun a => drv3_mem_b a Q) P = true ->
  forall a, List.Exists (YG0n.in_zr a) P -> List.Exists (YG0n.in_zr a) Q.
Proof. intros P Q H a Ha. apply drv3_mem_b_sound. exact (S1ImgCheck.pst_allb_sound _ _ a H Ha). Qed.
Lemma drv3_out_ok : forall P s, List.forallb (fun r => FuzzAllocAccInst102.acc_dj r s) P = true ->
  forall a, YG0n.in_zr a s -> ~ List.Exists (YG0n.in_zr a) P.
Proof.
intros P s H a Hs HP. apply List.Exists_exists in HP as [r [Hr Har]]. rewrite List.forallb_forall in H.
exact (FuzzAllocAccInst102.acc_dj_ok r s a (H r Hr) Har Hs).
Qed.
#[local] Abbreviation RA := FuzzReallocAp.ra_cells.
#[local] Abbreviation PSTA := (@PRH_Base.prh_pst PIc).
(* g_own_ran_out (atom 13, one byte) and g_most (atom 14, eight bytes): the cells FuzzReallocAp's OWN_ok / MOST_ok name *)
#[local] Abbreviation OWNV := (PAImg_prog.A_prog_val (YP0b.A_OBJ 13)).
#[local] Abbreviation MOSTV := (PAImg_prog.A_prog_val (YP0b.A_OBJ 14)).
Lemma drv3_ra_pst_sub : forall a, List.Exists (YG0n.in_zr a) RA -> List.Exists (YG0n.in_zr a) PSTA.
Proof. apply drv3_sub_ok. vm_compute. reflexivity. Qed.
Lemma drv3_ra_own_pst : forall a, List.Exists (YG0n.in_zr a) [(OWNV, 1)] -> List.Exists (YG0n.in_zr a) PSTA.
Proof. apply drv3_sub_ok. vm_compute. reflexivity. Qed.
Lemma drv3_ra_most_pst : forall a, List.Exists (YG0n.in_zr a) [(MOSTV, 8)] -> List.Exists (YG0n.in_zr a) PSTA.
Proof. apply drv3_sub_ok. vm_compute. reflexivity. Qed.
Lemma drv3_ra_own_out : ~ List.Exists (YG0n.in_zr OWNV) RA.
Proof. apply (drv3_out_ok RA (OWNV, 1)); [vm_compute; reflexivity | unfold YG0n.in_zr; cbn [fst snd]; lia]. Qed.
Lemma drv3_ra_most_out : forall o, 0 <= o < 8 -> ~ List.Exists (YG0n.in_zr (MOSTV + o)) RA.
Proof.
intros o Ho. apply (drv3_out_ok RA (MOSTV, 8)); [vm_compute; reflexivity | unfold YG0n.in_zr; cbn [fst snd]; lia].
Qed.
Section ra. Context {rc : YM05.RunCeil}.
#[local] Abbreviation SEGS := (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (PAr rc)).
Lemma drv3_ra_pst_ok : forall a, List.Exists (YG0n.in_zr a) RA ->
  YG0d.in_img SEGS a /\ ~ List.Exists (YG0n.in_zr a) (YG0f.as_owned_static TA).
Proof.
intros a H. pose proof (drv3_ra_pst_sub a H) as Hp.
exact (conj (S1ImgA.pst_in_img_A a Hp) (proj1 (FuzzAllocAccInst102.acc_pal_pst_ok_A a Hp))).
Qed.
Lemma drv3_ra_pst_errno : forall a, List.Exists (YG0n.in_zr a) RA -> ~ (YG0f.as_errno TA <= a < YG0f.as_errno TA + 4).
Proof. intros a H. exact (proj2 (FuzzAllocAccInst102.acc_pal_pst_ok_A a (drv3_ra_pst_sub a H))). Qed.
Lemma drv3_ra_most_ok : forall o, 0 <= o < 8 ->
  YG0d.in_img SEGS (MOSTV + o) /\ ~ List.Exists (YG0n.in_zr (MOSTV + o)) (YG0f.as_owned_static TA) /\
  ~ (YG0f.as_errno TA <= MOSTV + o < YG0f.as_errno TA + 4).
Proof.
intros o Ho. assert (Hp : List.Exists (YG0n.in_zr (MOSTV + o)) PSTA).
{ apply drv3_ra_most_pst. apply List.Exists_cons_hd. unfold YG0n.in_zr. cbn [fst snd]. lia. }
destruct (FuzzAllocAccInst102.acc_pal_pst_ok_A _ Hp) as [H1 H2].
exact (conj (S1ImgA.pst_in_img_A _ Hp) (conj H1 H2)).
Qed.
Lemma drv3_ra_own_ok :
  YG0d.in_img SEGS OWNV /\ ~ List.Exists (YG0n.in_zr OWNV) (YG0f.as_owned_static TA) /\
  ~ (YG0f.as_errno TA <= OWNV < YG0f.as_errno TA + 4).
Proof.
assert (Hp : List.Exists (YG0n.in_zr OWNV) PSTA).
{ apply drv3_ra_own_pst. apply List.Exists_cons_hd. unfold YG0n.in_zr. cbn [fst snd]. lia. }
destruct (FuzzAllocAccInst102.acc_pal_pst_ok_A _ Hp) as [H1 H2].
exact (conj (S1ImgA.pst_in_img_A _ Hp) (conj H1 H2)).
Qed.
(* CfImg_A's two runtime call targets are the listing's entries *)
Lemma drv3_ra_cf_unpoison :
  @YGcfNames.cf_pc_unpoison CfImgA.CfImg_A = @YC4aP.pa_sigma rc Listing_prog.A_prog_listing (PAr rc)
    YPsym.AS___asan_unpoison_memory_region.
Proof. vm_compute. reflexivity. Qed.
Lemma drv3_ra_cf_poison :
  @YGcfNames.cf_pc_poison CfImgA.CfImg_A = @YC4aP.pa_sigma rc Listing_prog.A_prog_listing (PAr rc)
    YPsym.AS___asan_poison_memory_region.
Proof. vm_compute. reflexivity. Qed.
(* fuzz_realloc_holds_Ap's PST_aro: the walk's statics are no byte the call memory's arodata_ok_cf covers. A covered
   byte is RELRO or a report read inside a non-writable segment (CfAroPresetA.ro_reads_nw_preset_A), and no static is
   read-only (S1ImgA.pst_not_ro_A); as FuzzFree.v ff_pst_aro *)
Lemma drv3_ra_pst_aro : forall a, YG0dcf.aro_addr_cf (ci := CfImgA.CfImg_A) a -> ~ List.Exists (YG0n.in_zr a) RA.
Proof.
intros a Ha Hx. apply (S1ImgA.pst_not_ro_A a (drv3_ra_pst_sub a Hx)). destruct Ha as [Ha | Ha].
- right. unfold PAImg_prog.A_prog_relro_lo, PAImg_prog.A_prog_relro_hi.
  cbv [YGcfNames.cf_relro_lo YGcfNames.cf_relro_hi CfImgA.CfImg_A] in Ha. exact Ha.
- left. pose proof CfAroPresetA.ro_reads_nw_preset_A as RONW.
  unfold YGcfAroBridge.ro_reads_nw_t in RONW. rewrite List.Forall_forall in RONW.
  apply List.Exists_exists in Ha as (r & Hr & Hra). unfold YG0n.in_zr in Hra.
  destruct (RONW r Hr) as (_ & sg & Hin & NW & L & R). exists sg. split; [exact Hin|]. split; [exact NW | lia].
Qed.
End ra.

(* put_string_holds' SNP (header) *)
Lemma drv3_snprintf_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallSnp.asnprintf_realizes_xrom (fx := fx) (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (PAr rc)) TA (ARi rc)
    (@YC4aP.pa_relro_lo rc Listing_prog.A_prog_listing (PAr rc)) (@YC4aP.pa_relro_hi rc Listing_prog.A_prog_listing (PAr rc))
    (YGcallSnpCk.FF_esc YImgTop.IMG_LO AImgCells.A_GOT_STACK_CHK_GUARD) PRH_Base.STK_RT_PRINTF
    AImgCells.A_GOT_STACK_CHK_GUARD AImgCells.A_STACK_CHK_GUARD YImgTop.IMG_LO YImgTop.IMG_TOP
    (PRW_put_string_e.ps_snp_cr (rc := rc) (PA := PAr rc))
    (@YC4aP.pa_sigma rc Listing_prog.A_prog_listing (PAr rc) YPsym.AS___wrap_snprintf).
Proof. intros rc fx. exact (PSnpRowA.snprintf_row_A_inst rc fx). Qed.

(* THE READ INTERCEPTOR'S CHECK (walked2's H_aread_check_stmt_cf_A): a Theorem Labs lane's AD2mcfh.tfib_ARDCHK
   (lib/A/AD2mcfh.v, the cfh set taken BY PATH from a working branch eb2778ca6e2f) at TfibB, its one
   Section hypothesis TfibSyms by AD2l.TfibB_syms; its aread_check_stmt is PresetD1preA.aread_check_stmt_cf by
   conversion, at fx := YK11.fx0, cp := CfParams_preset *)
Lemma drv3_aread_check_A : forall rc : YM05.RunCeil,
  PresetD1preA.aread_check_stmt_cf (fx := YK11.fx0) (rc := rc) (ci := CfImgA.CfImg_A)
    (cp := CfParamsPreset.CfParams_preset) AD2l.TfibB.
Proof. intros rc. exact (AD2mcfh.tfib_ARDCHK AD2l.TfibB AD2l.TfibB_syms). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE THIRD COMPOSED TOP. *)
Section walked3.

(* THE SECOND ALLOCATOR INSTANCE at TfibB, malloc and free in their keep forms (free primed, under the re-hide); amalloc
   at every float state, as walked2 states it. Every callee that takes an allocator row (FuzzMalloc, Caw102A_Top,
   Cno102A_Top, VrdTop, PjParseA_top, PjParseA_inst) takes it in this keep form, so each gets the row as it is. *)
(* the malloc row: CfMallocKeepA.amalloc_realizes_cf_keep_closed_A, the same statement *)
Lemma drv3_amalloc_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A)
    (cp := CfParamsPreset.CfParams_preset) AB1v.tfibsegs AD2l.TfibB.
Proof. intros rc fx. exact (CfMallocKeepA.amalloc_realizes_cf_keep_closed_A (fx := fx) (rc := rc)). Qed.
(* the free row: CfFreeKeepA.afree_realizes_cf_rh_keep_A, the same statement *)
Lemma drv3_afree_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A)
    (cp := CfParamsPreset.CfParams_preset) AB1v.tfibsegs AD2l.TfibB.
Proof. intros rc fx. exact (CfFreeKeepA.afree_realizes_cf_rh_keep_A (fx := fx) (rc := rc)). Qed.
(* (the read interceptor's check is now cited: drv3_aread_check_A above) *)
(* walked2's check_round_trip text: Crt102TopInstA.crt102_top_TfibA_inst, the round-trip corollary at the instance
   (CTX0 := iface_ctx0, the literals Ent102InstA.ia_mod_at / ia_stamp); its one premise, tx_value's text at the
   instance and every float state, is ATxValueInst.tx_value_A_inst *)
Lemma drv3_check_round_trip_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_check_round_trip_A fx rc Ent102InstA.ia_mod_at Ent102InstA.ia_stamp.
Proof.
intros rc fx.
exact (@Crt102TopInstA.crt102_top_TfibA_inst rc (fun fxk => @ATxValueInst.tx_value_A_inst rc fxk) fx).
Qed.
(* THE CITED WALKS' CALLEE TEXTS AND ROWS, each once, at the driver's instance *)
(* caw_A_top's HEXV: S8aTopClosed.ex_value_A_inst_drv, ex_value's text at the instance, with no premise *)
Lemma drv3_ex_value_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnEx.tex_value_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TA (ARi rc) SKc PRH_Base.DOC_D.
Proof. intros rc fx. exact (S8aTopClosed.ex_value_A_inst_drv rc fx). Qed.
(* fuzz_realloc_holds_Ap's and VrdTop's AREAL_cf: the realloc wrapper's row at the second allocator in its keep _k form
   (YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep, the leaf's memnorm keep and the room at k), at the instance:
   AllocAssembleA.arealloc_realizes_cf_A, the same statement *)
Lemma drv3_arealloc_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (Hp : list Z) (k : nat),
  YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP)
    (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (PAr rc)) AD2l.TfibB Hp
    (@YC4aP.pa_sigma rc Listing_prog.A_prog_listing (PAr rc) YPsym.AS___wrap_realloc) k.
Proof. exact AllocAssembleA.arealloc_realizes_cf_A. Qed.

(* tfuzz_free_specX (crs_holds_Ap's HT_fuzz_free, pj_free_holds' FREE, pjw_holds_lc's HFREE) *)
Lemma drv3_fuzz_free_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_free_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TA (ARi rc) SKc.
Proof.
intros rc fx.
exact (PjParseA_inst.pjp_inst_ff (rc := rc) (SK := SKc)
  (fun fy => drv3_afree_A rc fy)
  (fun fy => drv3_aunpoison_A rc fy) fx).
Qed.

(* tfuzz_free_null_specX (crs_holds_Ap's HT_fuzz_free_null): the kit's FuzzFreeNull.fuzz_free_null_holds at TfibB, its
   rows AUNPOISON drv3_aunpoison_A and pal_pst_ok FuzzAllocAccInst102.acc_pal_pst_ok_A *)
Lemma drv3_fuzz_free_null_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_free_null_specX (fx := fx) (PI := PIc) (PA := PAr rc) TA (ARi rc) SKc.
Proof.
intros rc fx.
eapply (FuzzFreeNull.fuzz_free_null_holds (fx := fx) (rc := rc) (SK := SKc) TA);
  first [ exact (drv3_aunpoison_A rc fx) | exact PALibA.palib_A | exact FuzzAllocAccInst102.acc_pal_pst_ok_A
        | exact AD2l.TfibB_syms ].
Qed.

(* fuzz_realloc_holds_Ap's FMALLOC (header): a Theorem Labs lane's FuzzMalloc.fuzz_malloc_holds at TfibB *)
Lemma drv3_fuzz_malloc_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_malloc_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (RL := RLc)
    (L := Listing_prog.A_prog_listing) (PA := PAr rc) TA (ARi rc) SKc.
Proof.
intros rc fx.
exact (FuzzMalloc.fuzz_malloc_holds (fx := fx) (SK := SKc) TA PALibA.palib_A FuzzAllocAccInst102.acc_pal_pst_ok_A
  (drv3_amalloc_A rc fx)
  (drv3_apoison_A rc fx) AD2l.TfibB_syms).
Qed.

(* S7a_put.put_holds' HREAL (header): FuzzReallocAp.fuzz_realloc_holds_Ap at TfibB *)
Lemma drv3_fuzz_realloc_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnAlloc.tfuzz_realloc_specX (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) (RL := RLc) (PI := PIc)
    (L := Listing_prog.A_prog_listing) (PA := PAr rc) TA (ARi rc) SKc.
Proof.
intros rc fx.
eapply (FuzzReallocAp.fuzz_realloc_holds_Ap (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A) (SK := SKc) TA PALibA.palib_A
  FuzzReallocAp.ra_cells).
all: first
  [ exact drv3_ra_pst_ok | exact FuzzReallocAp.ra_cell_in | exact drv3_ra_pst_errno | exact drv3_ra_most_ok
  | exact drv3_ra_own_ok | exact drv3_ra_pst_sub | exact drv3_ra_own_out | exact drv3_ra_most_out
  | exact (drv3_fuzz_malloc_A rc fx) | exact (drv3_aunpoison_A rc fx) | exact (drv3_apoison_A rc fx)
  | exact (drv3_arealloc_A rc fx) | exact drv3_ra_cf_unpoison | exact drv3_ra_cf_poison
  | exact CfAroPresetA.relro_seg_preset_A | exact (CfAroPresetA.errno_relro_preset_A TA AD2l.TfibB_syms)
  | exact CfAroPresetA.relro_top_preset_A | exact CfAroPresetA.ro_reads_nw_preset_A | exact drv3_ra_pst_aro
  | (split; vm_compute; reflexivity) ].
Qed.

(* pjw_holds_lc's HPUT, indent_holds' HPUT, put_string_holds' PUT and write_value_holds' PUT: a Theorem Labs lane's
   S7a_put.put_holds (lib/A/Prog/S7a_put.v:3060; S7a_put.v, S7a_put_wit.v taken BY PATH from
   a working branch 51391f2ec30d) at ARx := iface_ARx, CTX0 := iface_ctx0: LAWS YGcallcf.AR_laws_x_xs,
   TL PALibA.palib_A, the image facts S7a_put_wit.s7p_*, AMC Cno102A_TopA.cn_memcpy_A_inst (PRowCpy's A' row),
   HIMGSH drv3_imgsh_A, HFRSH drv3_pjf_visf_A; HREAL drv3_fuzz_realloc_A *)
Lemma drv3_put_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnWriter.tput_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TA (ARi rc) SKc C0.
Proof.
intros rc fx.
pose proof (YGcallcf.AR_laws_x_xs (cp := CP) (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (PAr rc)) TA
  (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TA)) as LAWSx.
eapply (S7a_put.put_holds (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) (RL := RLc) (SK := SKc)
  (PA := PAr rc) TA (ARi rc)).
all: first
  [ exact LAWSx | exact PALibA.palib_A | exact S7a_put_wit.s7p_ent_A | exact S7a_put_wit.s7p_obj_A
  | exact (drv3_fuzz_realloc_A rc fx) | exact (Cno102A_TopA.cn_memcpy_A_inst (rc := rc) fx)
  | exact (drv3_imgsh_A rc) | exact (drv3_pjf_visf_A rc) | exact S7a_put_wit.s7p_pst_A
  | exact S7a_put_wit.s7p_head_wide | exact S7a_put_wit.s7p_pstro_A | exact S7a_put_wit.s7p_zs_aligned_A
  | exact S7a_put_wit.s7p_pab_A | exact (conj (Z.le_refl _) (Z.le_refl _)) ].
Qed.

(* write_value_holds' INDENT: a Theorem Labs lane's S7a_indent.indent_holds (lib/A/Prog/S7a_indent.v:2100; S7a_indent.v,
   S7a_indent_wit.v taken BY PATH from a working branch a8d2be84a39d), its HPUT drv3_put_A, the
   image facts S7a_indent_wit.s7w_ent_A / s7w_hlit_A / s7w_pstro_A *)
Lemma drv3_indent_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnWriter.tindent_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TA (ARi rc) SKc C0.
Proof.
intros rc fx.
pose proof (YGcallcf.AR_laws_x_xs (cp := CP) (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (PAr rc)) TA
  (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TA)) as LAWSx.
exact (S7a_indent.indent_holds (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) (RL := RLc) (SK := SKc)
  (PA := PAr rc) TA (ARi rc) _ LAWSx PALibA.palib_A S7a_indent_wit.s7w_ent_A C0 (drv3_put_A rc fx)
  (S7a_indent_wit.s7w_hlit_A (ARi rc) _ LAWSx) S7a_indent_wit.s7w_pstro_A).
Qed.

(* write_value_holds' PUTSTR: a Theorem Labs lane's PRW_put_string.put_string_holds (lib/A/Prog/PRW_put_string.v:130;
   PRW_put_string.v, _a.v, _l.v, _t.v taken BY PATH from a working branch f75b9f6e6fa6, the rest of
   its closure already on this line from there) at ARx := iface_ARx, CTX0 := iface_ctx0: the image facts
   PRW_S7bWit.s7bw_* / PRW_S7bLitWit.s7bl_ps_hlit*, errno_low PALibA.palib_errno_A, the frame laws OWNLOW / SMX / ASFX /
   FFLX / SFX by YGcallcf / YGcallScf at iface_ARx (as lib/B/Prog/PutStringB_Wit.v cites them at B'), ASO
   AD2l.TfibB_ok, ASM0 drv3_asmr0_A, HIMGSH drv3_imgsh_A, HFHULL drv3_pjf_visf_A, PUT drv3_put_A, ASTRLEN drv3_strlen_A,
   AMCPY Cno102A_TopA.cn_memcpy_A_inst, gcan / can the canary cells of s7bw_ps_snp_img; SNP drv3_snprintf_A *)
Lemma drv3_put_string_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnWriter.tput_string_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TA (ARi rc) SKc C0.
Proof.
intros rc fx.
pose proof (YGcallcf.AR_laws_x_xs (cp := CP) (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (PAr rc)) TA
  (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TA)) as LAWSx.
eapply (PRW_put_string.put_string_holds (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) (SK := SKc) (RL := RLc)
  (PA := PAr rc) TA (ARi rc)).
all: first
  [ exact LAWSx | exact PALibA.palib_A | exact PRW_S7bWit.s7bw_ps_ent | exact PRW_S7bWit.s7bw_uar
  | exact PRW_S7bWit.s7bw_obj | exact PRW_S7bWit.s7bw_objs_disj | exact PRW_S7bWit.s7bw_uarc
  | exact (@YC4aP.pa_segs_low _ _ (PAr rc)) | exact PALibA.palib_errno_A
  | exact (YGcallcf.ARx_owned_low_law_xs (cp := CP) _ TA (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TA))
  | exact (YGcallScf.stack_malloc_x_any _ (ARi rc)) | exact (drv3_asmr0_A rc fx) | exact PRW_S7bWit.s7bw_sm0
  | exact S7a_put_wit.s7p_head_wide | exact AD2l.TfibB_ok | exact (drv3_imgsh_A rc) | exact (drv3_pjf_visf_A rc)
  | exact PRW_S7bWit.s7bw_hpab | exact PRW_S7bWit.s7bw_pst_ok_ps | exact PRW_S7bWit.s7bw_pstro_A
  | exact (fun fx0 => drv3_put_A rc fx0) | exact (PRW_S7bLitWit.s7bl_ps_hlit17 (ARi rc) _ LAWSx)
  | exact (PRW_S7bLitWit.s7bl_ps_hlit85 (ARi rc) _ LAWSx) | exact (PRW_S7bLitWit.s7bl_ps_hlit87 (ARi rc) _ LAWSx)
  | exact (PRW_S7bLitWit.s7bl_ps_hlit91 (ARi rc) _ LAWSx) | exact (PRW_S7bLitWit.s7bl_ps_hlit93 (ARi rc) _ LAWSx)
  | exact (PRW_S7bLitWit.s7bl_ps_hlit89 (ARi rc) _ LAWSx) | exact (fun fx0 => drv3_strlen_A rc fx0)
  | exact (Cno102A_TopA.cn_memcpy_A_inst (rc := rc)) | exact PRW_S7bWit.s7bw_ps_snp_img
  | exact (fun fx0 => drv3_snprintf_A rc fx0)
  | exact (YGcallScf.astack_free_x_xs (cp := CP) _ TA) | exact (YGcallScf.frame_flag_x_xs (cp := CP) _ TA)
  | exact (YGcallScf.stack_free_x_any _ (ARi rc)) ].
Qed.

(* pjw_holds_lc's HWV: a Theorem Labs lane's PRW_write_value.write_value_holds (lib/A/Prog/PRW_write_value.v:7468, on this line
   from a working branch f75b9f6e6fa6) at ARx := iface_ARx, CTX0 := iface_ctx0, every depth: the
   image facts PRW_S7bWit.s7bw_wv_ent / s7bw_wv_obj / s7bw_pstro_A, PRW_S7bLitWit.s7bl_wv_hlit, HJT drv3_wv_hjt_A, HW
   S7a_put_wit.s7p_head_wide, PUT drv3_put_A, PUTSTR drv3_put_string_A, INDENT drv3_indent_A, STRLEN drv3_strlen_A *)
Lemma drv3_write_value_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (n : nat),
  PRH_FnWriter.twrite_value_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TA (ARi rc) SKc C0 n.
Proof.
intros rc fx n.
pose proof (YGcallcf.AR_laws_x_xs (cp := CP) (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (PAr rc)) TA
  (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TA)) as LAWSx.
eapply (PRW_write_value.write_value_holds (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) (RL := RLc) (SK := SKc)
  (PA := PAr rc) TA (ARi rc)).
all: first
  [ exact LAWSx | exact PALibA.palib_A | exact PRW_S7bWit.s7bw_wv_ent | exact PRW_S7bWit.s7bw_wv_obj
  | exact drv3_wv_hjt_A | exact (PRW_S7bLitWit.s7bl_wv_hlit (ARi rc) _ LAWSx) | exact PRW_S7bWit.s7bw_pstro_A
  | exact (fun fx0 => drv3_put_A rc fx0) | exact (fun fx0 => drv3_put_string_A rc fx0)
  | exact (fun fx0 => drv3_indent_A rc fx0) | exact S7a_put_wit.s7p_head_wide
  | exact (fun fx0 => drv3_strlen_A rc fx0) ].
Qed.

(* pj_parse_holds_A's TPV (header): a Theorem Labs lane's VrdTop.vrd_parse_value_holds at CTX0 := iface_ctx0, depth 0 *)
Lemma drv3_parse_value_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CTX CW : list (list Z)),
  PRH_FnParse.tparse_value_specX (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) (PI := PIc) (RL := RLc)
    (L := Listing_prog.A_prog_listing) (PA := PAr rc) TA (ARi rc) SKc 0%nat CTX C0 CW.
Proof.
intros rc fx CTX CW.
exact (VrdTop.vrd_parse_value_holds (rc := rc) (SK := SKc) C0 CW
  (fun fy Hp k => drv3_arealloc_A rc fy Hp k)
  (fun fy => drv3_amalloc_A rc fy)
  (fun fy => drv3_afree_A rc fy)
  fx 0%nat CTX).
Qed.

(* H_txt_pj_parse_A (and parse_noting's HPJ, crs_holds_Ap's HT_pj_parse at every cursor set) *)
Lemma drv3_pj_parse_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (CW : list (list Z)),
  PRH_FnPj.tpj_parse_specX (fx := fx) (cp := CP) (PI := PIc) (RL := RLc) (PA := PAr rc) TA (ARi rc) SKc C0 CW.
Proof.
intros rc fx CW.
exact (PjParseA_top.pj_parse_holds_A (fx := fx) (rc := rc) (SK := SKc)
  (fun fy => drv3_afree_A rc fy)
  (fun fy => drv3_aunpoison_A rc fy) C0 CW (fun fy CTX => drv3_parse_value_A rc fy CTX CW)).
Qed.

(* H_txt_check_as_written_A *)
Lemma drv3_check_as_written_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_check_as_written_A fx rc.
Proof.
intros rc fx.
exact (Caw102A_Top.caw_A_top (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A) (PA := PAr rc) TA SKc C0
  (Caw102A_Img.caw_img_A TA AD2l.TfibB_syms) PALibA.palib_A
  (drv3_amalloc_A rc fx)
  (fun fz => drv3_afree_A rc fz)
  (fun fz => drv3_ex_value_A rc fz)
  (fun fz => PresetD2pAPf.txt_fuzz_alloc_ran_out_A_holds rc fz)).
Qed.

(* crs_holds_Ap's HT_pj_write *)
Lemma drv3_pj_write_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnWriter.tpj_write_specX (fx := fx) (rc := rc) (cp := CP) (PI := PIc) (PA := PAr rc) TA (ARi rc) SKc C0
    PRH_Base.DOC_D.
Proof.
intros rc fx.
pose proof (YGcallcf.AR_laws_x_xs (cp := CP) (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (PAr rc)) TA
  (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TA)) as LAWSx.
eapply (PRW_pj_write.pjw_holds_lc (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A) (cp := CP) (RL := RLc) (SK := SKc)
  (PA := PAr rc) TA (ARi rc)).
all: first
  [ exact LAWSx | exact (@YC4aP.pa_segs_low _ _ (PAr rc)) | exact PRW_S7bWit.s7bw_pjw_ent
  | exact (S6ImgWit.s6w_aim TA (ARi rc) _ LAWSx AD2l.TfibB_syms)
  | exact (fun n => drv3_write_value_A rc fx n) | exact (fun fx0 => drv3_put_A rc fx0)
  | exact (fun fx0 => drv3_fuzz_free_A rc fx0) | exact PRW_S7bWit.s7bw_pjw_ret | exact PRW_S7bWit.s7bw_pstro_A
  | exact PRW_S7bWit.s7bw_pst_ok_pjw | exact (PRW_S7bLitWit.s7bl_pjw_hlit (ARi rc) _ LAWSx)
  | exact PRW_S7bWit.s7bw_pjw_nl_img | exact (conj (Z.le_refl _) (Z.le_refl _))
  | exact (fun ly S Hp W mem md (H : ARi rc ly S Hp W mem md) => proj1 H)
  | drv3_argcnt ].
Qed.

(* H_txt_check_reject_clean_starved_A *)
Lemma drv3_check_reject_clean_starved_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_check_reject_clean_starved_A fx rc.
Proof.
intros rc fx.
exact (CrsTopAp.crs_holds_Ap (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A) (RL := RLc) (SK := SKc) C0
  (fun fy => Ent102DrvTopA2.drv2_check_reject_clean_A rc fy) (fun fy => drv3_fuzz_alloc_count_A rc fy)
  (fun fy => drv3_fuzz_alloc_fail_A rc fy) (fun fy => Ent102DrvTopA2.drv2_fuzz_alloc_live_A rc fy)
  (fun fy => PresetD2pAPf.txt_fuzz_alloc_ran_out_A_holds rc fy) (fun fy => drv3_fuzz_free_A rc fy)
  (fun fy => drv3_fuzz_free_null_A rc fy)
  (fun fy CW => drv3_pj_parse_A rc fy CW) (fun fy => drv3_pj_write_A rc fy) (drv3_asmr1_A rc fx)).
Qed.

(* H_txt_pj_free_A *)
Lemma drv3_pj_free_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState), PresetD2pAPf.txt_pj_free_A fx rc.
Proof.
intros rc fx.
exact (S6PjFreeTop.pj_free_holds (fx := fx) (rc := rc) (ci := CfImgA.CfImg_A) (RL := RLc) (PA := PAr rc) SKc TA (ARi rc)
  (YGcallcf.AR_laws_x_xs (cp := CP) _ TA (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TA)) PALibA.palib_A (drv3_pjf_visf_A rc)
  S6ImgWit.s6w_ent_pj_free S6ImgWit.s6w_obj S6ImgWit.s6w_pab S6ImgWit.s6w_pst_img S6ImgWit.s6w_pst_ro
  S6ImgWit.s6w_ret_free
  (S6ImgWit.s6w_aim TA (ARi rc) _ (YGcallcf.AR_laws_x_xs (cp := CP) _ TA (YG0lawscf.AR_laws_ok_cf (cp := CP) _ TA))
    AD2l.TfibB_syms)
  (drv3_fuzz_free_A rc fx) C0 PRH_Base.DOC_D).
Qed.

(* H_txt_check_no_overread_A *)
Lemma drv3_check_no_overread_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PresetD2pAPf.txt_check_no_overread_A fx rc.
Proof.
intros rc fx.
exact (Cno102A_TopA.check_no_overread_holds_A_inst (fx := fx) (rc := rc) (SK := SKc) C0
  (fun fz => drv3_amalloc_A rc fz)
  (fun fz => drv3_afree_A rc fz)
  (fun fz => PresetD2pAPf.txt_fuzz_alloc_ran_out_A_holds rc fz)
  (fun fz => Ent102DrvTopA2.drv2_parse_noting_A drv3_pj_parse_A rc fz) (fun fz => drv3_pj_free_A rc fz)).
Qed.

(* THE ONE COMPOSITION of this file's discharges: the driver's ROOM form (lib/A/PresetD2pAPf.v
   TFIB_T_room_all_A_closed) at the walk's values (sm := ReaderRes.jr_strtod; XM_LIB / XN_LIB := fun _ => 0, which
   occur in no statement here; PAYLOAD_ROOM := fun _ => True; a_mod_at / a_stamp := Ent102InstA.ia_mod_at / ia_stamp;
   the harness slot by the seam Ent102SeamA.preset_lib_x_stmt_A_holds), with the rows and callee texts above and
   walked2's citations (drv2_aintrin_cpy_A, drv2_aintrin_set_A, drv2_stack_malloc_cfm_A, and drv2_parse_noting_A at
   drv3_pj_parse_A). walked3 below and the halts top (lib/A/PresetClosedTopsA.v) both take it, so the list of
   discharges is written once. *)
Lemma TFIB_T_room_all_A_walked3 : PresetD2oA.TFIB_T_room_all_concl_A (fun _ => True).
Proof.
exact (PresetD2pAPf.TFIB_T_room_all_A_closed drv3_amalloc_A drv3_afree_A
  Ent102DrvTopA2.drv2_aintrin_cpy_A Ent102DrvTopA2.drv2_aintrin_set_A Ent102DrvTopA2.drv2_stack_malloc_cfm_A
  drv3_aread_check_A
  ReaderRes.jr_strtod (fun _ => 0) (fun _ => 0) (fun _ => True) Ent102InstA.ia_mod_at Ent102InstA.ia_stamp
  drv3_check_no_overread_A (Ent102DrvTopA2.drv2_parse_noting_A drv3_pj_parse_A) drv3_check_as_written_A
  drv3_check_reject_clean_starved_A drv3_check_round_trip_A drv3_pj_free_A
  (fun rc fx => Ent102SeamA.preset_lib_x_stmt_A_holds rc fx (fun _ => 0) (fun _ => 0) (fun _ => True))).
Qed.

(* walked3 from the room form: at PAYLOAD_ROOM := fun _ => True the payload's room is I, so TFIB_T's plain no-refusal
   premise is not used *)
Theorem TFIB_T_closed_A_walked3 : PresetD2pA.TFIB_T_closed_A.
Proof.
intros sp brk mbase rnd inp en_p Hsp Hbrk Hmb Hfit Hinp _.
exact (TFIB_T_room_all_A_walked3 sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp (fun _ _ _ _ _ => I)).
Qed.

(* inside the Section: the remaining hypotheses by name, and the allowed axioms *)
Print Assumptions TFIB_T_room_all_A_walked3.
Print Assumptions TFIB_T_closed_A_walked3.
End walked3.

Set Printing Implicit.
Check TFIB_T_closed_A_walked3.
Unset Printing Implicit.
