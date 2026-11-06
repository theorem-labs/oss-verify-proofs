(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr Agree SysStep.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_presp_B.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HApxF HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjA HCount HObjK HObjF H_freelist H_ListAddTail H_scanner_get_token H_vfm_A H_vfm_G H_vfm_X H_vfm_GX
     H_match_A H_match_X H_UpnpPrintf H_membuffer_delete H2KitA HPrepA H_hlist_view H_str_alloc H_map_str_to_int H_httpmsg_destroy H_presp_seg H_presp H_phdr_seg H_phdr
     H_pent_seg H_pent_seg2 H_pent_kit H_pent H_puri H_pparse_seg H_pparse_stmt H_pparse_reql.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Hypothesis STACK_MALLOC_0 : stack_malloc_stmt FI 0.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.
Hypothesis STACK_MALLOC_2 : stack_malloc_stmt FI 2.
Hypothesis STACK_MALLOC_3 : stack_malloc_stmt FI 3.
Hypothesis SET_SHADOW_F5 : set_shadow_f5_stmt.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation PS := (aps FI AI).
Local Notation hdr := (hdr FI AI).
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Section PJ.
  Variables (q lo P : Z) (st : fsstate FI).
  Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem) (canary : word).
  Hypothesis POK : H_pparse_seg.pq_okA FI q lo P st.
  Hypothesis RF0 : RFAKE FI st m0.
  Hypothesis FCO : fs_call_ok FI st (wz A0_TP) 5.
  Hypothesis FE0 : FSENV FI m0.
  Variable mws : list word.
  Hypothesis MWL : length mws = 22%nat.
  Hypothesis MID : forall i, 0 <= i < 11 -> exists id, nth_error mws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id <= 11.
  Notation F := (H_pparse_seg.qF FI st). Notation FL := (H_pparse_seg.qFL FI st). Notation SF := (H_pparse_seg.qSF FI st).

Local Notation pq_okA := (H_pparse_seg.pq_okA FI q lo P st).
Local Notation qF := (H_pparse_seg.qF FI st).

Local Notation pscrQ := (H_pparse_seg.pscrQ FI P st).
Local Notation prestQ := (H_pparse_seg.prestQ FI q st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation pinvQS := (H_pparse_seg.pinvQS FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation pregsQ := (H_pparse_seg.pregsQ FI q P st gp (wz A0_TP)).
Local Notation loopstQ := (H_pparse_seg.loopstQ FI q P st gp (wz A0_TP) F_ fc).
Local Notation exitstQ := (H_pparse_seg.exitstQ FI q P st gp (wz A0_TP) F_ fc).
Local Notation prologueQ := (H_pparse_seg.prologueQ FI STACK_MALLOC_1 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO FE0).
Local Notation ajcallstQ := (H_pparse_seg.ajcallstQ FI q P st gp (wz A0_TP) F_ fc).
Local Notation retstQ := (H_pparse_seg.retstQ FI q P st gp (wz A0_TP) F_ fc).
Local Notation reqlstQ := (H_pparse_seg.reqlstQ FI q P st gp (wz A0_TP) F_ fc).
Local Notation loopQ := (H_pparse_seg.loopQ FI q lo P st gp (wz A0_TP) F_ fc POK).
Local Notation retQ := (H_pparse_seg.retQ FI q P st gp (wz A0_TP) F_ fc).
Local Notation epostQ := (H_pparse_seg.epostQ FI q lo st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc).
Local Notation pWQ := (H_pparse_seg.pWQ FI q lo st).
Local Notation rframeQ := (H_pparse_seg.rframeQ FI q lo st).
Local Notation exitFQ := (H_pparse_seg.exitFQ FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation exitQ := (H_pparse_seg.exitQ FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation pinvQ_stepSh := (H_pparse_seg.pinvQ_stepSh FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation unpoisonQ := (H_pparse_seg.unpoisonQ FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation rejoinQ := (H_pparse_seg.rejoinQ FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation inP := (H_pparse_seg.inP P).
Local Notation dj_inP := (H_pparse_seg.dj_inP P).
Local Notation pinv_stepP := (H_pparse_seg.pinv_stepP FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation outX := (H_pparse_seg.outX FI).
Local Notation clsX := (H_pparse_seg.clsX FI).
Local Notation dj_inPX := (H_pparse_seg.dj_inPX FI P).
Local Notation pinv_stepX := (H_pparse_seg.pinv_stepX FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation epostQ_mono := (H_pparse_seg.epostQ_mono FI q lo st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc).
Local Notation xobj_rframe := (H_pparse_seg.xobj_rframe FI q lo P st m0 POK RF0).
Local Notation eframe_facts := (H_pparse_seg.eframe_facts FI q lo P st m0 POK RF0).
Local Notation elive := (H_pparse_seg.elive FI P st).
Local Notation elive_of := (H_pparse_seg.elive_of FI q lo P st m0 POK RF0).
Local Notation pinv_rf := (H_pparse_seg.pinv_rf FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation inFJ := (H_pparse_seg.inFJ FI st).
Local Notation inW3 := (H_pparse_seg.inW3 FI P st).
Local Notation dj_W3 := (H_pparse_seg.dj_W3 FI P st).
Local Notation app_W3 := (H_pparse_seg.app_W3 FI q lo P st m0 POK RF0).
Local Notation fsw_W3 := (H_pparse_seg.fsw_W3 FI q lo P st m0 POK RF0).
Local Notation out_W3 := (H_pparse_seg.out_W3 FI q lo P st m0 POK RF0).
Local Notation pinv_stepF := (H_pparse_seg.pinv_stepF FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation fj_split := (H_pparse_seg.fj_split FI st).
Local Notation fj_join := (H_pparse_seg.fj_join FI st).
Local Notation txt_okA := (H_pparse_seg.txt_okA FI).
Local Notation pctx := (H_pparse_seg.pctx q lo P canary).
Local Notation clow_stepW := (H_pparse_seg.clow_stepW canary).
Local Notation low_fsW := (H_pparse_seg.low_fsW FI q lo P st POK).
Local Notation pctx_stepF := (H_pparse_seg.pctx_stepF FI q lo P st m0 POK RF0 canary).
Local Notation pctx_stepP := (H_pparse_seg.pctx_stepP FI q lo P st m0 POK RF0 canary).
Local Notation dj_FJER := (H_pparse_seg.dj_FJER FI st).
Local Notation evf_ok := (H_pparse_seg.evf_ok FI q lo P st m0 POK RF0).

Local Notation rWS := (H_pparse_reql.rWS lo P).
Local Notation tok_shwQ := (H_pparse_reql.tok_shwQ FI q lo P st POK).
Local Notation pscrT := (H_pparse_reql.pscrT FI P st).
Local Notation pscr_split := (H_pparse_reql.pscr_split FI P st).
Local Notation pscr_join := (H_pparse_reql.pscr_join FI P st).
Local Notation pinv_stepT := (H_pparse_reql.pinv_stepT FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation pctx_stepT := (H_pparse_reql.pctx_stepT FI q lo P st m0 POK RF0 canary).
Local Notation rWS_sub := (H_pparse_reql.rWS_sub lo P).
Local Notation sgt_callQ := (H_pparse_reql.sgt_callQ FI IC q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 canary).
Local Notation rWT := (H_pparse_reql.rWT lo P).
Local Notation skipQ := (H_pparse_reql.skipQ FI IC q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 canary).
Local Notation qouts_shw := (H_pparse_reql.qouts_shw FI q lo P st m0 POK RF0).
Local Notation plocQ := (H_pparse_reql.plocQ FI st).
Local Notation ploc_split := (H_pparse_reql.ploc_split FI st).
Local Notation ploc_junk := (H_pparse_reql.ploc_junk FI st).
Local Notation ploc_cells := (H_pparse_reql.ploc_cells FI st).
Local Notation ploc_of_cells := (H_pparse_reql.ploc_of_cells FI st).
Local Notation rW09 := (H_pparse_reql.rW09 FI P st).
Local Notation rWRQ := (H_pparse_reql.rWRQ FI P st).
Local Notation rW09_ok := (H_pparse_reql.rW09_ok FI P st).
Local Notation rWRQ_ok := (H_pparse_reql.rWRQ_ok FI P st).
Local Notation rW09_fcls := (H_pparse_reql.rW09_fcls FI q lo P st m0 POK RF0).
Local Notation rWRQ_fcls := (H_pparse_reql.rWRQ_fcls FI q lo P st m0 POK RF0).
Local Notation rWT_fcls := (H_pparse_reql.rWT_fcls FI q lo P st m0 POK RF0).
Local Notation low_fsW3 := (H_pparse_reql.low_fsW3 FI q lo P st m0 POK RF0).
Local Notation m09Q := (H_pparse_reql.m09Q FI IC STACK_MALLOC_0 STACK_MALLOC_1 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary).
Local Notation mrqQ := (H_pparse_reql.mrqQ FI IC STACK_MALLOC_0 STACK_MALLOC_1 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary).
Local Notation pstatR := (H_pparse_reql.pstatR mws).
Local Notation pstatR_step := (H_pparse_reql.pstatR_step FI mws MWL).
Local Notation hiER_fsW3 := (H_pparse_reql.hiER_fsW3 FI q lo P st m0 POK RF0).
Local Notation pstatR_stepF := (H_pparse_reql.pstatR_stepF FI q lo P st m0 POK RF0 mws MWL).
Local Notation pstatR_stepP := (H_pparse_reql.pstatR_stepP FI q lo P st m0 POK RF0 mws MWL).
Local Notation u64arr_read4Q := (H_pparse_reql.u64arr_read4Q mws MWL).
Local Notation keepFP := (H_pparse_reql.keepFP FI P st).
Local Notation ploc_keep := (H_pparse_reql.ploc_keep FI P st mws MWL).
Local Notation bytes_skipnQ := (H_pparse_reql.bytes_skipnQ mws MWL).
Local Notation keepS := (H_pparse_reql.keepS q).
Local Notation keepS_of_munch := (H_pparse_reql.keepS_of_munch FI q lo P st m0 POK RF0).
Local Notation map_callQ := (H_pparse_reql.map_callQ FI IC STACK_MALLOC_0 q lo P st ra (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary mws MWL).
Local Notation ploc_stepP := (H_pparse_reql.ploc_stepP FI q lo P st m0 POK RF0).
Local Notation rWM := (H_pparse_reql.rWM P).
Local Notation rWM_inP := (H_pparse_reql.rWM_inP P mws MWL).
Local Notation map09Q := (H_pparse_reql.map09Q FI IC STACK_MALLOC_0 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary mws MWL MID).
Local Notation dj_inFJ := (H_pparse_reql.dj_inFJ FI st mws MWL).
Local Notation pinv_stepJ := (H_pparse_reql.pinv_stepJ FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0 mws MWL).
Local Notation pctx_stepJ := (H_pparse_reql.pctx_stepJ FI q lo P st m0 POK RF0 canary mws MWL).
Local Notation pstatR_stepJ := (H_pparse_reql.pstatR_stepJ FI q lo P st m0 POK RF0 mws MWL).
Local Notation rWU := (H_pparse_reql.rWU FI st).
Local Notation rWU_inFJ := (H_pparse_reql.rWU_inFJ FI st mws MWL).
Local Notation slash1Q := (H_pparse_reql.slash1Q FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 canary mws MWL).
Local Notation slash2Q := (H_pparse_reql.slash2Q FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 canary mws MWL).
Local Notation rWA := (H_pparse_reql.rWA FI P st).
Local Notation fk_ok_own := (H_pparse_reql.fk_ok_own FI st m0 RF0 mws MWL).
Local Notation fkeep_own := (H_pparse_reql.fkeep_own FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 RF0 mws MWL).
Local Notation rmove := (H_pparse_reql.rmove FI q lo P st).
Local Notation rmove_refl := (H_pparse_reql.rmove_refl FI q lo P st).
Local Notation rmove_trans := (H_pparse_reql.rmove_trans FI q lo P st).
Local Notation rmove_fk := (H_pparse_reql.rmove_fk FI q lo P st).
Local Notation rmove_T := (H_pparse_reql.rmove_T FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0 mws MWL).
Local Notation rmove_U := (H_pparse_reql.rmove_U FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0 mws MWL).
Local Notation pcell_T := (H_pparse_reql.pcell_T FI q lo P st POK).
Local Notation pcell_fk := (H_pparse_reql.pcell_fk FI q lo P st POK mws MWL).
Local Notation pcell_U := (H_pparse_reql.pcell_U FI q lo P st m0 POK RF0).
Local Notation pstatR_T := (H_pparse_reql.pstatR_T FI q lo P st m0 POK RF0 mws MWL).
Local Notation rW09_sub := (H_pparse_reql.rW09_sub FI P st).
Local Notation rWRQ_sub := (H_pparse_reql.rWRQ_sub FI P st).
Local Notation rWM_sub := (H_pparse_reql.rWM_sub FI P st).
Local Notation strcallstQ := (H_pparse_reql.strcallstQ FI q P st gp (wz A0_TP) F_ fc).
Local Notation segAQ := (H_pparse_reql.segAQ FI IC STACK_MALLOC_0 STACK_MALLOC_1 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary mws MWL MID).
Local Notation rWP := (H_pparse_reql.rWP P).
Local Notation rWP_ok := (H_pparse_reql.rWP_ok FI P st mws MWL).
Local Notation rWP_fcls := (H_pparse_reql.rWP_fcls FI q lo P st m0 POK RF0 mws MWL).
Local Notation pstatU_step := (H_pparse_reql.pstatU_step FI mws MWL).
Local Notation keepU := (H_pparse_reql.keepU FI P st).
Local Notation puri_callQ := (H_pparse_reql.puri_callQ FI IC STACK_MALLOC_3 SET_SHADOW_F5 q lo P st ra (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary mws MWL).
Local Notation wmove := (H_pparse_reql.wmove FI q lo st).
Local Notation wmove_refl := (H_pparse_reql.wmove_refl FI q lo st).
Local Notation wmove_trans := (H_pparse_reql.wmove_trans FI q lo st).
Local Notation wmove_fk := (H_pparse_reql.wmove_fk FI q lo st).
Local Notation wmove_P := (H_pparse_reql.wmove_P FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0 mws MWL).
Local Notation utext_stepP := (H_pparse_reql.utext_stepP FI q lo P st m0 POK RF0).
Local Notation rWB := (H_pparse_reql.rWB P).
Local Notation rWP_subB := (H_pparse_reql.rWP_subB P).
Local Notation segBQ := (H_pparse_reql.segBQ FI IC STACK_MALLOC_3 SET_SHADOW_F5 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary mws MWL).
Local Notation pscrC := (H_pparse_reql.pscrC FI P st).
Local Notation pscrC_split := (H_pparse_reql.pscrC_split FI P st).
Local Notation pscrC_join := (H_pparse_reql.pscrC_join FI P st).
Local Notation slk_apart := (H_pparse_reql.slk_apart FI q lo P st POK).
Local Notation pctx_stepTx := (H_pparse_reql.pctx_stepTx FI q lo P st m0 POK RF0 canary mws MWL).
Local Notation outX_text := (H_pparse_reql.outX_text FI mws MWL).
Local Notation inW2 := (H_pparse_reql.inW2 FI P st).
Local Notation dj_slk := (H_pparse_reql.dj_slk FI q lo P st m0 POK RF0).
Local Notation pslk_stepW := (H_pparse_reql.pslk_stepW FI q lo P st m0 POK RF0).
Local Notation pslk_stepF := (H_pparse_reql.pslk_stepF FI q lo P st m0 POK RF0).
Local Notation rWP_W2 := (H_pparse_reql.rWP_W2 FI P st mws MWL).
Local Notation inP_W2 := (H_pparse_reql.inP_W2 FI P st).
Local Notation keepC := (H_pparse_reql.keepC FI P st).
Local Notation rWC := (H_pparse_reql.rWC P).
Local Notation rWP_subC := (H_pparse_reql.rWP_subC P).
Local Notation urlCQ := (H_pparse_reql.urlCQ FI IC STACK_MALLOC_3 SET_SHADOW_F5 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary mws MWL).
Local Notation wmove_S := (H_pparse_reql.wmove_S FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0 mws MWL).
Local Notation sstore_T := (H_pparse_reql.sstore_T lo mws MWL).
Local Notation sstore_rWT := (H_pparse_reql.sstore_rWT lo P mws MWL).
Local Notation fcell_S := (H_pparse_reql.fcell_S FI q lo P st POK mws MWL).
Local Notation ploc_S := (H_pparse_reql.ploc_S FI q lo P st m0 POK RF0 mws MWL).
Local Notation pslk_S := (H_pparse_reql.pslk_S FI q lo P st POK).
Local Notation keepM := (H_pparse_reql.keepM FI P st).
Local Notation wmove_In := (H_pparse_reql.wmove_In FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 RF0 mws MWL).
Local Notation mapCQ := (H_pparse_reql.mapCQ FI IC STACK_MALLOC_0 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary mws MWL).
Local Notation inPE := (H_pparse_reql.inPE P).
Local Notation dj_inPE := (H_pparse_reql.dj_inPE P).
Local Notation pinv_stepE := (H_pparse_reql.pinv_stepE FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0 mws MWL).
Local Notation pctx_stepE := (H_pparse_reql.pctx_stepE FI q lo P st m0 POK RF0 canary mws MWL).
Local Notation wmove_E := (H_pparse_reql.wmove_E FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0 mws MWL).
Local Notation keepV := (H_pparse_reql.keepV FI P st).
Local Notation vpokeQ := (H_pparse_reql.vpokeQ FI IC q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 canary mws MWL).
Local Notation keepD := (H_pparse_reql.keepD FI P st).
Local Notation decQ := (H_pparse_reql.decQ FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 canary mws MWL MID).
Local Notation rWC_fsw := (H_pparse_reql.rWC_fsw FI q lo P st m0 POK RF0).
Local Notation shwlow_wmove := (H_pparse_reql.shwlow_wmove FI q lo P st m0 POK RF0 mws MWL).
Local Notation keepZ := (H_pparse_reql.keepZ FI P st).
Local Notation segCQ := (H_pparse_reql.segCQ FI IC STACK_MALLOC_0 STACK_MALLOC_3 SET_SHADOW_F5 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary mws MWL MID).
Local Notation skip0Q := (H_pparse_reql.skip0Q FI IC q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 mws MWL).

  #[using="m0 POK RF0 mws MWL"] Lemma pinv_stepA : forall shd, Z.of_nat (cells_size shd) = 16 -> forall (W : list ivl) (LBK : BL) q' m m2 stc,
    pinvQS shd q' m -> apx FI AI W LBK q' m m2 -> Forall inP W ->
    fs_live FI stc = fs_newff FI st 1 :: fs_live FI st -> RFAKE FI stc m2 ->
    stk asegs m2 lo q' -> mem_inv asegs m2 -> asan_env asegs m2 ->
    pinvQS shd q' m2.
  Proof.
    intros shd HSZ W LBK q' m m2 stc (ST & (j0 & j160 & j192 & QC) & MI & AE & (QB & QAL) & VR) AP HW LIVE1 RF2 ST2 MI2 AE2.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & _).
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    assert (PSH : P + 504 <= SF \/ SF + 16 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    assert (QLO : lo <= q' /\ alloc_ceiling <= q') by (clear - QB LO CLO; lia).
    assert (TRS : forall X cs, q' <= X -> rw_cells asegs m X cs -> rw_cells asegs m2 X cs).
    { intros X cs HX C. eapply (apx_rw_cells FI AI); [exact AP| exact C| apply aclient_range_above; exact HX| apply (dj_inP W _ _ HW); right; clear - HX QLO PHI; lia]. }
    assert (TRF : forall X cs, F <= X -> X + Z.of_nat (cells_size cs) <= F + 128 -> rw_cells asegs m X cs -> rw_cells asegs m2 X cs).
    { intros X cs H1 H2 C. eapply (apx_rw_cells FI AI); [exact AP| exact C| apply aclient_range_fs; clear - H1 H2 FLO FHI; lia| apply (dj_inP W _ _ HW); clear - H1 H2 PAF; lia]. }
    unfold H_pparse_seg.pinvQS, H_pparse_seg.prestQ.
    split; [exact ST2|].
    split; [exists j0, j160, j192; apply TRS; [clear; lia| exact QC]|].
    split; [exact MI2|]. split; [exact AE2|]. split; [exact (conj QB QAL)|].
    split; [exact Hq|].
    split. { eapply (stk_gagree (fun a => aclient FI AI LBK q' a /\ outside W a)); [intros a Ha [Hc Ho]; exact (AP a Ha Hc Ho)| exact GAP|].
             intros a Ha. split; [left; clear - Ha; lia|]. eapply disjoint_outside; [apply (dj_inP W a 1 HW); right; clear - Ha QLO PHI; lia| lia]. }
    split; [apply TRS; [clear - QB; lia| exact FRhi]|].
    split; [exists w0; apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FH]|].
    split; [exists jf; apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FT1]|].
    split; [apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FT2]|].
    split. { eapply (apx_rw_cells FI AI); [exact AP| exact SHF| apply aclient_range_fs_shadow; rewrite ?HSZ; clear - SHF1 SHF2; lia| apply (dj_inP W _ _ HW); rewrite HSZ; clear - PSH; lia]. }
    split. { eapply (apx_rw_cells FI AI); [exact AP| exact FLG| apply aclient_range_fs; simpl_sizes; clear - FLLO FLHI; lia| apply (dj_inP W _ _ HW); simpl_sizes; clear - PAFL; lia]. }
    exists stc. split; [exact RF2| exact LIVE1].
  Qed.

  #[using="AMS mws MWL"] Lemma stack_shadow_clientE : forall (LB : BL) q0 lo' a,
    sh alloc_ceiling - sh alloc_ceiling mod 8 <= lo' -> lo' <= a < 0x10007fff8000 -> aclient FI AI LB q0 a.
  Proof.
    intros LB q0 lo' a H1 H2. right; left. exists lo', 0x10007fff8000. split; [| lia].
    apply AMS. unfold a0_static. split; [lia|]. repeat right. pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)). lia.
  Qed.
  #[using="HC FI P st POK mws MWL"] Lemma sh_window_okE : SH_LO <= sh lo - sh lo mod 8 /\ sh lo - sh lo mod 8 <= sh lo /\ sh q <= SH_HI /\ sh q + 8 <= SH_HI.
  Proof.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & _). destruct (stack_window_lo FI lo CLO) as [S1 _]. pose proof (stack_lo_ok lo).
    pose proof (sh_hi_ok q ltac:(lia)). pose proof (sh_hi_ok8 q ltac:(lia)). repeat split; assumption.
  Qed.

  #[using="AMS q lo st m0 POK RF0 mws MWL"] Lemma imgsh_apxE : forall (W : list ivl) (LBK : BL) q' m m2 X n, apx FI AI W LBK q' m m2 -> Forall inP W ->
    shw m X n -> 0x10000 <= X -> X + n <= 0x609000 -> shw m2 X n.
  Proof.
    intros W LBK q' m m2 X n AP HW SW X1 X2. pose proof (shw_win_ok _ _ _ SW) as [Hn _].
    pose proof POK as POK'. destruct POK' as (_ & _ & _ & _ & PLO & _).
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2). pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & B5).
    eapply (shw_band_eq m m2 X n 0x7fffa000 0x800b9200 SW).
    - intros a Ha v Hv. refine (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(lia) _ _)) Hv).
      + right; left. exists 0x7fffa000, 0x800b9200. split; [| lia]. apply AMS. unfold a0_static. split; [lia|]. do 11 right. left. lia.
      + apply outside_of_forall. eapply Forall_impl; [| exact HW]. intros [x y] (H1 & H2 & H3). cbn [fst snd] in *. clear - H1 H2 H3 Ha PF1 PF2 B1 B2 B5. lia.
    - lia.
    - lia.
    - reflexivity.
    - reflexivity.
    - unfold sh, SHADOW_OFF. clear - X1. Z.div_mod_to_equations. lia.
    - intros _. unfold sh, SHADOW_OFF. clear - X2 Hn. Z.div_mod_to_equations. lia.
  Qed.
  #[using="AMS q lo st POK mws MWL"] Lemma imgcell_apxE : forall (W : list ivl) (LBK : BL) q' m m2 X cs, apx FI AI W LBK q' m m2 -> Forall inP W ->
    rw_cells asegs m X cs -> a0_static X (X + Z.of_nat (cells_size cs)) -> X + Z.of_nat (cells_size cs) <= 0x609000 -> rw_cells asegs m2 X cs.
  Proof.
    intros W LBK q' m m2 X cs AP HW C HS HX. pose proof POK as POK'. destruct POK' as (_ & _ & _ & _ & PLO & _).
    eapply (apx_rw_cells FI AI); [exact AP| exact C| eapply aclient_range_static; [apply AMS; exact HS| lia| lia]| apply (dj_inP W _ _ HW); left; clear - HX PLO; lia].
  Qed.

  Variables (LBK : BL) (gmax : Z) (ws : list word) (cslack : list byte) (ras : list Z) (GL : list (Z * Z)).
  Variables (s_0 : PS) (LB_0 : BL).
  Hypothesis HR0 : RHEAP_A FI AI s_0 LB_0 m0.
  Hypothesis KSUB0 : bsub FI AI LBK LB_0.
  Hypothesis QTOP : q + 64 <= am_stack_top FI AI.
  Hypothesis GMX : 0 < gmax < 2^31.
  Hypothesis WSL : length ws = 66%nat.
  Hypothesis HID : forall i, 0 <= i < 33 -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id < 64.
  Hypothesis ZSTAT : am_static FI AI ZERO_ADDR_A (ZERO_ADDR_A + 32).
  Hypothesis GLR : Forall (fun xn : Z * Z => 0x10000 <= fst xn /\ fst xn + snd xn <= 0x609000) GL.

  Notation pinvQ := (pinvQS qshadow).

  #[using="Type"] Lemma aj_cps : forall (Q : PS -> BL -> machine_state -> Prop) ms (s : PS) (LB : BL),
    evt asegs (fun ms' => AJ FI AI J Q ms' s LB) ms -> AJ FI AI J Q ms s LB.
  Proof. intros Q ms s LB H. eapply (aj_evt FI AI J); [exact H| intros ms' H'; exact H']. Qed.

  Definition estat (m : mem) : Prop :=
    shw m P 504 /\ shw m SEPTAB_A 20 /\ shw m FMT_CHUNK_A 7 /\ shw m FMT_CRLF_A 3
    /\ shz m (sh lo) (sh q) /\ shr m (sh lo - sh lo mod 8) (sh q + 8)
    /\ (exists ev, clow canary ev m) /\ shw m ERRNO_A 4 /\ pstatE gmax m.
  Definition estat2 (m : mem) : Prop := H_phdr.phdr_statics ws m cslack /\ gstA GL m.
  Ltac stat_band := unfold a0_static; split; [cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; env_band.

  Definition wpok (iv : ivl) : Prop := inP iv \/ H_pparse_seg.inER iv.
  Definition ekeep (WP : list ivl) (OB : BL) (m m' : mem) : Prop :=
    (forall a cs, (P <= a /\ a + Z.of_nat (cells_size cs) <= P + 504) \/ (a0_static a (a + Z.of_nat (cells_size cs)) /\ a + Z.of_nat (cells_size cs) <= 0x609000) ->
        disjoint_from WP a (Z.of_nat (cells_size cs)) -> rw_cells asegs m a cs -> rw_cells asegs m' a cs)
    /\ (forall a bs, a0_static a (a + Z.of_nat (length bs)) -> a + Z.of_nat (length bs) <= 0x5e68c8 -> bytes_at asegs m a bs -> bytes_at asegs m' a bs)
    /\ (forall a n, a0_static a (a + n) -> a + n <= 0x5e68c8 -> wr_at asegs m a n -> wr_at asegs m' a n)
    /\ bkeep FI AI OB m m'
    /\ (forall X n, 0x10000 <= X -> X + n <= 0x609000 -> shw m X n -> shw m' X n)
    /\ apxF FI AI (pparse_WA P) LBK q st m m'
    /\ (forall rs a, fpchain m (am_stack_top FI AI) q a rs -> fpchain m' (am_stack_top FI AI) q a rs)
    /\ (shw m P 504 -> shw m' P 504)
    /\ (shz m (sh lo) (sh q) -> shz m' (sh lo) (sh q)) /\ (shr m (sh lo - sh lo mod 8) (sh q + 8) -> shr m' (sh lo - sh lo mod 8) (sh q + 8)).

  #[using="mws MWL ws WSL"] Lemma shw_munch_gen : forall (W : list ivl) m m' X n, shw m X n -> munch W m m' ->
    (forall a, sh X - sh X mod 8 <= a < sh (X + n - 1) - sh (X + n - 1) mod 8 + 8 -> outside W a) -> shw m' X n.
  Proof.
    intros W m m' X n (ACC & RD & WK) MU OUT. split; [| split; [| exact WK]].
    - intros a Ha. destruct (ACC a Ha) as (k & (B0 & B1 & BB) & Hk). exists k. split; [| exact Hk].
      split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (BB i Hi).
      cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. rewrite Z.add_0_r.
      pose proof (win_ok_sh_band X n a WK Ha) as SB.
      apply (mrd_munch W m m' (sh a) MU); [| exact (shband_range _ SB)].
      apply OUT. unfold sh, SHADOW_OFF. clear - Ha. Z.div_mod_to_equations. lia.
    - intros Hn a Ha. destruct (RD Hn a Ha) as (v & Hv). exists v. rewrite <- Hv.
      pose proof (win_ok_words_band X n a WK Hn Ha) as SB.
      apply (mrd_munch W m m' a MU); [| exact (shband_range _ SB)]. exact (OUT a Ha).
  Qed.

  #[using="HC FI q lo st POK mws MWL ws WSL"] Lemma dj_wpok_low2 : forall (WP : list ivl) X n, Forall wpok WP -> X + n <= 0x5e68c8 \/ (0x5e68d0 <= X /\ X + n <= 0x609000) -> disjoint_from WP X n.
  Proof.
    intros WP X n HW HX. pose proof POK as POK'. destruct POK' as (_ & _ & _ & _ & PLO & _).
    induction HW as [|[x y] W [(H1 & H2 & H3)|(H1 & H2 & H3)] _ IH]; cbn [disjoint_from fst snd] in *; [exact I| |]; (split; [lia| exact IH]).
  Qed.
  #[using="HC FI q lo st POK mws MWL ws WSL"] Lemma dj_wpok_low : forall (WP : list ivl) X n, Forall wpok WP -> X + n <= 0x5e68c8 -> disjoint_from WP X n.
  Proof.
    intros WP X n HW HX. pose proof POK as POK'. destruct POK' as (_ & _ & _ & _ & PLO & _).
    induction HW as [|[x y] W [(H1 & H2 & H3)|(H1 & H2 & H3)] _ IH]; cbn [disjoint_from fst snd] in *; [exact I| |]; (split; [lia| exact IH]).
  Qed.

  #[using="Type"] Lemma ek_pcell : forall WP OB m m' a cs, ekeep WP OB m m' -> P <= a -> a + Z.of_nat (cells_size cs) <= P + 504 ->
    disjoint_from WP a (Z.of_nat (cells_size cs)) -> rw_cells asegs m a cs -> rw_cells asegs m' a cs.
  Proof. intros WP OB m m' a cs (K1 & _) H1 H2 DJ C. apply (K1 a cs); [left; split; assumption| exact DJ| exact C]. Qed.
  #[using="POK mws MWL ws WSL"] Lemma ek_scell : forall WP OB m m' a cs, ekeep WP OB m m' -> Forall wpok WP -> a0_static a (a + Z.of_nat (cells_size cs)) ->
    a + Z.of_nat (cells_size cs) <= 0x5e68c8 -> rw_cells asegs m a cs -> rw_cells asegs m' a cs.
  Proof. intros WP OB m m' a cs (K1 & _) HW H1 H2 C. apply (K1 a cs); [right; split; [exact H1| lia]| apply (dj_wpok_low WP _ _ HW H2)| exact C]. Qed.

  #[using="mws MWL ws WSL"] Lemma ek_hlist : forall WP OB m m' ns hs X, ekeep WP OB m m' -> p_hlist FI AI m P ns hs X -> bsub FI AI (hl_blocks FI AI ns hs) OB ->
    disjoint_from WP (P + 288) 96 -> p_hlist FI AI m' P ns hs X.
  Proof.
    intros WP OB m m' ns hs X EK (LHC & FLC & FFC & DL & HM & IT & VB & ZL & X0) SUB DJ.
    pose proof EK as (_ & _ & _ & BK & _).
    assert (PK : forall a cs, P + 288 <= a -> a + Z.of_nat (cells_size cs) <= P + 384 -> rw_cells asegs m a cs -> rw_cells asegs m' a cs).
    { intros a cs H1 H2 C. apply (ek_pcell WP OB m m' a cs EK); [lia| lia| | exact C]. eapply disjoint_from_sub; [exact DJ| lia| lia]. }
    unfold p_hlist.
    split; [apply PK; [lia| unfold lhead_cells; simpl_sizes; lia| exact LHC]|].
    split; [apply PK; [lia| unfold fl_cells; simpl_sizes; lia| exact FLC]|].
    split; [apply PK; [lia| simpl_sizes; lia| exact FFC]|].
    split. { eapply (dlseg_bkeep FI AI); [exact DL| exact BK|]. intros b it Hb. apply SUB. unfold hl_blocks. apply in_or_app. left. exact (in_map fst _ _ Hb). }
    split. { eapply (hdrs_mem_bkeep FI AI); [exact HM| exact BK|]. intros b Hb. apply SUB. unfold hl_blocks. apply in_or_app. right. exact Hb. }
    repeat (split; [assumption|]). exact X0.
  Qed.

  #[using="POK mws MWL ws WSL"] Lemma ek_pstat : forall WP OB m m', ekeep WP OB m m' -> Forall wpok WP -> pstatE gmax m -> pstatE gmax m'.
  Proof.
    intros WP OB m m' EK HW (G1 & G2 & G3 & G4). pose proof EK as (_ & _ & _ & _ & SK & _). unfold H_pent_seg.pstatE.
    split; [apply (ek_scell WP OB m m' _ _ EK HW); [stat_band| simpl_sizes; lia| exact G1]|].
    split; [apply (ek_scell WP OB m m' _ _ EK HW); [stat_band| simpl_sizes; lia| exact G2]|].
    split; [apply SK; [lia| lia| exact G3]|].
    apply (ek_scell WP OB m m' _ _ EK HW); [stat_band| simpl_sizes; lia| exact G4].
  Qed.

  #[using="POK mws MWL ws WSL"] Lemma ek_clow : forall WP OB m m', ekeep WP OB m m' -> Forall wpok WP -> disjoint_from WP ERRNO_A 4 ->
    (exists ev, clow canary ev m) -> exists ev, clow canary ev m'.
  Proof.
    intros WP OB m m' EK HW DJ (ev & CL1 & CL2 & CL3). pose proof EK as (K1 & _). exists ev. unfold clow, A0_got_ssp, A0_ssp_guard in *.
    split; [apply (K1 _ _); [right; split; [stat_band| simpl_sizes; lia]| simpl_sizes; exact DJ| exact CL1]|].
    split; [apply (ek_scell WP OB m m' _ _ EK HW); [stat_band| simpl_sizes; lia| exact CL2]|].
    apply (K1 _ _); [right; split; [stat_band| simpl_sizes; lia]| apply (dj_wpok_low2 WP _ _ HW); simpl_sizes; lia| exact CL3].
  Qed.
  #[using="POK mws MWL ws WSL"] Lemma ek_stat : forall WP OB m m', ekeep WP OB m m' -> Forall wpok WP -> estat m -> (exists ev, clow canary ev m') -> estat m'.
  Proof.
    intros WP OB m m' EK HW (SHP & SHSEP & SHF1 & SHF2 & SHZ & SHR & _ & SHE & PST) CL.
    pose proof EK as (_ & _ & _ & _ & SK & _ & _ & K7 & K8 & K9). unfold estat.
    split; [exact (K7 SHP)|]. split; [apply SK; [unfold SEPTAB_A; lia| unfold SEPTAB_A; lia| exact SHSEP]|].
    split; [apply SK; [lia| lia| exact SHF1]|]. split; [apply SK; [lia| lia| exact SHF2]|].
    split; [exact (K8 SHZ)|]. split; [exact (K9 SHR)|]. split; [exact CL|].
    split; [apply SK; [lia| lia| exact SHE]|]. exact (ek_pstat WP OB m m' EK HW PST).
  Qed.

  #[using="mws MWL WSL GLR"] Lemma ek_stat2 : forall WP OB m m', ekeep WP OB m m' -> estat2 m -> estat2 m'.
  Proof.
    intros WP OB m m' (_ & BK & WK & _ & SK & _) ((HS & SHSEP & SHFMT & COMMAB & CSL & SHC & ZB & SHZ0) & GS).
    split.
    - unfold H_phdr.phdr_statics.
      split.
      { destruct HS as ((TB1 & TB2) & SHT & TS). split; [split|split].
        - apply BK; [unfold a0_static; rewrite u64s_length, WSL; split; [lia|]; right; left; lia| rewrite u64s_length, WSL; lia| exact TB1].
        - apply WK; [unfold a0_static; rewrite WSL; split; [lia|]; right; left; lia| rewrite WSL; lia| exact TB2].
        - apply SK; [lia| lia| exact SHT].
        - intros i Hi. destruct (TS i Hi) as (Sx & str & slack & E1 & E2 & E3 & E4 & E5 & E6 & E7).
          exists Sx, str, slack. repeat (split; [assumption|]). apply SK; [lia| lia| exact E7]. }
      split; [apply SK; [unfold SEPTAB_A; lia| unfold SEPTAB_A; lia| exact SHSEP]|].
      split; [apply SK; [lia| lia| exact SHFMT]|].
      split; [exact COMMAB|]. split; [exact CSL|].
      split; [apply SK; [lia| lia| exact SHC]|].
      split; [apply BK; [unfold a0_static; cbn [length Z.of_nat Pos.of_succ_nat]; split; [lia|]; env_band| cbn [length Z.of_nat Pos.of_succ_nat]; lia| exact ZB]|].
      apply SK; [lia| lia| exact SHZ0].
    - unfold gstA in *. rewrite Forall_forall in *. intros xn Hx. pose proof (GLR xn Hx) as [G1 G2]. apply SK; [exact G1| exact G2| exact (GS xn Hx)].
  Qed.

  Definition ecls (WP : list ivl) (TB : BL) (iv : ivl) : Prop :=
    fst iv < snd iv /\
    ( (alloc_ceiling <= fst iv /\ snd iv <= q)
      \/ (F <= fst iv /\ snd iv <= F + 128) \/ (SF <= fst iv /\ snd iv <= SF + 16) \/ (FL <= fst iv /\ snd iv <= FL + 1)
      \/ inside WP (fst iv) (snd iv - fst iv)
      \/ (exists b, In b TB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) ).

  #[using="mws MWL ws WSL"] Lemma inside_wpok : forall (WP : list ivl) x n, Forall wpok WP -> inside WP x n -> 0 <= n ->
    (P <= x /\ x + n <= P + 504) \/ (0x5e68c8 <= x /\ x + n <= 0x5e68d0).
  Proof.
    intros WP x n HW. induction HW as [|[a b] W [(H1 & H2 & H3)|(H1 & H2 & H3)] _ IH]; cbn [inside fst snd] in *; intros HI Hn; [destruct HI| |];
      (destruct HI as [HI|HI]; [| exact (IH HI Hn)]); [left| right]; lia.
  Qed.
  #[using="mws MWL ws WSL"] Lemma inside_dj : forall (WP : list ivl) x n a k, inside WP x n -> disjoint_from WP a k -> 0 <= n -> a + k <= x \/ x + n <= a \/ n = 0.
  Proof.
    induction WP as [|[lo' hi'] W IH]; intros x n a k HI HD Hn; cbn [inside disjoint_from] in *; [destruct HI|].
    destruct HD as [D1 D2]. destruct HI as [HI|HI]; [lia| exact (IH x n a k HI D2 Hn)].
  Qed.
  #[using="Type"] Lemma inside_sub : forall (WP W' : list ivl) x n, inside WP x n -> Forall (fun iv : ivl => inside W' (fst iv) (snd iv - fst iv)) WP -> inside W' x n.
  Proof.
    induction WP as [|[lo' hi'] W IH]; intros W' x n HI HF; cbn [inside] in HI; [destruct HI|].
    inversion HF as [|? ? H1 H2]; subst. cbn [fst snd] in H1. destruct HI as [HI|HI]; [| exact (IH W' x n HI H2)].
    clear - H1 HI. induction W' as [|[a b] W' IH']; cbn [inside] in *; [destruct H1|]. destruct H1 as [H1|H1]; [left; lia| right; exact (IH' H1)].
  Qed.
  #[using="Type"] Lemma dj_forall : forall (W : list ivl) a n, Forall (fun iv : ivl => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
  Proof. induction W as [|[x y] W IH]; intros a n HF; cbn [disjoint_from]; [exact I|]. inversion HF as [|? ? H1 H2]; subst. split; [exact H1| exact (IH a n H2)]. Qed.

  #[using="ASL AMS m0 POK RF0 mws MWL ws s_0 LB_0 HR0 KSUB0 WSL"] Lemma ekeep_munch : forall (W WP : list ivl) (TB OB : BL) (s : PS) (LB : BL) m m',
    munch W m m' -> wmono asegs m m' -> Forall (ecls WP TB) W -> Forall wpok WP ->
    Forall (fun iv : ivl => inside (pparse_WA P) (fst iv) (snd iv - fst iv)) WP ->
    RHEAP_A FI AI s LB m -> bsub FI AI TB LB -> bsub FI AI OB LB -> bsub FI AI LBK LB -> idj TB OB -> idj TB LBK ->
    ekeep WP OB m m' /\ RHEAP_A FI AI s LB m'.
  Proof.
    intros W WP TB OB s LB m m' MU WM HCL HWP HWI HR TSUB OSUB KSUB TO TK.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    assert (PSH : P + 504 <= SF \/ SF + 16 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    assert (SHB : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000 /\ sh (FSB FI) + A0_FS_SHSIZE <= lo).
    { unfold sh, SHADOW_OFF in *. clear - B1 B2 B4 ACR CLO. repeat split; Z.div_mod_to_equations; lia. }
    destruct SHB as (SB1 & SB2 & SB3).
    assert (A0S : A0_FS_FRAMES = 36864) by reflexivity.
    assert (BLK : forall b, In b LB -> 0 <= blk_size b /\ blk_addr b + blk_size b + 16 <= alloc_ceiling /\ 0x609000 <= blk_addr b
                    /\ (blk_addr b + blk_size b + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= blk_addr b)
                    /\ (blk_addr b + blk_size b <= FSB FI \/ FSB FI + A0_FS_SIZE <= blk_addr b)).
    { intros b Hb. destruct (am_block_range FI AI s LB m b HR Hb) as (_ & _ & R3 & R4 & R5 & R6 & R7). auto. }

    assert (DJ1 : forall a n, ((P <= a /\ a + n <= P + 504) \/ (a + n <= 0x609000 /\ 0 <= n)) -> disjoint_from WP a n -> 0 <= n -> disjoint_from W a n).
    { intros a n HA HD Hn. apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b & Hb & CL)]]]]]; try lia.
      - destruct (inside_dj WP x (y - x) a n CL HD ltac:(lia)) as [D|[D|D]]; lia.
      - destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    assert (DJ2 : forall b, In b OB -> disjoint_from W (blk_addr b) (blk_size b)).
    { intros b Hb. apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct (BLK b (OSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5).
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b' & Hb' & CL)]]]]]; try lia.
      - destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      - assert (NE : b' <> b) by (apply (idj_neq TB OB b' b TO Hb' Hb)).
        destruct (am_blocks_disjoint FI AI s LB m b' b HR (TSUB b' Hb') (OSUB b Hb) NE); lia. }
    assert (FSW : Forall (fsw_iv FI) W).
    { eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *. unfold fsw_iv, app_iv, SH_HI. cbn [fst snd].
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b & Hb & CL)]]]]]; try lia.
      - destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      - destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    assert (SK : forall X n, X + n <= 0x609000 -> shw m X n -> shw m' X n).
    { intros X n HX SW. apply (shw_frame_fs FI W m m' X n SW MU FSW). left. lia. }
    split; [unfold ekeep; split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]|].
    - intros a cs HA HD C. eapply rw_cells_transport; [exact C| exact MU| exact WM|]. apply DJ1; [| exact HD| lia].
      destruct HA as [HA|[_ HA]]; [left; exact HA| right; split; [exact HA| lia]].
    - intros a bs HS HX B. eapply bytes_at_transport; [exact B| exact MU|]. apply DJ1; [right; lia| apply (dj_wpok_low WP _ _ HWP HX)| lia].
    - intros a n HS HX Wr. destruct (Z_le_gt_dec 0 n) as [Hn|Hn].
      + eapply wr_at_transport; [exact Wr| exact WM].
      + eapply wr_at_transport; [exact Wr| exact WM].
    - exact (bkeep_of_munch FI AI OB W m m' MU WM DJ2).
    - intros X n _ HX SW. exact (SK X n HX SW).
    - apply (apxF_of_munch FI AI ASL s_0 LB_0 LBK m0 m0 q st (pparse_WA P) W m m' HR0 KSUB0 RF0 MU WM).
      eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b & Hb & CL)]]]]].
      + left. exact CL.
      + right; left. intros a Ha. apply (new_frame_not_fclient FI AI ASL s_0 LB_0 LBK m0 q st 1 m0 F SF FL HR0 KSUB0 ltac:(lia) RF0 ltac:(lia) eq_refl eq_refl eq_refl). left. cbn [FB_of]. lia.
      + right; left. intros a Ha. apply (new_frame_not_fclient FI AI ASL s_0 LB_0 LBK m0 q st 1 m0 F SF FL HR0 KSUB0 ltac:(lia) RF0 ltac:(lia) eq_refl eq_refl eq_refl). right; left. cbn [SB_of]. lia.
      + right; left. intros a Ha. apply (new_frame_not_fclient FI AI ASL s_0 LB_0 LBK m0 q st 1 m0 F SF FL HR0 KSUB0 ltac:(lia) RF0 ltac:(lia) eq_refl eq_refl eq_refl). right; right. lia.
      + right; right. exact (inside_sub WP (pparse_WA P) x (y - x) CL HWI).
      + right; left. intros a Ha Hc. apply (fresh_block_not_aclient FI AI ASL s LB LBK b q m a HR (TSUB b Hb)); [| lia| lia|].
        * intros b0 Hb0. split; [exact (KSUB b0 Hb0)|]. intros ->. exact (idj_neq TB LBK b b TK Hb Hb0 eq_refl).
        * exact (fclient_aclient FI AI LBK q st m0 a RF0 Hc).
    - intros rs a CH. apply (fpchain_frame rs m m' _ q a W CH MU WM). eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b & Hb & CL)]]]]]; try lia.
      + destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      + destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia.
    - intros SHP. apply (shw_munch_gen W m m' P 504 SHP MU). intros a Ha.
      assert (HB : 0x7fff8000 <= a < 0x10007fff8000 /\ (a < SF \/ SF + 16 <= a)).
      { unfold sh, SHADOW_OFF in *. clear - Ha PLO PHI ACR PAF FAL SFB PAL. Z.div_mod_to_equations. lia. }
      apply disjoint_outside with (a := a) (n := 1); [| lia]. apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b & Hb & CL)]]]]]; try lia.
      + destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      + destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia.
    - intros SHZ. exact (shz_stack_fs FI W m m' lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - QHI; lia)) MU FSW).
    - intros SHR. exact (shr_stack_fs FI W m m' lo _ _ SHR CLO ltac:(lia) (sh_hi_ok8 q ltac:(clear - QHI; lia)) MU FSW).
    - apply (am_heap_frame FI AI s LB m m' W HR MU WM). eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[CL|[CL|[CL|[CL|(b & Hb & CL)]]]]].
      + left. lia.
      + do 3 right; left. lia.
      + do 4 right. lia.
      + do 3 right; left. lia.
      + destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; [do 3 right; left; lia|].
        right; left. exists 0x5e68c8, 0x5e68d0. split; [| unfold a0_wsafe; lia]. apply AMS. unfold a0_static. split; [lia|]. env_band.
      + right; right; left. exists b. split; [exact (TSUB b Hb)| lia].
  Qed.

  #[using="Type"] Lemma apxF_weaken2 : forall W W' (LB LB' : BL) q0 q1 (st0 st1 : fsstate FI) m m',
    apxF FI AI W LB' q1 st1 m m' -> q1 <= q0 -> (forall b, In b LB -> In b LB') -> (forall g, In g (fs_live FI st0) -> In g (fs_live FI st1)) ->
    (forall a, fclient FI AI LB q0 st0 a -> outside W' a -> outside W a) -> apxF FI AI W' LB q0 st0 m m'.
  Proof.
    intros W W' LB LB' q0 q1 st0 st1 m m' H HQ HL HF HO a Ha Hc Ho. apply H; [exact Ha| | exact (HO a Hc Ho)].
    eapply (fclient_weaken FI AI LB' LB q1 q0 st1 st0 a); eauto.
  Qed.
  #[using="ASL lo P m0 POK RF0 mws MWL ws WSL"] Lemma blk_not_fclient : forall (s : PS) (LB : BL) m (b : BLK) a, RHEAP_A FI AI s LB m -> In b LB -> bsub FI AI LBK LB -> idj [b] LBK ->
    blk_addr b <= a < blk_addr b + blk_size b -> ~ fclient FI AI LBK q st a.
  Proof.
    intros s LB m b a HR Hb KSUB TK Ha Hc. pose proof POK as POK'. destruct POK' as (CLO & LO & _).
    apply (fresh_block_not_aclient FI AI ASL s LB LBK b q m a HR Hb); [| lia| exact Ha| exact (fclient_aclient FI AI LBK q st m0 a RF0 Hc)].
    intros b0 Hb0. split; [exact (KSUB b0 Hb0)|]. intros ->. exact (idj_neq [b] LBK b b TK (or_introl eq_refl) Hb0 eq_refl).
  Qed.

  Definition fcls (WP : list ivl) (VB : BL) (iv : ivl) : Prop :=
    fst iv < snd iv /\
    ( inside WP (fst iv) (snd iv - fst iv) \/ inFJ iv
      \/ (exists b, In b VB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) ).

  #[using="ASL AMS m0 POK RF0 mws MWL ws s_0 LB_0 HR0 KSUB0 WSL"] Lemma ekeep_fk : forall (W WP : list ivl) (VB OB : BL) (s : PS) (LB : BL) qx (stx : fsstate FI) m m',
    munch ((lo, qx) :: FSIV W) m m' -> wmono asegs m m' -> fkeep FI W stx m m' -> lo <= qx <= q ->
    (forall g, In g (fs_live FI st) -> In g (fs_live FI stx)) -> (shw m P 504 -> shw m' P 504) ->
    Forall (fcls WP VB) W -> Forall wpok WP -> Forall (fun iv : ivl => inside (pparse_WA P) (fst iv) (snd iv - fst iv)) WP ->
    RHEAP_A FI AI s LB m -> bsub FI AI VB LB -> bsub FI AI OB LB -> bsub FI AI LBK LB -> idj VB OB -> idj VB LBK ->
    ekeep WP OB m m' /\ RHEAP_A FI AI s LB m'.
  Proof.
    intros W WP VB OB s LB qx stx m m' MU WM FK QX LSUB SHPK HCL HWP HWI HR VSUB OSUB KSUB VO VK.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    assert (SHB : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000 /\ sh (FSB FI) + A0_FS_SHSIZE <= lo).
    { unfold sh, SHADOW_OFF in *. clear - B1 B2 B4 ACR CLO. repeat split; Z.div_mod_to_equations; lia. }
    destruct SHB as (SB1 & SB2 & SB3).
    assert (A0S : A0_FS_FRAMES = 36864) by reflexivity.
    assert (BLK : forall b, In b LB -> 0 <= blk_size b /\ blk_addr b + blk_size b + 16 <= alloc_ceiling /\ 0x609000 <= blk_addr b
                    /\ (blk_addr b + blk_size b + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= blk_addr b)
                    /\ (blk_addr b + blk_size b <= FSB FI \/ FSB FI + A0_FS_SIZE <= blk_addr b)).
    { intros b Hb. destruct (am_block_range FI AI s LB m b HR Hb) as (_ & _ & R3 & R4 & R5 & R6 & R7). auto. }

    assert (DJP : forall a n, P <= a -> a + n <= P + 504 -> disjoint_from WP a n -> 0 <= n -> disjoint_from W a n).
    { intros a n H1 H2 HD Hn. apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[(CL1 & CL2 & CL3)|(b & Hb & CL)]]; cbn [fst snd] in *.
      - destruct (inside_dj WP x (y - x) a n CL HD ltac:(lia)) as [D|[D|D]]; lia.
      - lia.
      - destruct (BLK b (VSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    assert (DJS : forall a n, a + n <= 0x609000 -> disjoint_from WP a n -> 0 <= n -> disjoint_from ((lo, qx) :: FSIV W) a n).
    { intros a n H1 HD Hn. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|].
      apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[(CL1 & CL2 & CL3)|(b & Hb & CL)]]; cbn [fst snd] in *.
      - destruct (inside_dj WP x (y - x) a n CL HD ltac:(lia)) as [D|[D|D]]; lia.
      - lia.
      - destruct (BLK b (VSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    assert (DJ2 : forall b, In b OB -> disjoint_from ((lo, qx) :: FSIV W) (blk_addr b) (blk_size b)).
    { intros b Hb. destruct (BLK b (OSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|].
      apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[(CL1 & CL2 & CL3)|(b' & Hb' & CL)]]; cbn [fst snd] in *.
      - destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      - lia.
      - assert (NE : b' <> b) by (apply (idj_neq VB OB b' b VO Hb' Hb)).
        destruct (am_blocks_disjoint FI AI s LB m b' b HR (VSUB b' Hb') (OSUB b Hb) NE); lia. }
    assert (APW : app_ivs W).
    { eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *. unfold app_iv, SH_HI. cbn [fst snd].
      destruct CL as [CL|[(CL1 & CL2 & CL3)|(b & Hb & CL)]]; cbn [fst snd] in *.
      - destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      - lia.
      - destruct (BLK b (VSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    assert (FSW : Forall (fsw_iv FI) ((lo, qx) :: FSIV W)) by (apply fsw_cons_app; [apply app_iv_stack; exact CLO| apply fsw_FSIV; exact APW]).
    assert (SK : forall X n, X + n <= 0x609000 -> shw m X n -> shw m' X n).
    { intros X n HX SW. apply (shw_frame_fs FI _ m m' X n SW MU FSW). left. lia. }
    assert (LVP : lb (fs_live FI stx) P 504) by (exact (lb_mono _ _ _ _ PLB LSUB)).
    split; [unfold H_pent_kit.ekeep; split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]|].
    - intros a cs HA HD C. destruct HA as [[H1 H2]|[_ HA]].
      + apply (rw_cells_fkeep FI W stx m m' a cs C FK WM); [left; apply (Contracts.lb_sub _ _ _ _ _ LVP); lia| apply DJP; [exact H1| exact H2| exact HD| lia]].
      + eapply rw_cells_transport; [exact C| exact MU| exact WM| apply DJS; [exact HA| exact HD| lia]].
    - intros a bs HS HX B. eapply bytes_at_transport; [exact B| exact MU|]. apply DJS; [lia| apply (dj_wpok_low WP _ _ HWP HX)| lia].
    - intros a n HS HX Wr. eapply wr_at_transport; [exact Wr| exact WM].
    - exact (bkeep_of_munch FI AI OB _ m m' MU WM DJ2).
    - intros X n _ HX SW. exact (SK X n HX SW).
    - eapply (apxF_weaken2 W (pparse_WA P) LBK LBK q q st st m m'); [| lia| intros b Hb; exact Hb| intros g Hg; exact Hg|].
      + apply (apxF_of_munch_fkeep FI AI ASL s_0 LB_0 LBK m0 m0 q lo st W m m' HR0 KSUB0 RF0 CLO ltac:(lia)); [| exact WM|].
        * eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in *. destruct Hx as (O1 & O2). split; [lia| exact O2].
        * eapply (fkeep_weaken FI W W stx st m m' FK); [intros x Hx; exact Hx| exact LSUB].
      + intros a Hc Ho. apply outside_of_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL) Hr. cbn [fst snd] in *.
        destruct CL as [CL|[(CL1 & CL2 & CL3)|(b & Hb & CL)]]; cbn [fst snd] in *.
        * apply (inside_not_outside (pparse_WA P) x (y - x) a (inside_sub WP (pparse_WA P) x (y - x) CL HWI)); [lia| exact Ho].
        * apply (new_frame_not_fclient FI AI ASL s_0 LB_0 LBK m0 q st 1 m0 F SF FL HR0 KSUB0 ltac:(lia) RF0 ltac:(lia) eq_refl eq_refl eq_refl a); [left; cbn [FB_of]; lia| exact Hc].
        * apply (blk_not_fclient s LB m b a HR (VSUB b Hb) KSUB); [intros b1 b2 [E|[]] H2; subst b1; exact (VK b b2 Hb H2)| lia| exact Hc].
    - intros rs a CH. apply (fpchain_frame rs m m' _ q a _ CH MU WM). apply Forall_cons; [cbn [snd]; lia|]. apply Forall_cons; [cbn [snd]; lia|]. apply Forall_cons; [cbn [snd]; lia|].
      eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[(CL1 & CL2 & CL3)|(b & Hb & CL)]]; cbn [fst snd] in *.
      + destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      + lia.
      + destruct (BLK b (VSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia.
    - exact SHPK.
    - intros SHZ. exact (shz_stack_fs FI _ m m' lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - QHI; lia)) MU FSW).
    - intros SHR. exact (shr_stack_fs FI _ m m' lo _ _ SHR CLO ltac:(lia) (sh_hi_ok8 q ltac:(clear - QHI; lia)) MU FSW).
    - apply (am_heap_frame FI AI s LB m m' _ HR MU WM). apply Forall_cons; [left; cbn [fst]; lia|].
      apply Forall_cons; [do 3 right; left; cbn [fst snd]; lia|]. apply Forall_cons; [do 4 right; cbn [fst snd]; lia|].
      eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|[(CL1 & CL2 & CL3)|(b & Hb & CL)]]; cbn [fst snd] in *.
      + destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; [do 3 right; left; lia|].
        right; left. exists 0x5e68c8, 0x5e68d0. split; [| unfold a0_wsafe; lia]. apply AMS. unfold a0_static. split; [lia|]. env_band.
      + do 3 right; left. lia.
      + right; right; left. exists b. split; [exact (VSUB b Hb)| lia].
  Qed.

  #[using="mws MWL ws WSL"] Lemma fpchain_keep : forall rs m m2 top bottom a,
    (forall X v, bottom <= X -> bytes_at asegs m X (le8 v) -> bytes_at asegs m2 X (le8 v)) ->
    fpchain m top bottom a rs -> fpchain m2 top bottom a rs.
  Proof.
    induction rs as [|r rest IH]; intros m m2 top bottom a TR CH; cbn [fpchain] in *; [exact CH|].
    destruct CH as (V & V16 & R1 & R2 & a' & R3 & CH'). unfold valid_frame, rd64 in *.
    split; [exact V|]. split; [exact V16|]. split; [split; [apply TR; [lia| exact (proj1 R1)]| exact (proj2 R1)]|]. split; [exact R2|].
    exists a'. split; [split; [apply TR; [lia| exact (proj1 R3)]| exact (proj2 R3)]|].
    eapply IH; [| exact CH']. intros X v HX B. apply TR; [lia| exact B].
  Qed.

  Definition acls (WP : list ivl) (TB : BL) (iv : ivl) : Prop :=
    fst iv < snd iv /\ ( inside WP (fst iv) (snd iv - fst iv) \/ (exists b, In b TB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) ).

  #[using="ASL AMS m0 POK RF0 mws MWL ws WSL"] Lemma ekeep_apxF : forall (W WP : list ivl) (TB OB LBc : BL) (s : PS) (LB : BL) q' (stc : fsstate FI) m m',
    apxF FI AI W LBc q' stc m m' -> alloc_ceiling <= q' -> q' <= q -> (forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) ->
    Forall (acls WP TB) W -> Forall wpok WP -> Forall (fun iv : ivl => inside (pparse_WA P) (fst iv) (snd iv - fst iv)) WP ->
    RHEAP_A FI AI s LB m -> bsub FI AI TB LB -> bsub FI AI OB LBc -> bsub FI AI OB LB -> bsub FI AI LBK LBc -> bsub FI AI LBK LB ->
    idj TB OB -> idj TB LBK ->
    shw m' P 504 ->
    ekeep WP OB m m'.
  Proof.
    intros W WP TB OB LBc s LB q' stc m m' AP QC QQ LSUB HCL HWP HWI HR TSUB OSUBc OSUB KSUBc KSUB TO TK SHP'.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF1 & PF2).
    assert (A0S : A0_FS_FRAMES = 36864) by reflexivity.
    assert (BLK : forall b, In b LB -> 0 <= blk_size b /\ blk_addr b + blk_size b + 16 <= alloc_ceiling /\ 0x609000 <= blk_addr b
                    /\ (blk_addr b + blk_size b + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= blk_addr b)
                    /\ (blk_addr b + blk_size b <= FSB FI \/ FSB FI + A0_FS_SIZE <= blk_addr b)).
    { intros b Hb. destruct (am_block_range FI AI s LB m b HR Hb) as (_ & _ & R3 & R4 & R5 & R6 & R7). auto. }
    assert (LVP : lb (fs_live FI stc) P 504) by (exact (lb_mono _ _ _ _ PLB LSUB)).
    assert (DJ1 : forall a n, ((P <= a /\ a + n <= P + 504) \/ a + n <= 0x609000) -> disjoint_from WP a n -> 0 <= n -> disjoint_from W a n).
    { intros a n HA HD Hn. apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|(b & Hb & CL)].
      - destruct (inside_dj WP x (y - x) a n CL HD ltac:(lia)) as [D|[D|D]]; lia.
      - destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    assert (DJH : forall a n, (alloc_ceiling <= a \/ (0x7fff7000 <= a /\ a + n <= 0x10007fff8000)) -> disjoint_from W a n).
    { intros a n HA. apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|(b & Hb & CL)].
      - destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      - destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5). lia. }
    destruct sh_window_okE as (W1 & W2 & W3 & W4).
    assert (STKSH : forall a, sh lo - sh lo mod 8 <= a < sh q + 8 -> fclient FI AI LBc q' stc a /\ outside W a).
    { intros a Ha. assert (SLO : sh alloc_ceiling - sh alloc_ceiling mod 8 <= sh lo - sh lo mod 8).
      { pose proof (sh_mono alloc_ceiling lo CLO) as HM. clear - HM. Z.div_mod_to_equations. lia. }
      split.
      - right; left. exists (sh lo - sh lo mod 8), 0x10007fff8000. split; [| unfold SH_HI in W4; lia].
        apply AMS. unfold a0_static. split; [unfold SH_HI in W4; lia|]. repeat right. pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)). lia.
      - apply disjoint_outside with (a := a) (n := 1); [| lia]. apply DJH. right. unfold SH_LO, SH_HI in *. lia. }
    unfold H_pent_kit.ekeep; split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
    - intros a cs HA HD C. apply (apxF_rw_cells FI AI W LBc q' stc m m' a cs AP C); [| apply DJ1; [destruct HA as [HA|[_ HA]]; [left; exact HA| right; exact HA]| exact HD| lia]].
      destruct HA as [[H1 H2]|[HS HA]].
      + apply fclient_range_lb. apply (Contracts.lb_sub _ _ _ _ _ LVP); lia.
      + apply (fclient_range_static FI AI LBc q' stc a _ a (a + Z.of_nat (cells_size cs)) (AMS _ _ HS)); lia.
    - intros a bs HS HX B. apply (apxF_bytes_at FI AI W LBc q' stc m m' a bs AP B).
      + apply (fclient_range_static FI AI LBc q' stc a _ a (a + Z.of_nat (length bs)) (AMS _ _ HS)); lia.
      + apply DJ1; [right; lia| apply (dj_wpok_low WP _ _ HWP HX)| lia].
    - intros a n HS HX Wr. apply (apxF_wr_at FI AI W LBc q' stc m m' a n AP Wr).
      + apply (fclient_range_static FI AI LBc q' stc a _ a (a + n) (AMS _ _ HS)); lia.
      + destruct (Z_le_gt_dec 0 n) as [Hn|Hn]; [apply DJ1; [right; lia| apply (dj_wpok_low WP _ _ HWP HX)| lia]|].
        apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
        destruct CL as [CL|(b & Hb & CL)]; [destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia| destruct (BLK b (TSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5); lia].
    - intros b X cs Hb L1 L2 C. apply (apxF_rw_cells FI AI W LBc q' stc m m' X cs AP C); [apply (fclient_range_block FI AI LBc q' stc X _ b (OSUBc b Hb) L1 L2)|].
      destruct (BLK b (OSUB b Hb)) as (Z1 & Z2 & Z3 & Z4 & Z5).
      apply dj_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL). cbn [fst snd] in *.
      destruct CL as [CL|(b' & Hb' & CL)].
      + destruct (inside_wpok WP x (y - x) HWP CL ltac:(lia)) as [D|D]; lia.
      + assert (NE : b' <> b) by (apply (idj_neq TB OB b' b TO Hb' Hb)).
        destruct (am_blocks_disjoint FI AI s LB m b' b HR (TSUB b' Hb') (OSUB b Hb) NE); lia.
    - intros X n X1 X2 SW. pose proof (shw_win_ok _ _ _ SW) as [Hn _].
      eapply (shw_band_eq m m' X n 0x7fffa000 0x800b9200 SW).
      + intros a Ha v Hv. refine (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(lia) _ _)) Hv).
        * right; left. exists 0x7fffa000, 0x800b9200. split; [| lia]. apply AMS. unfold a0_static. split; [lia|]. do 11 right. left. lia.
        * apply disjoint_outside with (a := a) (n := 1); [| lia]. apply DJH. right. lia.
      + lia.
      + lia.
      + reflexivity.
      + reflexivity.
      + unfold sh, SHADOW_OFF. clear - X1. Z.div_mod_to_equations. lia.
      + intros _. unfold sh, SHADOW_OFF. clear - X2 Hn. Z.div_mod_to_equations. lia.
    - eapply (apxF_weaken2 W (pparse_WA P) LBK LBc q q' st stc m m' AP QQ KSUBc LSUB).
      intros a Hc Ho. apply outside_of_forall. eapply Forall_impl; [| exact HCL]. intros [x y] (XY & CL) Hr. cbn [fst snd] in *.
      destruct CL as [CL|(b & Hb & CL)].
      + apply (inside_not_outside (pparse_WA P) x (y - x) a (inside_sub WP (pparse_WA P) x (y - x) CL HWI)); [lia| exact Ho].
      + apply (blk_not_fclient s LB m b a HR (TSUB b Hb) KSUB); [intros b1 b2 [E|[]] H2; subst b1; exact (TK b b2 Hb H2)| lia| exact Hc].
    - intros rs a CH. apply (fpchain_keep rs m m' _ q a); [| exact CH]. intros X v HX B.
      apply (apxF_bytes_at FI AI W LBc q' stc m m' X _ AP B); [apply fclient_range_above; lia| apply DJH; left; lia].
    - intros _. exact SHP'.
    - intros SHZ a Ha. destruct (STKSH a ltac:(lia)) as [C O]. exact (gkeep_mrd _ _ _ _ (proj1 (AP a ltac:(unfold SH_LO, SH_HI in *; lia) C O)) (SHZ a Ha)).
    - intros SHR a Ha. destruct (SHR a Ha) as [v Hv]. exists v. destruct (STKSH a Ha) as [C O]. exact (gkeep_mrd _ _ _ v (proj1 (AP a ltac:(unfold SH_LO, SH_HI in *; lia) C O)) Hv).
  Qed.

  #[using="Type"] Lemma ekeep_trans : forall WP OB m1 m2 m3, ekeep WP OB m1 m2 -> ekeep WP OB m2 m3 -> ekeep WP OB m1 m3.
  Proof.
    intros WP OB m1 m2 m3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    unfold H_pent_kit.ekeep; split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
    - intros a cs HA HD C. exact (C1 a cs HA HD (A1 a cs HA HD C)).
    - intros a bs HS HX B. exact (C2 a bs HS HX (A2 a bs HS HX B)).
    - intros a n HS HX Wr. exact (C3 a n HS HX (A3 a n HS HX Wr)).
    - exact (bkeep_trans FI AI OB m1 m2 m3 A4 C4).
    - intros X n X1 X2 SW. exact (C5 X n X1 X2 (A5 X n X1 X2 SW)).
    - exact (apxF_trans FI AI _ _ _ _ m1 m2 m3 A6 C6).
    - intros rs a CH. exact (C7 rs a (A7 rs a CH)).
    - intros H. exact (C8 (A8 H)).
    - intros H. exact (C9 (A9 H)).
    - intros H. exact (C10 (A10 H)).
  Qed.

  #[using="Type"] Lemma ekeep_weaken : forall WP WP' OB m m', ekeep WP OB m m' -> (forall a n, disjoint_from WP' a n -> disjoint_from WP a n) -> ekeep WP' OB m m'.
  Proof.
    intros WP WP' OB m m' (A1 & A2) HS. split; [| exact A2]. intros a cs HA HD C. exact (A1 a cs HA (HS _ _ HD) C).
  Qed.

  #[using="Type"] Lemma ekeep_sub : forall WP OB OB' m m', ekeep WP OB m m' -> bsub FI AI OB' OB -> ekeep WP OB' m m'.
  Proof.
    intros WP OB OB' m m' (A1 & A2 & A3 & A4 & AR) HS. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [| exact AR].
    exact (bkeep_sub FI AI OB OB' m m' A4 HS).
  Qed.

  #[using="mws MWL ws WSL"] Lemma ek_meth : forall WP OB m m' meth, ekeep WP OB m m' -> disjoint_from WP P 8 -> p_meth m P meth -> p_meth m' P meth.
  Proof. intros WP OB m m' meth EK DJ [C R]. split; [| exact R]. apply (ek_pcell WP OB m m' _ _ EK); [lia| simpl_sizes; lia| simpl_sizes; exact DJ| exact C]. Qed.
  #[using="mws MWL ws WSL"] Lemma ek_ent : forall WP OB m m' eb el, ekeep WP OB m m' -> disjoint_from WP (P + 384) 16 -> p_ent m P eb el -> p_ent m' P eb el.
  Proof. intros WP OB m m' eb el EK DJ C. unfold p_ent in *. apply (ek_pcell WP OB m m' _ _ EK); [lia| simpl_sizes; lia| simpl_sizes; exact DJ| exact C]. Qed.
  #[using="mws MWL ws WSL"] Lemma ek_ctl : forall WP OB m m' err hack pos entp clen csz esp, ekeep WP OB m m' -> disjoint_from WP (P + 440) 40 ->
    p_ctl m P err hack pos entp clen csz esp -> p_ctl m' P err hack pos entp clen csz esp.
  Proof.
    intros WP OB m m' err hack pos entp clen csz esp EK DJ [C R]. split; [| exact R].
    apply (ek_pcell WP OB m m' _ _ EK); [lia| unfold p_ctl_cells; simpl_sizes; lia| unfold p_ctl_cells; simpl_sizes; exact DJ| exact C].
  Qed.
  #[using="mws MWL ws WSL"] Lemma ek_scan : forall WP OB m m' cur, ekeep WP OB m m' -> disjoint_from WP (P + 480) 20 -> p_scan m P cur -> p_scan m' P cur.
  Proof. intros WP OB m m' cur EK DJ C. unfold p_scan in *. apply (ek_pcell WP OB m m' _ _ EK); [lia| simpl_sizes; lia| simpl_sizes; exact DJ| exact C]. Qed.
  #[using="mws MWL ws WSL"] Lemma ek_msg : forall WP OB (LB : BL) m m' A len cap okm bs, ekeep WP OB m m' -> disjoint_from WP (P + 400) 32 -> bsub FI AI (okbA FI AI okm A cap) OB ->
    p_msg FI AI m LB P A len cap okm bs -> p_msg FI AI m' LB P A len cap okm bs.
  Proof.
    intros WP OB LB m m' A len cap okm bs EK DJ SUB (MBC & OWN & R1 & R2 & R3). pose proof EK as (_ & _ & _ & BK & _).
    split; [apply (ek_pcell WP OB m m' _ _ EK); [lia| unfold mbuf_cells; simpl_sizes; lia| unfold mbuf_cells; simpl_sizes; exact DJ| exact MBC]|].
    split; [| split; [exact R1| split; [exact R2| exact R3]]].
    destruct okm as [k|]; cbn [mownA] in *; [| exact OWN]. destruct OWN as [HIN TXC]. split; [exact HIN|].
    apply (BK (k, A, cap + 1) A _ (SUB _ (or_introl eq_refl))); [cbn [blk_addr fst snd]; lia| | exact TXC].
    cbn [blk_addr blk_size fst snd cells_size csize]. destruct TXC as [[W _] _]. cbn in W. lia.
  Qed.

  #[using="mws MWL ws WSL"] Lemma pctl_split : forall m err hack pos entp clen csz esp,
    rw_cells asegs m (P + 440) (p_ctl_cells err hack pos entp clen csz esp) ->
    rw_cells asegs m (P + 440) [C4 (wz err)] /\ rw_cells asegs m (P + 444) [C4 (wz hack)] /\ rw_cells asegs m (P + 448) [C4 (wz pos)]
    /\ rw_cells asegs m (P + 452) [C4 (wz entp)] /\ rw_cells asegs m (P + 456) [C4 (wz clen)] /\ rw_cells asegs m (P + 460) [C4 (wz 0)]
    /\ rw_cells asegs m (P + 464) [C8 (wz csz)] /\ rw_cells asegs m (P + 472) [C8 (wz esp)].
  Proof.
    intros m err hack pos entp clen csz esp H. unfold p_ctl_cells in H.
    split_chunk H 1%nat H1 R1. split_chunk R1 1%nat H2 R2. split_chunk R2 1%nat H3 R3. split_chunk R3 1%nat H4 R4.
    split_chunk R4 1%nat H5 R5. split_chunk R5 1%nat H6 R6. split_chunk R6 1%nat H7 H8.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7| exact H8].
  Qed.
  #[using="mws MWL ws WSL"] Lemma pctl_join : forall m err hack pos entp clen csz esp,
    rw_cells asegs m (P + 440) [C4 (wz err)] -> rw_cells asegs m (P + 444) [C4 (wz hack)] -> rw_cells asegs m (P + 448) [C4 (wz pos)] ->
    rw_cells asegs m (P + 452) [C4 (wz entp)] -> rw_cells asegs m (P + 456) [C4 (wz clen)] -> rw_cells asegs m (P + 460) [C4 (wz 0)] ->
    rw_cells asegs m (P + 464) [C8 (wz csz)] -> rw_cells asegs m (P + 472) [C8 (wz esp)] ->
    rw_cells asegs m (P + 440) (p_ctl_cells err hack pos entp clen csz esp).
  Proof.
    intros m err hack pos entp clen csz esp H1 H2 H3 H4 H5 H6 H7 H8. unfold p_ctl_cells.
    join_chunks H7 H8 J7. join_chunks H6 J7 J6. join_chunks H5 J6 J5. join_chunks H4 J5 J4. join_chunks H3 J4 J3. join_chunks H2 J3 J2. join_chunks H1 J2 J1.
    exact J1.
  Qed.

  #[using="mws MWL ws WSL"] Lemma ek_methw : forall WP OB m m' meth, ekeep WP OB m m' -> disjoint_from WP P 8 -> p_methwA m P meth -> p_methwA m' P meth.
  Proof. intros WP OB m m' meth EK DJ [C R]. split; [| exact R]. apply (ek_pcell WP OB m m' _ _ EK); [lia| simpl_sizes; lia| simpl_sizes; exact DJ| exact C]. Qed.
  #[using="mws MWL ws WSL"] Lemma ek_uri : forall WP OB m m' uc, ekeep WP OB m m' -> disjoint_from WP (P + 8) 216 -> p_uri m P uc -> p_uri m' P uc.
  Proof. intros WP OB m m' uc EK DJ [C R]. split; [| exact R]. apply (ek_pcell WP OB m m' _ _ EK); [lia| rewrite R; lia| rewrite R; exact DJ| exact C]. Qed.
  #[using="mws MWL ws WSL"] Lemma ek_rs : forall WP OB m m' rm sc, ekeep WP OB m m' -> disjoint_from WP (P + 224) 8 -> p_rs m P rm sc -> p_rs m' P rm sc.
  Proof. intros WP OB m m' rm sc EK DJ [C R]. split; [| exact R]. apply (ek_pcell WP OB m m' _ _ EK); [lia| simpl_sizes; lia| simpl_sizes; exact DJ| exact C]. Qed.
  #[using="mws MWL ws WSL"] Lemma ek_ver : forall WP OB m m' isreq maj min, ekeep WP OB m m' -> disjoint_from WP (P + 264) 24 -> p_ver m P isreq maj min -> p_ver m' P isreq maj min.
  Proof.
    intros WP OB m m' isreq maj min EK DJ [(pad & C) R]. split; [| exact R]. exists pad.
    apply (ek_pcell WP OB m m' _ _ EK); [lia| simpl_sizes; lia| simpl_sizes; exact DJ| exact C].
  Qed.
  #[using="mws MWL ws WSL"] Lemma ek_url : forall WP OB m m' ub, ekeep WP OB m m' -> disjoint_from WP (P + 432) 8 -> p_url m P ub -> p_url m' P ub.
  Proof. intros WP OB m m' ub EK DJ [C R]. split; [| exact R]. apply (ek_pcell WP OB m m' _ _ EK); [lia| simpl_sizes; lia| simpl_sizes; exact DJ| exact C]. Qed.
  #[using="mws MWL ws WSL"] Lemma ek_smsg : forall WP OB (LB : BL) m m' SA slen scap sok sbs, ekeep WP OB m m' -> disjoint_from WP (P + 232) 32 -> bsub FI AI (okbA FI AI sok SA scap) OB ->
    p_smsgWA FI AI m LB P SA slen scap sok sbs -> p_smsgWA FI AI m' LB P SA slen scap sok sbs.
  Proof.
    intros WP OB LB m m' SA slen scap sok sbs EK DJ SUB (MBC & OWN & R1 & R2). pose proof EK as (_ & _ & _ & BK & _).
    split; [apply (ek_pcell WP OB m m' _ _ EK); [lia| unfold mbuf_cells; simpl_sizes; lia| unfold mbuf_cells; simpl_sizes; exact DJ| exact MBC]|].
    split; [| split; [exact R1| exact R2]].
    destruct sok as [k|]; cbn [mownA] in *; [| exact OWN]. destruct OWN as [HIN TXC]. split; [exact HIN|].
    apply (BK (k, SA, scap + 1) SA _ (SUB _ (or_introl eq_refl))); [cbn [blk_addr fst snd]; lia| | exact TXC].
    cbn [blk_addr blk_size fst snd cells_size csize]. destruct TXC as [[W _] _]. cbn in W. lia.
  Qed.

  #[using="POK mws MWL WSL GLR"] Lemma ek_ppstat : forall WP OB m m' (mws' : list word), ekeep WP OB m m' -> Forall wpok WP -> length mws' = 22%nat ->
    pp_statA m gmax canary ws mws' cslack GL -> (exists ev, clow canary ev m') -> pp_statA m' gmax canary ws mws' cslack GL.
  Proof.
    intros WP OB m m' mws' EK HW ML (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & (TB1 & TB2) & A12 & TS & A14 & A15 & A16 & A17 & A18 & (gv & A19) & _ & A21 & _ & _) (ev & CL1 & CL2 & CL3).
    pose proof EK as (_ & BK & WK & _ & SK & _).
    destruct (ek_stat2 WP OB m m' EK (conj A1 A2)) as [B1 B2].
    unfold pp_statA.
    split; [exact B1|]. split; [exact B2|].
    split; [apply SK; [lia| lia| exact A3]|]. split; [apply SK; [lia| lia| exact A4]|].
    split; [exact (ek_pstat WP OB m m' EK HW A5)|].
    split; [apply SK; [lia| lia| exact A6]|]. split; [apply SK; [lia| lia| exact A7]|].
    split; [apply SK; [lia| lia| exact A8]|]. split; [apply SK; [lia| lia| exact A9]|]. split; [apply SK; [unfold A0_FMT_SSCANF_VER; lia| unfold A0_FMT_SSCANF_VER; lia| exact A10]|].
    split. { split; [apply BK; [unfold a0_static; rewrite u64s_length, ML; split; [lia|]; right; left; lia| rewrite u64s_length, ML; lia| exact TB1]|
                     apply WK; [unfold a0_static; rewrite ML; split; [lia|]; right; left; lia| rewrite ML; lia| exact TB2]]. }
    split; [apply SK; [lia| lia| exact A12]|].
    split. { intros i Hi. destruct (TS i Hi) as (Sx & str & slack & E1 & E2 & E3 & E4 & E5 & E6 & E7).
             exists Sx, str, slack. repeat (split; [assumption|]). apply SK; [lia| lia| exact E7]. }
    split; [apply SK; [lia| lia| exact A14]|]. split; [apply SK; [lia| lia| exact A15]|].
    split; [apply SK; [lia| lia| exact A16]|]. split; [apply SK; [lia| lia| exact A17]|].
    split; [apply (ek_scell WP OB m m' _ _ EK HW); [stat_band| simpl_sizes; lia| exact A18]|].
    split; [exists gv; apply (ek_scell WP OB m m' _ _ EK HW); [stat_band| simpl_sizes; lia| exact A19]|].
    split; [exists ev; exact CL1|].
    split; [apply SK; [unfold A0_ERRNO; lia| unfold A0_ERRNO; lia| exact A21]|].
    split; [exact CL2| exact CL3].
  Qed.

  Variables (t_0 : pstA FI AI).
  Notation POST := (pparse_post_A FI AI ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s_0 LB_0 LBK P lo gmax canary ws mws cslack GL t_0 m0).

  Definition QX (s : PS) (LB : BL) (m : mem) (t : pstA FI AI) : Prop :=
    RHEAP_A FI AI s LB m /\ p_parserA FI AI m LB P t /\ pa_isreq FI AI t = pa_isreq FI AI t_0
    /\ bsub FI AI (pa_blocks FI AI t ++ LBK) LB /\ NoDup (map blk_id (pa_blocks FI AI t ++ LBK))
    /\ pp_statA m gmax canary ws mws cslack GL
    /\ shw m P 504 /\ shz m (sh lo) (sh q) /\ shr m (sh lo - sh lo mod 8) (sh q + 8)
    /\ apxF FI AI (pparse_WA P) LBK q st m0 m.

  Definition QP (s : PS) (LB : BL) (t : pstA FI AI) : Prop :=
    (exists N1 LB1 N2 LB2 d k d2, pfirst FI AI (am_nsec FI AI s_0) LB_0 N1 LB1 /\ H_phdr.hlines FI AI d N1 LB1 N2 LB2
          /\ H_pent_kit.esteps FI AI k d2 N2 LB2 (am_nsec FI AI s) LB
          /\ 0 <= k <= 2 * gmax + 5 /\ 0 <= d /\ 0 <= d2 /\ d + d2 <= pa_len FI AI t_0 - pa_cur FI AI t_0
          /\ 5 * (am_nsec FI AI s - (k + 1)) <= 5 * am_nsec FI AI s_0 - phiH FI AI (pa_hs FI AI t_0) + phiH FI AI (pa_hs FI AI t))
    /\ H_phdr.hsumA FI AI (pa_hs FI AI t) <= H_phdr.hsumA FI AI (pa_hs FI AI t_0) + (pa_len FI AI t_0 - pa_cur FI AI t_0)
    /\ (length LB + length (pa_blocks FI AI t_0) <= length LB_0 + length (pa_blocks FI AI t))%nat.

  #[using="Type"] Lemma QX_done : forall (s : PS) (LB : BL) m' (st' : fsstate FI) (t : pstA FI AI) r t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    QX s LB m' t -> QP s LB t ->
    mem_inv asegs m' -> stk asegs m' lo q -> asan_env asegs m' -> RFAKE FI st' m' -> fs_live FI st' = fs_live FI st -> 0 <= r <= 5 ->
    POST s LB (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F_ (ret_pc ra) fc None m' (seg_rom asegs)).
  Proof.
    intros s LB m' st' t r t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (HR & PP & ISR & SUB & ND & STAT & SHP & SHZ & SHR & APF) (SCR & HSF & CNT) MI ST AE RF LIVE RR.
    unfold pparse_post_A.
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', st', r, t.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact AE|]. split; [exact RF|]. split; [exact LIVE|].
    split; [exact APF|]. split; [exact HR|]. split; [exact PP|]. split; [exact ISR|]. split; [exact SUB|]. split; [exact ND|].
    split; [exact SCR|]. split; [exact HSF|]. split; [exact CNT|]. split; [exact STAT|]. split; [exact SHP|]. split; [exact SHZ|]. split; [exact SHR| exact RR].
  Qed.

  #[using="POK MWL WSL GLR"] Lemma QX_move : forall WP OB (s : PS) (LB : BL) m (t : pstA FI AI) (s' : PS) (LB' : BL) m' (t' : pstA FI AI),
    QX s LB m t -> ekeep WP OB m m' -> Forall wpok WP ->
    RHEAP_A FI AI s' LB' m' -> p_parserA FI AI m' LB' P t' -> pa_isreq FI AI t' = pa_isreq FI AI t ->
    bsub FI AI (pa_blocks FI AI t' ++ LBK) LB' -> NoDup (map blk_id (pa_blocks FI AI t' ++ LBK)) -> (exists ev, clow canary ev m') ->
    QX s' LB' m' t'.
  Proof.
    intros WP OB s LB m t s' LB' m' t' (HR & PP & ISR & SUB & ND & STAT & SHP & SHZ & SHR & APF) EK HW HR' PP' ISR' SUB' ND' CL'.
    pose proof EK as (_ & _ & _ & _ & _ & K5 & _ & K7 & K8 & K9).
    split; [exact HR'|]. split; [exact PP'|]. split; [rewrite ISR'; exact ISR|]. split; [exact SUB'|]. split; [exact ND'|].
    split; [exact (ek_ppstat WP OB m m' mws EK HW MWL STAT CL')|].
    split; [exact (K7 SHP)|]. split; [exact (K8 SHZ)|]. split; [exact (K9 SHR)|].
    eapply (apxF_trans FI AI); [exact APF| exact K5].
  Qed.

  #[using="mws MWL ws WSL"] Lemma ek_parser_sc : forall WP OB (LB : BL) m m' (t : pstA FI AI), ekeep WP OB m m' -> disjoint_from WP P 480 -> bsub FI AI (pa_blocks FI AI t) OB ->
    p_parserA FI AI m LB P t -> p_scan m' P (pa_cur FI AI t) -> p_parserA FI AI m' LB P t.
  Proof.
    intros WP OB LB m m' t EK DJ SUB (_ & PMSG & CUR & PMETH & PURI & PRS & PSM & PVER & PHL & PENT & PCTL & PURL & UBO) PSC'.
    assert (DJS : forall X n, P <= X -> X + n <= P + 480 -> disjoint_from WP X n) by (intros X n H1 H2; eapply disjoint_from_sub; [exact DJ| lia| lia]).
    unfold pa_blocks in SUB.
    split; [exact PSC'|].
    split; [apply (ek_msg _ _ LB m m' _ _ _ _ _ EK (DJS (P + 400) 32 ltac:(lia) ltac:(lia))); [intros b Hb; apply SUB; apply in_or_app; right; apply in_or_app; left; exact Hb| exact PMSG]|].
    split; [exact CUR|].
    split; [exact (ek_methw _ _ m m' _ EK (DJS P 8 ltac:(lia) ltac:(lia)) PMETH)|].
    split; [exact (ek_uri _ _ m m' _ EK (DJS (P + 8) 216 ltac:(lia) ltac:(lia)) PURI)|].
    split; [exact (ek_rs _ _ m m' _ _ EK (DJS (P + 224) 8 ltac:(lia) ltac:(lia)) PRS)|].
    split; [apply (ek_smsg _ _ LB m m' _ _ _ _ _ EK (DJS (P + 232) 32 ltac:(lia) ltac:(lia))); [intros b Hb; apply SUB; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb| exact PSM]|].
    split; [exact (ek_ver _ _ m m' _ _ _ EK (DJS (P + 264) 24 ltac:(lia) ltac:(lia)) PVER)|].
    split; [apply (ek_hlist _ _ m m' _ _ _ EK PHL); [intros b Hb; apply SUB; apply in_or_app; left; exact Hb| exact (DJS (P + 288) 96 ltac:(lia) ltac:(lia))]|].
    split; [exact (ek_ent _ _ m m' _ _ EK (DJS (P + 384) 16 ltac:(lia) ltac:(lia)) PENT)|].
    split; [exact (ek_ctl _ _ m m' _ _ _ _ _ _ _ EK (DJS (P + 440) 40 ltac:(lia) ltac:(lia)) PCTL)|].
    split; [exact (ek_url _ _ m m' _ EK (DJS (P + 432) 8 ltac:(lia) ltac:(lia)) PURL)| exact UBO].
  Qed.

  #[using="mws MWL ws WSL"] Lemma ek_parser : forall WP OB (LB : BL) m m' (t : pstA FI AI), ekeep WP OB m m' -> disjoint_from WP P 504 -> bsub FI AI (pa_blocks FI AI t) OB ->
    p_parserA FI AI m LB P t -> p_parserA FI AI m' LB P t.
  Proof.
    intros WP OB LB m m' t EK DJ SUB PP.
    apply (ek_parser_sc WP OB LB m m' t EK ltac:(eapply disjoint_from_sub; [exact DJ| lia| lia]) SUB PP).
    destruct PP as (PSC & _). exact (ek_scan _ _ m m' _ EK ltac:(eapply disjoint_from_sub; [exact DJ| lia| lia]) PSC).
  Qed.

  #[using="P POK mws MWL ws WSL"] Lemma pWQ_cls : Forall (ecls [] []) pWQ.
  Proof.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & _).
    unfold H_pparse_seg.pWQ, ecls. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [lia|]).
    - left. lia.
    - right; left. lia.
    - right; right; left. lia.
    - right; right; right; left. lia.
  Qed.
  #[using="ASL AMS POK RF0 MWL HR0 KSUB0 WSL GLR"] Lemma exitJ : forall q' r (s : PS) (LB : BL) m (t : pstA FI AI) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    QX s LB m t -> QP s LB t -> pinvQ q' m -> 0 <= r <= 5 ->
    AJ FI AI J POST (exitstQ q' r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m) s LB.
  Proof.
    intros q' r s LB m t x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 QXF QPF INV RR.
    apply aj_cps.
    eapply evt_mono.
    { apply (exitQ q' r (fun mm => munch pWQ m mm /\ wmono asegs m mm)); [exact INV| split; [apply munch_refl| apply wmono_refl]|].
      intros ma mb [MU1 WM1] MU2 WM2. split; [eapply munch_trans; eassumption| eapply wmono_trans; eassumption]. }
    intros ms' (r0 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & -> & MI & LIVE & RF & ST & AE & (MU & WM) & ->).
    apply (aj_ret FI AI J).
    pose proof QXF as (HR & PP & _ & SUB & ND & STAT & _).
    assert (OSUB : bsub FI AI (pa_blocks FI AI t) LB) by (intros b Hb; apply SUB; apply in_or_app; left; exact Hb).
    assert (KSUB : bsub FI AI LBK LB) by (intros b Hb; apply SUB; apply in_or_app; right; exact Hb).
    destruct (ekeep_munch pWQ [] [] (pa_blocks FI AI t) s LB m m' MU WM pWQ_cls (Forall_nil _) (Forall_nil _) HR
                (fun b Hb => False_ind _ Hb) OSUB KSUB (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha)) as [EK HR'].
    eapply (QX_done s LB m' st' t r); [| exact QPF| exact MI| exact ST| exact AE| exact RF| exact LIVE| exact RR].
    eapply (QX_move [] _ s LB m t s LB m' t); [exact QXF| exact EK| apply Forall_nil| exact HR'
      | exact (ek_parser [] _ LB m m' t EK I (fun b Hb => Hb) PP)| reflexivity| exact SUB| exact ND|].
    destruct STAT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (ev & CE) & _ & CG & CS).
    apply (ek_clow [] _ m m' EK (Forall_nil _) I). exists ev. exact (conj CE (conj CG CS)).
  Qed.

  #[using="Type"] Lemma QX_clow : forall (s : PS) (LB : BL) m (t : pstA FI AI), QX s LB m t -> exists ev, clow canary ev m.
  Proof.
    intros s LB m t (_ & _ & _ & _ & _ & STAT & _).
    destruct STAT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (ev & CE) & _ & CG & CS). exists ev. exact (conj CE (conj CG CS)).
  Qed.
  #[using="ASL AMS POK RF0 MWL s_0 LB_0 HR0 KSUB0 WSL GLR"] Lemma sf_move : forall (s : PS) (LB : BL) m m' (t : pstA FI AI), QX s LB m t -> munch [(SF, SF + 16)]%Z m m' -> wmono asegs m m' -> QX s LB m' t.
  Proof.
    intros s LB m m' t QXF MU WM. pose proof QXF as (HR & PP & _ & SUB & ND & _).
    assert (OSUB : bsub FI AI (pa_blocks FI AI t) LB) by (intros b Hb; apply SUB; apply in_or_app; left; exact Hb).
    assert (KSUB : bsub FI AI LBK LB) by (intros b Hb; apply SUB; apply in_or_app; right; exact Hb).
    assert (CLS : Forall (ecls [] []) [(SF, SF + 16)]%Z).
    { constructor; [| constructor]. unfold ecls. cbn [fst snd]. split; [lia|]. right; right; left. lia. }
    destruct (ekeep_munch _ [] [] (pa_blocks FI AI t) s LB m m' MU WM CLS (Forall_nil _) (Forall_nil _) HR
                (fun b Hb => False_ind _ Hb) OSUB KSUB (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha)) as [EK HR'].
    eapply (QX_move [] _ s LB m t s LB m' t); [exact QXF| exact EK| apply Forall_nil| exact HR'
      | exact (ek_parser [] _ LB m m' t EK I (fun b Hb => Hb) PP)| reflexivity| exact SUB| exact ND|].
    exact (ek_clow [] _ m m' EK (Forall_nil _) I (QX_clow s LB m t QXF)).
  Qed.

  #[using="mws MWL ws WSL"] Lemma pctx_of : forall (s : PS) (LB : BL) m A len cap (kA : K) bs cur ev,
    RHEAP_A FI AI s LB m -> p_scan m P cur -> p_msg FI AI m LB P A len cap (Some kA) bs ->
    shw m P 504 -> shw m SEPTAB_A 20 -> shw m FMT_REQ09_A 10 -> shw m FMT_REQ_A 22 ->
    shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) -> clow canary ev m -> shw m ERRNO_A 4 ->
    pctx A len cap cur bs m /\ txt_okA A len cap /\ In (kA, A, cap + 1) LB /\ nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) /\ cap + 1 <= 2^26 + 16.
  Proof.
    intros s LB m A len cap kA bs cur ev HR PSC PMSG SHP SHSEP SHF1 SHF2 SHZ SHR CLOW SHE.
    destruct (p_msg_facts FI AI m LB P A len cap (Some kA) bs s HR PMSG) as (HL & HCp & LBS0 & _ & SOME).
    destruct (SOME ltac:(discriminate)) as (S1 & S2 & S3 & S4 & S5 & S6).
    destruct PMSG as (MBC & [HIN TXC] & _ & _ & MNUL).
    split.
    { unfold H_pparse_seg.pctx. split; [exact PSC|]. split; [exact MBC|]. split; [exact TXC|]. split; [exact SHP|].
      split; [eapply (block_shw FI AI s LB m (kA, A, cap + 1) A (cap + 1) HR HIN); cbn; lia|].
      split; [exact SHSEP|]. split; [exact SHF1|]. split; [exact SHF2|]. split; [exact SHZ|]. split; [exact SHR|]. split; [exists ev; exact CLOW| exact SHE]. }
    split; [| split; [exact HIN| split; [exact MNUL| unfold LMAX_A in HCp; clear - HCp; lia]]].
    unfold H_pparse_seg.txt_okA. split; [exact S1|]. split; [exact S2|]. split; [exact HL|]. split; [exact S3|]. split; [exact S5|]. split; [exact S6|].
    unfold LMAX_A in HCp. clear - HCp. lia.
  Qed.
  #[using="Type"] Lemma pctx_back : forall (LB : BL) m A len cap cur bs (kA : K), pctx A len cap cur bs m -> In (kA, A, cap + 1) LB ->
    0 <= len <= cap -> cap + 1 <= LMAX_A -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) ->
    p_scan m P cur /\ p_msg FI AI m LB P A len cap (Some kA) bs /\ (exists ev, clow canary ev m).
  Proof.
    intros LB m A len cap cur bs kA (SC & MBC & TXT & _ & _ & _ & _ & _ & _ & _ & CLW & _) HIN LC CB NUL.
    split; [exact SC|]. split; [| exact CLW]. split; [exact MBC|]. split; [cbn [mownA]; split; [exact HIN| exact TXT]|]. split; [exact LC|]. split; [exact CB| exact NUL].
  Qed.

  #[using="ASL AMS m0 POK RF0 mws MWL ws WSL"] Lemma apres_ek : forall (s : PS) (LB LBc OB : BL) q' (stc : fsstate FI) m m',
    apres FI AI LBc q' m m' -> RFAKE FI stc m -> fs_live FI stc = fs_newff FI st 1 :: fs_live FI st -> q + -336 <= q' <= q + -320 ->
    RHEAP_A FI AI s LB m -> bsub FI AI OB LBc -> bsub FI AI OB LB -> bsub FI AI LBK LBc -> bsub FI AI LBK LB -> shw m P 504 ->
    ekeep [] OB m m'.
  Proof.
    intros s LB LBc OB q' stc m m' AP RF LIVE1 QB HR OSUBc OSUB KSUBc KSUB SHP.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    destruct (elive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    assert (APF : apxF FI AI [] LBc q' stc m m') by (apply (apxF_of_apx FI AI [] LBc LBc q' q' stc stc m m m' (apx_of_apres FI AI [] LBc q' m m' AP) RF ltac:(lia) (fun b Hb => Hb) (fun g Hg => Hg))).
    apply (ekeep_apxF [] [] [] OB LBc s LB q' stc m m' APF ltac:(lia) ltac:(lia) LSUB (Forall_nil _) (Forall_nil _) (Forall_nil _) HR
             (fun b Hb => False_ind _ Hb) OSUBc OSUB KSUBc KSUB (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha)).
    apply (shw_apxF_lb FI AI [] LBc q' stc m m' P 504 SHP APF RF LVP). intros a _. exact I.
  Qed.
  #[using="q lo P m0 POK RF0"] Lemma ploc_stepA : forall (LBc : BL) q' mb ml vb vl ub ul m m', plocQ mb ml vb vl ub ul m -> apres FI AI LBc q' m m' -> plocQ mb ml vb vl ub ul m'.
  Proof.
    intros LBc q' mb ml vb vl ub ul m m' (j1 & j2 & j3 & HA) AP. exists j1, j2, j3.
    destruct eframe_facts as (FLO & FHI & _).
    eapply (apx_rw_cells FI AI [] LBc q' m m'); [exact (apx_of_apres FI AI [] LBc q' m m' AP)| exact HA| apply aclient_range_fs; simpl_sizes; clear - FLO FHI; lia| exact I].
  Qed.

  #[using="POK mws MWL ws WSL"] Lemma pctx_ek : forall WP OB (s' : PS) (LB' : BL) A len cap cur bs (kA : K) m m',
    pctx A len cap cur bs m -> ekeep WP OB m m' -> Forall wpok WP -> disjoint_from WP (P + 400) 32 -> disjoint_from WP (P + 480) 20 -> disjoint_from WP ERRNO_A 4 ->
    In (kA, A, cap + 1) OB -> RHEAP_A FI AI s' LB' m' -> In (kA, A, cap + 1) LB' -> 0 <= cap -> pctx A len cap cur bs m'.
  Proof.
    intros WP OB s' LB' A len cap cur bs kA m m' (SC & MBC & TXT & SHP & SHA & SHSEP & SHF1 & SHF2 & SHZ & SHR & CL & SHE) EK HW DJM DJS DJE HIN HR' HIN' CAP0.
    pose proof EK as (_ & _ & _ & BK & SK & _ & _ & K7 & K8 & K9).
    unfold H_pparse_seg.pctx.
    split; [apply (ek_pcell WP OB m m' _ _ EK); [lia| simpl_sizes; lia| simpl_sizes; exact DJS| exact SC]|].
    split; [apply (ek_pcell WP OB m m' _ _ EK); [lia| unfold mbuf_cells; simpl_sizes; lia| unfold mbuf_cells; simpl_sizes; exact DJM| exact MBC]|].
    split. { apply (BK (kA, A, cap + 1) A _ HIN); [cbn [blk_addr fst snd]; lia| | exact TXT]. cbn [blk_addr blk_size fst snd cells_size csize]. destruct TXT as [[W _] _]. cbn in W. lia. }
    split; [exact (K7 SHP)|].
    split; [eapply (block_shw FI AI s' LB' m' (kA, A, cap + 1) A (cap + 1) HR' HIN'); cbn; lia|].
    split; [apply SK; [unfold SEPTAB_A; lia| unfold SEPTAB_A; lia| exact SHSEP]|].
    split; [apply SK; [lia| lia| exact SHF1]|]. split; [apply SK; [lia| lia| exact SHF2]|].
    split; [exact (K8 SHZ)|]. split; [exact (K9 SHR)|].
    split; [exact (ek_clow WP OB m m' EK HW DJE CL)|].
    apply SK; [lia| lia| exact SHE].
  Qed.

  #[using="Type"] Lemma pstat_of_pp : forall m, pp_statA m gmax canary ws mws cslack GL -> pstatR m /\ pstatU m /\ shw m A0_FMT_SSCANF_VER 8 /\ shw m SEPTAB_A 20 /\ shw m FMT_REQ09_A 10 /\ shw m FMT_REQ_A 22 /\ shw m ERRNO_A 4.
  Proof.
    intros m ((_ & SHSEP & _) & _ & _ & _ & _ & _ & _ & A8 & A9 & A10 & TB & A12 & TS & A14 & A15 & A16 & A17 & A18 & A19 & _ & A21 & _ & _).
    split; [exact (conj TB (conj A12 TS))|]. split; [exact (conj A14 (conj A15 (conj A16 (conj A17 (conj A18 A19)))))|].
    split; [exact A10|]. split; [exact SHSEP|]. split; [exact A8|]. split; [exact A9| exact A21].
  Qed.

  #[using="ASL AMS POK RF0 MWL HR0 KSUB0 WSL GLR"] Lemma rejoin_exitJ : forall q' r (s : PS) (LB : BL) m (t : pstA FI AI) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    QX s LB m t -> QP s LB t -> pinvQS qshadowU q' m -> 0 <= r <= 5 -> r <> 4 ->
    AJ FI AI J POST (MS (pregsQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (wz r) x28 x29 x30 x31) F_ (wz PQ_REJOIN) fc None m (seg_rom asegs)) s LB.
  Proof.
    intros q' r s LB m t x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 QXF QPF INV RR RN.
    apply aj_cps. apply (rejoinQ q' r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m _ INV RR).
    - intros m' R4 _ _ _. exfalso. exact (RN R4).
    - intros m' _ INV' MU WM. apply evt_done.
      exact (exitJ q' r s LB m' t x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (sf_move s LB m m' t QXF MU WM) QPF INV' RR).
  Qed.

  #[using="IC ASL AMS POK RF0 MWL HR0 KSUB0 WSL GLR"] Lemma reql0J : forall q' (s : PS) (LB : BL) m (t : pstA FI AI) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    QX s LB m t -> QP s LB t -> pinvQ q' m -> pa_okm FI AI t = None ->
    AJ FI AI J POST (reqlstQ q' x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m) s LB.
  Proof.
    intros q' s LB m t x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 QXF QPF INV OKN.
    apply aj_cps. apply (unpoisonQ q' x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m _ INV).
    intros m1 INV1 MU1 WM1.
    pose proof (sf_move s LB m m1 t QXF MU1 WM1) as QX1.
    pose proof QX1 as (HR1 & PP1 & _ & SUB1 & ND1 & STAT1 & SHP1 & SHZ1 & _).
    pose proof PP1 as (PSC & PMSG & CUR & _).
    destruct PMSG as (MBC & OWN & LC & _ & L0). rewrite OKN in OWN, L0. cbn [mownA] in OWN. destruct OWN as (A0 & C0 & _).
    rewrite A0, C0, L0 in MBC. assert (CUR0 : pa_cur FI AI t = 0) by (rewrite L0 in CUR; lia). unfold p_scan in PSC. rewrite CUR0 in PSC.
    destruct (pstat_of_pp m1 STAT1) as (_ & _ & _ & SHSEP & _).
    pose proof INV1 as (_ & SCRQ & _).
    destruct (pscr_split q' m1 SCRQ) as (ty0 & tb0 & tl0 & SCR).
    eapply (skip0Q q' ty0 tb0 tl0); [exact INV1| exact PSC| exact MBC| exact SHP1| exact SHSEP| exact SHZ1| exact SCR|].
    intros r m2 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RR INV2 SC2 MU2 WM2. apply evt_done.

    pose proof INV1 as (_ & _ & _ & _ & (QB & _) & _). pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    assert (OSUB : bsub FI AI (pa_blocks FI AI t) LB) by (intros b Hb; apply SUB1; apply in_or_app; left; exact Hb).
    assert (KSUB : bsub FI AI LBK LB) by (intros b Hb; apply SUB1; apply in_or_app; right; exact Hb).
    assert (CLS : Forall (ecls [(P + 488, P + 496)]%Z []) (rWT q')).
    { unfold rWT, ecls. constructor; [cbn [fst snd]; split; [clear - LO QB; lia| left; clear - CLO LO QB; lia]|].
      constructor; [cbn [fst snd inside]; split; [clear; lia| do 4 right; left; left; clear; lia]| constructor]. }
    assert (HWP : Forall wpok [(P + 488, P + 496)]%Z) by (constructor; [left; unfold H_pparse_seg.inP; cbn [fst snd]; clear; lia| constructor]).
    assert (HWI : Forall (fun iv : ivl => inside (pparse_WA P) (fst iv) (snd iv - fst iv)) [(P + 488, P + 496)]%Z)
      by (constructor; [unfold pparse_WA; cbn [inside fst snd]; left; clear; lia| constructor]).
    destruct (ekeep_munch (rWT q') [(P + 488, P + 496)]%Z [] (pa_blocks FI AI t) s LB m1 m2 MU2 WM2 CLS HWP HWI HR1
                (fun b Hb => False_ind _ Hb) OSUB KSUB (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha)) as [EK HR2].
    assert (QX2 : QX s LB m2 t).
    { eapply (QX_move _ _ s LB m1 t s LB m2 t); [exact QX1| exact EK| exact HWP| exact HR2| | reflexivity| exact SUB1| exact ND1|].
      - apply (ek_parser_sc _ _ LB m1 m2 t EK ltac:(cbn [disjoint_from]; split; [left; clear; lia| exact I]) (fun b Hb => Hb) PP1). unfold p_scan. rewrite CUR0. exact SC2.
      - apply (ek_clow _ _ m1 m2 EK HWP ltac:(cbn [disjoint_from]; split; [left; clear - PLO; lia| exact I]) (QX_clow s LB m1 t QX1)). }
    exact (rejoin_exitJ q' r s LB m2 t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ QX2 QPF INV2 ltac:(lia) ltac:(lia)).
  Qed.

  #[using="ASL AMS m0 POK RF0 mws MWL ws s_0 LB_0 HR0 KSUB0 WSL"] Lemma wmove_ek : forall (W WP : list ivl) (VB OB : BL) (s : PS) (LB : BL) m m',
    wmove W m m' -> shw m' P 504 -> Forall (fcls WP VB) W -> Forall wpok WP -> Forall (fun iv : ivl => inside (pparse_WA P) (fst iv) (snd iv - fst iv)) WP ->
    RHEAP_A FI AI s LB m -> bsub FI AI VB LB -> bsub FI AI OB LB -> bsub FI AI LBK LB -> idj VB OB -> idj VB LBK ->
    ekeep WP OB m m' /\ RHEAP_A FI AI s LB m'.
  Proof.
    intros W WP VB OB s LB m m' (MU & WM & FK) SHP' HCL HWP HWI HR VSUB OSUB KSUB VO VK.
    pose proof POK as POK'. destruct POK' as (CLO & LO & _).
    exact (ekeep_fk W WP VB OB s LB q st m m' MU WM FK ltac:(lia) (fun g Hg => Hg) (fun _ => SHP') HCL HWP HWI HR VSUB OSUB KSUB VO VK).
  Qed.
  Definition WPA : list ivl := [(P + 4, P + 8); (P + 440, P + 444); (P + 480 + 8, P + 480 + 16)]%Z.
  #[using="mws MWL ws WSL"] Lemma WPA_ok : Forall wpok WPA.
  Proof. unfold WPA, wpok, H_pparse_seg.inP. repeat (constructor; [left; cbn [fst snd]; lia|]). constructor. Qed.
  #[using="mws MWL ws WSL"] Lemma WPA_in : Forall (fun iv : ivl => inside (pparse_WA P) (fst iv) (snd iv - fst iv)) WPA.
  Proof. unfold WPA, pparse_WA. repeat (constructor; [cbn [inside fst snd]; left; lia|]). constructor. Qed.
  #[using="mws MWL ws WSL"] Lemma rWA_cls : Forall (fcls WPA []) (H_pparse_reql.rWA FI P st).
  Proof.
    unfold H_pparse_reql.rWA, fcls, WPA.
    constructor; [cbn [fst snd inside]; split; [lia| left; left; lia]|].
    constructor; [cbn [fst snd inside]; split; [lia| left; right; left; lia]|].
    constructor; [cbn [fst snd inside]; split; [lia| left; right; right; left; lia]|].
    constructor; [cbn [fst snd]; split; [lia| right; left; unfold H_pparse_seg.inFJ; cbn [fst snd]; lia]|].
    constructor; [cbn [fst snd]; split; [lia| right; left; unfold H_pparse_seg.inFJ; cbn [fst snd]; lia]|].
    constructor; [cbn [fst snd]; split; [lia| right; left; unfold H_pparse_seg.inFJ; cbn [fst snd]; lia]| constructor].
  Qed.

  #[using="ASL AMS m0 POK RF0 mws MWL ws s_0 LB_0 HR0 KSUB0 WSL"] Lemma rmove_ek : forall (OB : BL) (s : PS) (LB : BL) m m', rmove m m' -> shw m' P 504 -> RHEAP_A FI AI s LB m -> bsub FI AI OB LB -> bsub FI AI LBK LB ->
    ekeep WPA OB m m' /\ RHEAP_A FI AI s LB m'.
  Proof.
    intros OB s LB m m' MV SHP' HR OSUB KSUB.
    exact (wmove_ek _ WPA [] OB s LB m m' MV SHP' rWA_cls WPA_ok WPA_in HR (fun b Hb => False_ind _ Hb) OSUB KSUB (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha)).
  Qed.

  Hypothesis TRH : In (PC0_MALLOC :: 0x8847c :: 0x8aad4 :: bv_unsigned ra :: ras) A0_TRACES.
  Hypothesis TRE : In (PC0_MALLOC :: 0x8847c :: 0x8a000 :: 0x8ab28 :: bv_unsigned ra :: ras) A0_TRACES.
  Hypothesis PBUD : pbud FI AI (pa_len FI AI t_0 - pa_cur FI AI t_0) (2 * gmax + 5) (HCount.cgG FI AI (pa_hs FI AI t_0)) s_0 LB_0.
  Hypothesis CUR0 : 0 <= pa_cur FI AI t_0 <= pa_len FI AI t_0.
  Hypothesis GERM : H_pent_kit.germ_stmt_A FI AI (H_pent_kit.gstA GL).

  Definition P1 (s : PS) (LB : BL) (t : pstA FI AI) : Prop :=
    pfirst FI AI (am_nsec FI AI s_0) LB_0 (am_nsec FI AI s) LB /\ pa_hs FI AI t = pa_hs FI AI t_0
    /\ (length LB + length (pa_blocks FI AI t_0) <= length LB_0 + length (pa_blocks FI AI t))%nat
    /\ pa_len FI AI t = pa_len FI AI t_0 /\ pa_cur FI AI t_0 <= pa_cur FI AI t <= pa_len FI AI t
    /\ (H_phdr.hbud FI AI (pa_len FI AI t_0 - pa_cur FI AI t_0) (HCount.cgG FI AI (pa_hs FI AI t_0)) s LB
        /\ forall d N2 LB2 (s2 : PS) G2, H_phdr.hlines FI AI d (am_nsec FI AI s) LB N2 LB2 -> 0 <= d <= pa_len FI AI t_0 - pa_cur FI AI t_0 -> am_nsec FI AI s2 = N2 ->
             0 <= G2 -> CG_A * (N2 - am_nsec FI AI s) + G2 <= HCount.cgG FI AI (pa_hs FI AI t_0) + CG_B * d + CG_SL ->
             H_pent_kit.ebud FI AI (2 * gmax + 5) (pa_len FI AI t_0 - pa_cur FI AI t_0 - d) G2 s2 LB2).
  Definition P2 (s : PS) (LB : BL) (t : pstA FI AI) : Prop :=
    exists N1 LB1 d, pfirst FI AI (am_nsec FI AI s_0) LB_0 N1 LB1 /\ H_phdr.hlines FI AI d N1 LB1 (am_nsec FI AI s) LB
      /\ 0 <= d /\ d + (pa_len FI AI t - pa_cur FI AI t) <= pa_len FI AI t_0 - pa_cur FI AI t_0 /\ 0 <= pa_len FI AI t - pa_cur FI AI t
      /\ 5 * (am_nsec FI AI s - 1) <= 5 * am_nsec FI AI s_0 - phiH FI AI (pa_hs FI AI t_0) + phiH FI AI (pa_hs FI AI t)
      /\ H_phdr.hsumA FI AI (pa_hs FI AI t) + (pa_len FI AI t - pa_cur FI AI t) <= H_phdr.hsumA FI AI (pa_hs FI AI t_0) + (pa_len FI AI t_0 - pa_cur FI AI t_0)
      /\ (length LB + length (pa_blocks FI AI t_0) <= length LB_0 + length (pa_blocks FI AI t))%nat
      /\ H_pent_kit.ebud FI AI (2 * gmax + 5) (pa_len FI AI t_0 - pa_cur FI AI t_0 - d) (HCount.cgG FI AI (pa_hs FI AI t)) s LB.

  #[using="mws MWL ws WSL"] Lemma pfirst_nsec : forall N (LB : BL) N' (LB' : BL), pfirst FI AI N LB N' LB' -> N <= N' <= N + 1.
  Proof. intros N LB N' LB' H. destruct H as [N LB|N LB k A n Hn|N LB k k' A n Hn]; [lia| |]; pose proof (nsec1_range n); lia. Qed.

  #[using="mws MWL ws GMX WSL"] Lemma QP_core : forall (s : PS) (LB : BL) (t : pstA FI AI) N1 LB1 d,
    pfirst FI AI (am_nsec FI AI s_0) LB_0 N1 LB1 -> H_phdr.hlines FI AI d N1 LB1 (am_nsec FI AI s) LB ->
    0 <= d -> d + (pa_len FI AI t - pa_cur FI AI t) <= pa_len FI AI t_0 - pa_cur FI AI t_0 -> 0 <= pa_len FI AI t - pa_cur FI AI t ->
    5 * (am_nsec FI AI s - 1) <= 5 * am_nsec FI AI s_0 - phiH FI AI (pa_hs FI AI t_0) + phiH FI AI (pa_hs FI AI t) ->
    H_phdr.hsumA FI AI (pa_hs FI AI t) + (pa_len FI AI t - pa_cur FI AI t) <= H_phdr.hsumA FI AI (pa_hs FI AI t_0) + (pa_len FI AI t_0 - pa_cur FI AI t_0) ->
    (length LB + length (pa_blocks FI AI t_0) <= length LB_0 + length (pa_blocks FI AI t))%nat -> QP s LB t.
  Proof.
    intros s LB t N1 LB1 d PF HL D0 DC LC TG7 TG6 CNT. unfold QP.
    split; [| split; [lia| exact CNT]].
    exists N1, LB1, (am_nsec FI AI s), LB, d, 0, 0.
    split; [exact PF|]. split; [exact HL|]. split; [apply H_pent_kit.ess_nil|]. split; [lia|]. split; [exact D0|]. split; [lia|]. split; [lia| lia].
  Qed.
  #[using="mws MWL ws GMX WSL"] Lemma QP_of_P2 : forall (s : PS) (LB : BL) (t : pstA FI AI), P2 s LB t -> QP s LB t.
  Proof. intros s LB t (N1 & LB1 & d & PF & HL & D0 & DC & LC & TG7 & TG6 & CNT & _). exact (QP_core s LB t N1 LB1 d PF HL D0 DC LC TG7 TG6 CNT). Qed.

  #[using="mws MWL ws GMX WSL"] Lemma QP_of_P1 : forall (s : PS) (LB : BL) (t : pstA FI AI), P1 s LB t -> QP s LB t.
  Proof.
    intros s LB t (PF & HS & CNT & LEN & CR & _). pose proof (pfirst_nsec _ _ _ _ PF) as NS.
    apply (QP_core s LB t (am_nsec FI AI s) LB 0 PF (H_phdr.hls_nil FI AI _ _)); [lia| rewrite LEN; lia| lia| rewrite HS; lia| rewrite HS, LEN; lia| exact CNT].
  Qed.

  #[using="Type"] Lemma mownA_sub : forall m (LB LB' : BL) A cap ok bs, mownA FI AI m LB A cap ok bs -> bsub FI AI LB LB' -> mownA FI AI m LB' A cap ok bs.
  Proof. intros m LB LB' A cap [k|] bs H SUB; cbn [mownA] in *; [destruct H as [H1 H2]; split; [exact (SUB _ H1)| exact H2]| exact H]. Qed.
  #[using="Type"] Lemma p_msg_sub : forall m (LB LB' : BL) A len cap okm bs, p_msg FI AI m LB P A len cap okm bs -> bsub FI AI LB LB' -> p_msg FI AI m LB' P A len cap okm bs.
  Proof. intros m LB LB' A len cap okm bs (H1 & H2 & H3) SUB. split; [exact H1|]. split; [exact (mownA_sub m LB LB' A cap okm bs H2 SUB)| exact H3]. Qed.
  #[using="Type"] Lemma p_smsg_sub : forall m (LB LB' : BL) SA slen scap sok sbs, p_smsgWA FI AI m LB P SA slen scap sok sbs -> bsub FI AI LB LB' -> p_smsgWA FI AI m LB' P SA slen scap sok sbs.
  Proof. intros m LB LB' SA slen scap sok sbs (H1 & H2 & H3) SUB. split; [exact H1|]. split; [exact (mownA_sub m LB LB' SA scap sok sbs H2 SUB)| exact H3]. Qed.

  Definition t_req (t : pstA FI AI) (cur meth err pos : Z) (uc : list cell) (maj min ub : Z) (UB : BL) : pstA FI AI :=
    mkPSA FI AI cur (pa_A FI AI t) (pa_len FI AI t) (pa_cap FI AI t) (pa_okm FI AI t) (pa_bs FI AI t) meth uc (pa_rm FI AI t) (pa_sc FI AI t)
          (pa_SA FI AI t) (pa_slen FI AI t) (pa_scap FI AI t) (pa_sok FI AI t) (pa_sbs FI AI t) (pa_isreq FI AI t) maj min
          (pa_ns FI AI t) (pa_hs FI AI t) (pa_X FI AI t) (pa_ebw FI AI t) (pa_elw FI AI t) err (pa_hack FI AI t) pos (pa_entp FI AI t)
          (pa_clen FI AI t) (pa_csz FI AI t) (pa_esp FI AI t) ub UB.

  Definition WPR : list ivl := [(P + 4, P + 8); (P + 8, P + 224); (P + 276, P + 284); (P + 432, P + 444); (P + 448, P + 452); (P + 488, P + 496); (ERRNO_A, ERRNO_A + 4)]%Z.
  #[using="mws MWL ws WSL"] Lemma WPR_ok : Forall wpok WPR.
  Proof.
    unfold WPR, wpok, H_pparse_seg.inP, H_pparse_seg.inER. repeat (constructor; [left; cbn [fst snd]; lia|]).
    constructor; [right; cbn [fst snd]; lia| constructor].
  Qed.

  Definition pa_rest (t : pstA FI AI) : BL := hl_blocks FI AI (pa_ns FI AI t) (pa_hs FI AI t) ++ okbA FI AI (pa_sok FI AI t) (pa_SA FI AI t) (pa_scap FI AI t).
  #[using="Type"] Lemma pa_rest_sub : forall t, bsub FI AI (pa_rest t) (pa_blocks FI AI t).
  Proof.
    intros t b Hb. unfold pa_rest in Hb. unfold pa_blocks. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right].
    apply in_or_app. right. apply in_or_app. left. exact Hb.
  Qed.
  #[using="Type"] Lemma pa_rest_idj : forall t (kA : K), pa_okm FI AI t = Some kA -> NoDup (map blk_id (pa_blocks FI AI t ++ LBK)) ->
    idj [(kA, pa_A FI AI t, pa_cap FI AI t + 1)] (pa_rest t) /\ idj [(kA, pa_A FI AI t, pa_cap FI AI t + 1)] LBK.
  Proof.
    intros t kA OKM ND. unfold pa_blocks in ND. rewrite OKM in ND. cbn [okbA] in ND. unfold pa_rest.
    apply nd_app in ND. destruct ND as (ND1 & I1 & _). apply nd_app in ND1. destruct ND1 as (_ & I2 & ND2).
    apply (nd_app [(kA, pa_A FI AI t, pa_cap FI AI t + 1)]) in ND2. destruct ND2 as (_ & I3 & _).
    split.
    - apply idj_app_r. split; [apply idj_sym; apply idj_app_r in I2; exact (proj1 I2)| apply idj_app_r in I3; exact (proj1 I3)].
    - apply idj_app_l in I1. destruct I1 as [_ I1]. apply (idj_app_l [(kA, pa_A FI AI t, pa_cap FI AI t + 1)]) in I1. exact (proj1 I1).
  Qed.

  #[using="POK mws MWL ws WSL"] Lemma pp_req : forall OB (LB LB' : BL) m m' (t : pstA FI AI) cur' meth' err' pos' uc' maj' min' ub' UB',
    ekeep WPR OB m m' -> p_parserA FI AI m LB P t -> bsub FI AI (pa_rest t) OB -> bsub FI AI LB LB' ->
    p_scan m' P cur' -> p_msg FI AI m' LB' P (pa_A FI AI t) (pa_len FI AI t) (pa_cap FI AI t) (pa_okm FI AI t) (pa_bs FI AI t) -> 0 <= cur' <= pa_len FI AI t ->
    rw_cells asegs m' (P + 4) [C4 (wz meth')] -> 0 <= meth' <= 12 -> p_uri m' P uc' ->
    rw_cells asegs m' (P + 276) [C4 (wz maj')] -> rw_cells asegs m' (P + 280) [C4 (wz min')] -> - 2^31 <= maj' < 2^31 -> - 2^31 <= min' < 2^31 ->
    rw_cells asegs m' (P + 440) [C4 (wz err')] -> 0 <= err' < 2^31 -> rw_cells asegs m' (P + 448) [C4 (wz pos')] -> 0 <= pos' <= 4 ->
    p_url m' P ub' -> ubo FI AI ub' UB' ->
    p_parserA FI AI m' LB' P (t_req t cur' meth' err' pos' uc' maj' min' ub' UB').
  Proof.
    intros OB LB LB' m m' t cur' meth' err' pos' uc' maj' min' ub' UB' EK PP SUB LSUB PSC' PMSG' CUR' MC' MR' PURI' MJ' MN' MJR MNR EC' ER' PC' PR' PURL' UBO'.
    destruct PP as (_ & _ & _ & PMETH & _ & PRS & PSM & PVER & PHL & PENT & PCTL & _ & _).
    unfold pa_rest in SUB.
    unfold p_parserA, t_req. cbn [pa_cur pa_A pa_len pa_cap pa_okm pa_bs pa_meth pa_uc pa_rm pa_sc pa_SA pa_slen pa_scap pa_sok pa_sbs pa_isreq pa_maj pa_min
      pa_ns pa_hs pa_X pa_ebw pa_elw pa_err pa_hack pa_pos pa_entp pa_clen pa_csz pa_esp pa_ub pa_UB].
    Ltac djr := let PLOx := fresh "PLOx" in pose proof POK as (_ & _ & _ & _ & PLOx & _); unfold WPR; cbn [disjoint_from fst snd]; repeat split; lia.
    split; [exact PSC'|]. split; [exact PMSG'|]. split; [exact CUR'|].
    split. { destruct PMETH as [C _]. split; [| exact MR']. split_chunk C 1%nat C0 C4x.
             apply (ek_pcell _ _ _ _ _ _ EK) in C0; [| lia| simpl_sizes; lia| simpl_sizes; djr]. join_chunks C0 MC' R. exact R. }
    split; [exact PURI'|].
    split; [exact (ek_rs _ _ m m' _ _ EK ltac:(djr) PRS)|].
    split. { apply (p_smsg_sub m' LB LB' _ _ _ _ _); [| exact LSUB]. apply (ek_smsg _ _ LB m m' _ _ _ _ _ EK ltac:(djr)); [| exact PSM].
             intros b Hb; apply SUB; apply in_or_app; right; exact Hb. }
    split. { destruct PVER as [(pad & C) (IR & _ & _)]. split; [| exact (conj IR (conj MJR MNR))]. exists pad.
             split_chunk C 2%nat C01 C23. split_chunk C23 2%nat C2x C3.
             apply (ek_pcell _ _ _ _ _ _ EK) in C01; [| lia| simpl_sizes; lia| simpl_sizes; djr].
             apply (ek_pcell _ _ _ _ _ _ EK) in C3; [| simpl_sizes; lia| simpl_sizes; lia| simpl_sizes; djr].
             join_chunks MJ' MN' R1. join_chunks R1 C3 R2. join_chunks C01 R2 R3. exact R3. }
    split; [apply (ek_hlist _ _ m m' _ _ _ EK PHL); [intros b Hb; apply SUB; apply in_or_app; left; exact Hb| djr]|].
    split; [exact (ek_ent _ _ m m' _ _ EK ltac:(djr) PENT)|].
    split. { destruct PCTL as (C & _ & R2 & _ & R4 & R5 & R6 & R7).
             destruct (pctl_split m _ _ _ _ _ _ _ C) as (_ & C444 & _ & C452 & C456 & C460 & C464 & C472).
             split; [| repeat (split; [assumption|]); assumption].
             apply pctl_join; [exact EC'| | exact PC'| | | | |];
               (eapply (ek_pcell _ _ _ _ _ _ EK); [| | | eassumption]; [lia| simpl_sizes; lia| simpl_sizes; djr]). }
    split; [exact PURL'| exact UBO'].
  Qed.

  Definition WPB : list ivl := [(P + 8, P + 8 + 216); (ERRNO_A, ERRNO_A + 4); (P + 432, P + 440); (P + 448, P + 452)]%Z.
  Definition WPC : list ivl := [(P + 4, P + 8); (P + 8, P + 8 + 216); (ERRNO_A, ERRNO_A + 4); (P + 276, P + 280); (P + 280, P + 284); (P + 432, P + 440); (P + 440, P + 444); (P + 448, P + 452)]%Z.
  #[using="mws MWL ws WSL"] Lemma WPB_ok : Forall wpok WPB.
  Proof. unfold WPB, wpok, H_pparse_seg.inP, H_pparse_seg.inER. repeat (constructor; [first [left; cbn [fst snd]; lia| right; cbn [fst snd]; lia]|]). constructor. Qed.
  #[using="mws MWL ws WSL"] Lemma WPC_ok : Forall wpok WPC.
  Proof. unfold WPC, wpok, H_pparse_seg.inP, H_pparse_seg.inER. repeat (constructor; [first [left; cbn [fst snd]; lia| right; cbn [fst snd]; lia]|]). constructor. Qed.
  #[using="mws MWL ws WSL"] Lemma WPB_in : Forall (fun iv : ivl => inside (pparse_WA P) (fst iv) (snd iv - fst iv)) WPB.
  Proof. unfold WPB, pparse_WA. repeat (constructor; [cbn [inside fst snd]; first [left; lia| right; left; lia]|]). constructor. Qed.
  #[using="mws MWL ws WSL"] Lemma WPC_in : Forall (fun iv : ivl => inside (pparse_WA P) (fst iv) (snd iv - fst iv)) WPC.
  Proof. unfold WPC, pparse_WA. repeat (constructor; [cbn [inside fst snd]; first [left; lia| right; left; lia]|]). constructor. Qed.
  #[using="mws MWL ws WSL"] Lemma rWB_cls : Forall (fcls WPB []) (H_pparse_reql.rWB P).
  Proof.
    unfold H_pparse_reql.rWB, fcls, WPB.
    constructor; [cbn [fst snd inside]; split; [lia| left; left; lia]|].
    constructor; [cbn [fst snd inside]; split; [lia| left; right; left; lia]|].
    constructor; [cbn [fst snd inside]; split; [lia| left; right; right; left; lia]|].
    constructor; [cbn [fst snd inside]; split; [lia| left; right; right; right; left; lia]| constructor].
  Qed.
  #[using="mws MWL ws WSL"] Lemma rWC_cls : forall (kA : K) A cap, 0 <= cap -> Forall (fcls WPC [(kA, A, cap + 1)]) (H_pparse_reql.rWC P A cap).
  Proof.
    intros kA A cap Hc. unfold H_pparse_reql.rWC, fcls, WPC.
    constructor; [cbn [fst snd inside]; split; [lia| left; left; lia]|].
    constructor; [cbn [fst snd inside]; split; [lia| left; right; left; lia]|].
    constructor; [cbn [fst snd inside]; split; [lia| left; right; right; left; lia]|].
    constructor; [cbn [fst snd inside]; split; [lia| left; right; right; right; left; lia]|].
    constructor; [cbn [fst snd inside]; split; [lia| left; right; right; right; right; left; lia]|].
    constructor; [cbn [fst snd inside]; split; [lia| left; right; right; right; right; right; left; lia]|].
    constructor; [cbn [fst snd inside]; split; [lia| left; right; right; right; right; right; right; left; lia]|].
    constructor; [cbn [fst snd inside]; split; [lia| left; right; right; right; right; right; right; right; left; lia]|].
    constructor; [| constructor]. cbn [fst snd]. split; [lia|]. right; right. exists (kA, A, cap + 1). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia.
  Qed.
  #[using="Type"] Lemma WPR_of_B : forall a n, disjoint_from WPR a n -> disjoint_from WPB a n.
  Proof. intros a n. unfold WPB, WPR. cbn [disjoint_from fst snd]. clear. intros. repeat split; try exact I; lia. Qed.
  #[using="Type"] Lemma WPR_of_C : forall a n, disjoint_from WPR a n -> disjoint_from WPC a n.
  Proof. intros a n. unfold WPC, WPR. cbn [disjoint_from fst snd]. clear. intros. repeat split; try exact I; lia. Qed.
  #[using="Type"] Lemma WPR_of_A : forall a n, disjoint_from WPR a n -> disjoint_from WPA a n.
  Proof. intros a n. unfold WPA, WPR. cbn [disjoint_from fst snd]. clear. intros. repeat split; try exact I; lia. Qed.
  #[using="Type"] Lemma WPR_of_nil : forall a n, disjoint_from WPR a n -> disjoint_from [] a n.
  Proof. intros a n _. exact I. Qed.

  #[using="mws MWL ws WSL"] Lemma ublk_facts : forall (s' : PS) (LB' : BL) m (k : K) U l (ustr : list byte),
    RHEAP_A FI AI s' LB' m -> In (k, U, l + 1) LB' -> 0 <= l -> rw_cells asegs m U [CB (Z.to_nat (l + 1)) (ustr ++ [Z_to_bv 8 0])] -> Z.of_nat (length ustr) = l ->
    exists slack : list byte,
      (- (U + l + 1)) mod 8 <= Z.of_nat (length slack) /\ 0x609000 <= U /\ U + l + 1 + Z.of_nat (length slack) <= alloc_ceiling
      /\ (U + l + 1 + Z.of_nat (length slack) <= FSB FI \/ FSB FI + A0_FS_SIZE <= U)
      /\ (U + l + 1 + Z.of_nat (length slack) <= 0x7fff7000 \/ 0x10007fff8000 <= U)
      /\ shw m U (l + 1) /\ bytes_at asegs m U (ustr ++ Z_to_bv 8 0 :: slack) /\ 0 < U < 2^64.
  Proof.
    intros s' LB' m k U l ustr HR HIN L0 UC UL.
    destruct (am_block_range FI AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & R5 & R6 & R7). cbn [blk_addr blk_size fst snd] in *.
    pose proof (rw_cells_bytes_at asegs _ _ _ UC) as UBY. cbn [cells_bytes cbytes] in UBY. rewrite app_nil_r in UBY.
    destruct (H2KitA.block_slackA FI AI s' LB' m (k, U, l + 1) (ustr ++ [Z_to_bv 8 0]) HR HIN UBY ltac:(rewrite length_app; cbn [length blk_size snd]; lia)) as (sl & kE & SLB & SL7 & SLAL).
    cbn [blk_addr blk_size fst snd] in SLB, SLAL.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    exists sl.
    split; [clear - SL7 SLAL; Z.div_mod_to_equations; lia|]. split; [exact R5|]. split; [clear - R4 SL7; lia|].
    split; [destruct R7 as [R7|R7]; [left; clear - R7 SLAL SL7 B4; Z.div_mod_to_equations; lia| right; exact R7]|].
    split; [destruct R6 as [R6|R6]; [left; clear - R6 SL7; lia| right; exact R6]|].
    split; [apply (block_shw FI AI s' LB' m (k, U, l + 1) U (l + 1) HR HIN); cbn [blk_addr blk_size fst snd]; lia|].
    split; [| clear - R1 R4 ACR L0; lia].
    replace (ustr ++ Z_to_bv 8 0 :: sl) with ((ustr ++ [Z_to_bv 8 0]) ++ sl) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact UBY|]. rewrite length_app. cbn [length]. replace (U + Z.of_nat (length ustr + 1)) with (U + (l + 1)) by lia. exact SLB.
  Qed.

  #[using="Type"] Lemma pa_blocks_req : forall (t : pstA FI AI) cur meth err pos uc maj min ub (UB : BL), pa_UB FI AI t = [] ->
    pa_blocks FI AI (t_req t cur meth err pos uc maj min ub UB) = pa_blocks FI AI t ++ UB.
  Proof.
    intros t cur meth err pos uc maj min ub UB E. unfold pa_blocks, t_req. cbn [pa_ns pa_hs pa_okm pa_A pa_cap pa_sok pa_SA pa_scap pa_UB]. rewrite E, app_nil_r, <- !app_assoc. reflexivity.
  Qed.
  #[using="Type"] Lemma nd_insert : forall (X Y : BL) (b : BLK), NoDup (map blk_id (X ++ Y)) -> idj [b] (X ++ Y) -> NoDup (map blk_id ((X ++ [b]) ++ Y)).
  Proof.
    intros X Y b ND IB. apply nd_app in ND. destruct ND as (NX & IXY & NY). apply idj_app_r in IB. destruct IB as [IBX IBY].
    apply nd_app. split; [apply nd_app; split; [exact NX| split; [apply idj_sym; exact IBX|]]| split; [apply idj_app_l; split; [exact IXY| exact IBY]| exact NY]].
    apply (proj2 (nd_cons b [])). split; [intros a c _ []| constructor].
  Qed.

  #[using="ASL AMS POK RF0 MWL s_0 LB_0 HR0 KSUB0 WSL"] Lemma sf_chain : forall (s : PS) (LB : BL) m m' (t : pstA FI AI) rs a, QX s LB m t -> munch [(SF, SF + 16)]%Z m m' -> wmono asegs m m' ->
    fpchain m (am_stack_top FI AI) q a rs -> fpchain m' (am_stack_top FI AI) q a rs.
  Proof.
    intros s LB m m' t rs a QXF MU WM CH. pose proof QXF as (HR & PP & _ & SUB & ND & _).
    assert (OSUB : bsub FI AI (pa_blocks FI AI t) LB) by (intros b Hb; apply SUB; apply in_or_app; left; exact Hb).
    assert (KSUB : bsub FI AI LBK LB) by (intros b Hb; apply SUB; apply in_or_app; right; exact Hb).
    assert (CLS : Forall (ecls [] []) [(SF, SF + 16)]%Z).
    { constructor; [| constructor]. unfold ecls. cbn [fst snd]. split; [lia|]. right; right; left. lia. }
    destruct (ekeep_munch _ [] [] (pa_blocks FI AI t) s LB m m' MU WM CLS (Forall_nil _) (Forall_nil _) HR
                (fun b Hb => False_ind _ Hb) OSUB KSUB (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha)) as [EK HR'].
    destruct EK as (_ & _ & _ & _ & _ & _ & K7 & _). exact (K7 _ _ CH).
  Qed.

  Definition E2 (t : pstA FI AI) : Prop :=
    pa_pos FI AI t = 2 /\ (exists kA : K, pa_okm FI AI t = Some kA) /\ pa_meth FI AI t <= 11 /\ pa_entp FI AI t = 1
    /\ pa_X FI AI t + 2 * (pa_len FI AI t - pa_cur FI AI t) <= 2^27 + 64.
  Definition CONT2 : Prop :=
    forall q' (s : PS) (LB : BL) m (t : pstA FI AI) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31,
      QX s LB m t -> P1 s LB t -> pinvQ q' m -> fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras -> E2 t ->
      AJ FI AI J POST (loopstQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m) s LB.

  #[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_3 SET_SHADOW_F5 POK RF0 FCO MWL MID HR0 KSUB0 QTOP GMX WSL GLR PBUD"] Lemma reqlJ : forall q' m (t : pstA FI AI) (kA : K) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    CONT2 -> QX s_0 LB_0 m t -> P1 s_0 LB_0 t -> pinvQ q' m -> fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras ->
    pa_okm FI AI t = Some kA -> pa_pos FI AI t = 0 -> pp_sideA FI AI t ->
    AJ FI AI J POST (reqlstQ q' x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m) s_0 LB_0.
  Proof.
    intros q' m t kA x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 K2 QXF P1F INV CH OKM POS0 SIDE.
    apply aj_cps. apply (unpoisonQ q' x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m _ INV).
    intros m1 INV1 MU1 WM1.
    pose proof (sf_move s_0 LB_0 m m1 t QXF MU1 WM1) as QX1.
    pose proof (sf_chain s_0 LB_0 m m1 t _ _ QXF MU1 WM1 CH) as CH1.
    clear QXF CH INV MU1 WM1 m.
    pose proof QX1 as (HR1 & PP1 & ISR1 & SUB1 & ND1 & STAT1 & SHP1 & SHZ1 & SHR1 & _).
    pose proof PP1 as (PSC & PMSG & CUR & PMETH & PURI & _ & _ & PVER & _ & _ & PCTL & PURL & UBO).
    rewrite OKM in PMSG.
    destruct (p_msg_facts FI AI m1 LB_0 P _ _ _ (Some kA) _ s_0 HR1 PMSG) as (_ & _ & LBS0 & _).
    destruct (pstat_of_pp m1 STAT1) as (PSR & PSU & SHFV & SHSEP & SHF1 & SHF2 & SHE).
    destruct (QX_clow s_0 LB_0 m1 t QX1) as (ev1 & CLOW1).
    destruct (pctx_of s_0 LB_0 m1 _ _ _ kA _ _ ev1 HR1 PSC PMSG SHP1 SHSEP SHF1 SHF2 SHZ1 SHR1 CLOW1 SHE) as (CTX1 & TOK & KIN & NUL & CAPB).
    destruct PCTL as (CTLC & ER & CR2 & CR3 & CR4 & CR5 & CR6 & CR7).
    destruct (pctl_split m1 _ _ _ _ _ _ _ CTLC) as (C440 & C444 & C448 & C452 & C456 & C460 & C464 & C472).
    destruct PMETH as [MC MR]. split_chunk MC 1%nat MC0 MC4.
    pose proof (am_fsenv FI AI _ _ _ HR1) as FE1.
    assert (OSUB : bsub FI AI (pa_blocks FI AI t) LB_0) by (intros b Hb; apply SUB1; apply in_or_app; left; exact Hb).
    assert (KSUB : bsub FI AI LBK LB_0) by (intros b Hb; apply SUB1; apply in_or_app; right; exact Hb).
    destruct PVER as [(pad & VC) (IR & MJR & MNR)]. split_chunk VC 2%nat V01 V23. split_chunk V23 1%nat V2 V3x. split_chunk V3x 1%nat V3 V4.
    destruct PURI as [UC UCS]. destruct PURL as [UBC UBR].
    eapply (segAQ q' (pa_A FI AI t) (pa_len FI AI t) (pa_cap FI AI t) (pa_cur FI AI t) (pa_meth FI AI t) (pa_err FI AI t) (pa_bs FI AI t));
      [exact INV1| exact CTX1| exact TOK| exact PSR| exact FE1| exact CUR| exact C440| exact MC4| | |].
    -
      intros m2 r cur' e' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RR RN CR' EE INV2 CTX2 EC2 MC2 MV. apply evt_done.
      pose proof CTX2 as (_ & _ & _ & SHP2 & _).
      destruct (rmove_ek (pa_blocks FI AI t) s_0 LB_0 m1 m2 MV SHP2 HR1 OSUB KSUB) as [EKA HR2].
      assert (EK : ekeep WPR (pa_blocks FI AI t) m1 m2).
      { apply (ekeep_weaken WPA WPR _ m1 m2 EKA). intros a n. unfold WPA, WPR. cbn [disjoint_from fst snd]. clear. intros. repeat split; try exact I; lia. }
      destruct TOK as (TK1 & TK2 & TK3 & _).
      destruct (pctx_back LB_0 m2 _ _ _ cur' _ kA CTX2 KIN TK3 ltac:(unfold LMAX_A; clear - CAPB; lia) NUL) as (PSC2 & PMSG2 & CL2).
      Ltac dja := let PLOx := fresh "PLOx" in pose proof POK as (_ & _ & _ & _ & PLOx & _); unfold WPA; cbn [disjoint_from fst snd]; repeat split; lia.
      Ltac eka EK H := apply (ek_pcell _ _ _ _ _ _ EK) in H; [| clear; lia| simpl_sizes; clear; lia| simpl_sizes; dja].
      assert (PP2 : p_parserA FI AI m2 LB_0 P (t_req t cur' (pa_meth FI AI t) e' (pa_pos FI AI t) (pa_uc FI AI t) (pa_maj FI AI t) (pa_min FI AI t) (pa_ub FI AI t) (pa_UB FI AI t))).
      { eka EKA V2. eka EKA V3. eka EKA C448.
        apply (pp_req (pa_blocks FI AI t) LB_0 LB_0 m1 m2 t); [exact EK| exact PP1| exact (pa_rest_sub t)| intros b Hb; exact Hb| exact PSC2| rewrite OKM; exact PMSG2| clear - CR' CUR; lia
          | exact MC2| exact MR| exact (ek_uri _ _ m1 m2 _ EKA ltac:(dja) (conj UC UCS))| exact V2| exact V3| exact MJR| exact MNR| exact EC2| clear - EE ER; lia| exact C448| exact CR3
          | exact (ek_url _ _ m1 m2 _ EKA ltac:(dja) (conj UBC UBR))| exact UBO]. }
      assert (QX2 : QX s_0 LB_0 m2 (t_req t cur' (pa_meth FI AI t) e' (pa_pos FI AI t) (pa_uc FI AI t) (pa_maj FI AI t) (pa_min FI AI t) (pa_ub FI AI t) (pa_UB FI AI t))).
      { eapply (QX_move WPR _ s_0 LB_0 m1 t s_0 LB_0 m2); [exact QX1| exact EK| exact WPR_ok| exact HR2| exact PP2| reflexivity| exact SUB1| exact ND1| exact CL2]. }
      apply (rejoin_exitJ q' r s_0 LB_0 m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ QX2); [| exact INV2| exact RR| exact RN].
      apply QP_of_P1. destruct P1F as (PF & HS & CNT & LEN & CRX & BUD1).
      split; [exact PF|]. split; [exact HS|]. split; [exact CNT|]. split; [exact LEN|]. split; [cbn [t_req pa_cur pa_len]; clear - CRX CR'; lia| exact BUD1].
    -
      intros m2 cur' o l mb ml vb vl y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 CR' O1 L1 OL INV2 CTX2 PSR2 FE2 PL2 EC2 MC2 MV. apply evt_done.
      pose proof CTX2 as (_ & _ & TXT2 & SHP2 & _).
      destruct (rmove_ek (pa_blocks FI AI t) s_0 LB_0 m1 m2 MV SHP2 HR1 OSUB KSUB) as [EKA HR2].
      pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
      pose proof INV2 as (ST2 & _ & MI2 & AE2 & (QB & QAL) & VR2). destruct VR2 as (_ & _ & _ & _ & _ & _ & _ & _ & (stc & RF2 & LIVE2)).
      pose proof TOK as (TK1 & TK2 & TK3 & _).
      destruct P1F as (PF & HS & CNT & LEN & CRX & BUD1). destruct SIDE as (_ & _ & UB0 & UBN & _ & _ & _ & _ & LEN26 & _).
      pose proof (rw_cells_bytes_at asegs _ _ _ TXT2) as TBY. cbn [cells_bytes cbytes] in TBY. rewrite app_nil_r in TBY.
      set (src := firstn (Z.to_nat l) (skipn (Z.to_nat o) (pa_bs FI AI t))).
      assert (SRCL : Z.of_nat (length src) = l) by (unfold src; rewrite length_firstn, length_skipn; clear - LBS0 TK3 CUR O1 L1 OL; lia).
      assert (SRCB : bytes_at asegs m2 (pa_A FI AI t + o) src).
      { pose proof (bytes_skipnQ m2 _ _ o TBY ltac:(clear - LBS0 TK3 CUR O1 L1 OL; lia)) as B1.
        rewrite <- (firstn_skipn (Z.to_nat l) (skipn (Z.to_nat o) (pa_bs FI AI t))) in B1. apply bytes_at_app in B1. exact (proj1 B1). }
      unfold H_pparse_reql.strcallstQ, H_pparse_seg.pregsQ.
      eapply (aj_bind FI AI J).
      { eapply (H_str_alloc.str_alloc_spec_A IC FI AI J AC ASL) with (lo := lo) (st := stc) (SRC := pa_A FI AI t + o) (n := l) (src := src) (bsrc := (kA, pa_A FI AI t, pa_cap FI AI t + 1));
          [exact HR2| exact RF2| exact AE2| exact ST2| exact CLO| unfold A0_RT_STACK; clear - LO QB; lia| exact QAL| clear - QTOP QB; lia| exact MI2| exact SRCB| exact SRCL
           | clear - LEN26 CUR O1 L1 OL; lia
           | apply (am_budget_le_at FI AI s_0 LB_0 _ _ (proj1 PBUD)); clear - LEN CRX CUR O1 L1 OL; lia
           | exact KIN| cbn [blk_addr fst snd]; clear - CUR O1; lia| cbn [blk_addr blk_size fst snd]; clear - TK3 OL; lia| reflexivity| reflexivity]. }
      intros sa LBa msa PO. unfold str_alloc_post_A in PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & k & U & -> & (MI3 & ST3 & AE3 & RF3 & AP) & -> & HR3 & UCH & NS3).
      rewrite ret_pc_even by lia.
      assert (INV3 : pinvQS qshadowU q' m3) by (apply (pinv_stepA qshadowU eq_refl [] LB_0 q' m2 m3 stc INV2 (apx_of_apres FI AI [] LB_0 q' m2 m3 AP) (Forall_nil _) LIVE2 RF3 ST3 MI3 AE3)).
      pose proof (apres_ek s_0 LB_0 LB_0 (pa_blocks FI AI t) q' stc m2 m3 AP RF2 LIVE2 QB HR2 OSUB OSUB KSUB KSUB SHP2) as EK23.
      assert (KIN3 : In (kA, pa_A FI AI t, pa_cap FI AI t + 1) ((k, U, l + 1) :: LB_0)) by (right; exact KIN).
      assert (OKIN : In (kA, pa_A FI AI t, pa_cap FI AI t + 1) (pa_blocks FI AI t)) by (unfold pa_blocks; rewrite OKM; cbn [okbA]; apply in_or_app; right; left; reflexivity).
      pose proof (pctx_ek [] _ sa _ _ _ _ cur' _ kA m2 m3 CTX2 EK23 (Forall_nil _) I I I OKIN HR3 KIN3 ltac:(clear - TK3; lia)) as CTX3.
      pose proof (ploc_stepA LB_0 q' _ _ _ _ _ _ m2 m3 PL2 AP) as PL3.

      destruct (pctx_back LB_0 m2 _ _ _ cur' _ kA CTX2 KIN TK3 ltac:(unfold LMAX_A; clear - CAPB; lia) NUL) as (_ & _ & CL2).
      pose proof (ek_ppstat _ _ m1 m2 mws EKA WPA_ok MWL STAT1 CL2) as STAT2.
      destruct (pctx_back _ m3 _ _ _ cur' _ kA CTX3 KIN3 TK3 ltac:(unfold LMAX_A; clear - CAPB; lia) NUL) as (_ & _ & CL3).
      pose proof (ek_ppstat _ _ m2 m3 mws EK23 (Forall_nil _) MWL STAT2 CL3) as STAT3.
      destruct (pstat_of_pp m3 STAT3) as (PSR3 & PSU3 & SHFV3 & _).
      pose proof (am_fsenv FI AI _ _ _ HR3) as FE3.

      Ltac ek0 EK H := apply (ek_pcell _ _ _ _ _ _ EK) in H; [| clear; lia| simpl_sizes; clear; lia| exact I].
      eka EKA UBC. ek0 EK23 UBC. eka EKA C448. ek0 EK23 C448.
      destruct (rw_cells_forget asegs m1 _ _ UC) as (junk & UJ). rewrite UCS in UJ. eka EKA UJ. ek0 EK23 UJ.
      destruct (ublk_facts sa _ m3 k U l src HR3 (or_introl eq_refl) ltac:(clear - L1; lia) UCH SRCL) as (slack & U1 & U2 & U3 & U4 & U5 & SHU & UBY & UR).
      apply aj_cps.
      eapply (segBQ q' (pa_A FI AI t) (pa_len FI AI t) (pa_cap FI AI t) cur' U l (pa_pos FI AI t) (pa_bs FI AI t) src slack junk mb ml vb vl (wz (pa_A FI AI t + o)) (wz (pa_ub FI AI t)));
        [exact INV3| exact CTX3| exact TOK| exact PSU3| exact FE3| reflexivity| exact PL3| exact UBC| exact UJ| exact C448| exact SRCL| clear - L1 LEN26 OL CUR O1; lia
         | exact U1| exact U2| exact U3| exact U4| exact U5| exact SHU| exact UBY|].
      intros m4 r pos' junk' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 RP INV4 CTX4 UBC4 UC4 PC4 MV4. apply evt_done.
      pose proof CTX4 as (_ & _ & _ & SHP4 & _).
      assert (OSUB3 : bsub FI AI (pa_blocks FI AI t) ((k, U, l + 1) :: LB_0)) by (intros b Hb; right; exact (OSUB b Hb)).
      assert (KSUB3 : bsub FI AI LBK ((k, U, l + 1) :: LB_0)) by (intros b Hb; right; exact (KSUB b Hb)).
      destruct (wmove_ek _ WPB [] (pa_blocks FI AI t) sa _ m3 m4 MV4 SHP4 rWB_cls WPB_ok WPB_in HR3 (fun b Hb => False_ind _ Hb) OSUB3 KSUB3
                  (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha)) as [EK34 HR4].
      pose proof (ekeep_trans WPR _ m1 m2 m4 (ekeep_weaken _ WPR _ m1 m2 EKA WPR_of_A)
                    (ekeep_trans WPR _ m2 m3 m4 (ekeep_weaken _ WPR _ m2 m3 EK23 WPR_of_nil) (ekeep_weaken _ WPR _ m3 m4 EK34 WPR_of_B))) as EK14.
      destruct (pctx_back _ m4 _ _ _ cur' _ kA CTX4 KIN3 TK3 ltac:(unfold LMAX_A; clear - CAPB; lia) NUL) as (PSC4 & PMSG4 & CL4).
      Ltac djb := let PLOx := fresh "PLOx" in pose proof POK as (_ & _ & _ & _ & PLOx & _); unfold WPB; cbn [disjoint_from fst snd]; repeat split; lia.
      Ltac ekb EK H := apply (ek_pcell _ _ _ _ _ _ EK) in H; [| clear; lia| simpl_sizes; clear; lia| simpl_sizes; djb].
      eka EKA V2. ek0 EK23 V2. ekb EK34 V2. eka EKA V3. ek0 EK23 V3. ekb EK34 V3. ek0 EK23 EC2. ekb EK34 EC2. ek0 EK23 MC2. ekb EK34 MC2.
      set (t4 := t_req t cur' 12 (pa_err FI AI t) pos' [CB 216 junk'] (pa_maj FI AI t) (pa_min FI AI t) U [(k, U, l + 1)]).
      assert (PP4 : p_parserA FI AI m4 ((k, U, l + 1) :: LB_0) P t4).
      { apply (pp_req (pa_blocks FI AI t) LB_0 _ m1 m4 t); [exact EK14| exact PP1| exact (pa_rest_sub t)| intros b Hb; right; exact Hb| exact PSC4| rewrite OKM; exact PMSG4| clear - CR' CUR; lia
          | exact MC2| clear; lia| split; [exact UC4| reflexivity]| exact V2| exact V3| exact MJR| exact MNR| exact EC2| exact ER| exact PC4| clear - RP CR3; lia
          | split; [exact UBC4| clear - UR; lia]| cbn [ubo blk_addr fst]; split; [reflexivity| clear - UR; lia]]. }
      assert (QX4 : QX sa ((k, U, l + 1) :: LB_0) m4 t4).
      { eapply (QX_move WPR _ s_0 LB_0 m1 t sa _ m4 t4); [exact QX1| exact EK14| exact WPR_ok| exact HR4| exact PP4| reflexivity| | | exact CL4].
        - unfold t4. rewrite (pa_blocks_req t _ _ _ _ _ _ _ _ _ UBN). intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| right; exact (KSUB b Hb)].
          apply in_app_or in Hb. destruct Hb as [Hb|[<-|[]]]; [right; exact (OSUB b Hb)| left; reflexivity].
        - unfold t4. rewrite (pa_blocks_req t _ _ _ _ _ _ _ _ _ UBN). apply nd_insert; [exact ND1|].
          pose proof (am_blocks_nodup FI AI sa _ m3 HR3) as NDL. apply (nd_cons (k, U, l + 1) LB_0) in NDL. destruct NDL as [NIN _].
          intros a b [<-|[]] Hb. apply (NIN _ b (or_introl eq_refl)). exact (SUB1 b Hb). }
      apply (rejoin_exitJ q' r sa _ m4 t4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ QX4); [| exact INV4| clear - RP; lia| clear - RP; lia].
      apply QP_of_P1. split; [rewrite NS3; apply pf_new; clear - L1 LEN26 OL CUR O1; lia|]. split; [exact HS|].
      split; [unfold t4; rewrite (pa_blocks_req t _ _ _ _ _ _ _ _ _ UBN), length_app; cbn [length]; clear - CNT; lia|].
      split; [exact LEN|]. split; [unfold t4; cbn [t_req pa_cur pa_len]; clear - CRX CR' CUR; lia|].
      rewrite NS3. exact (proj2 PBUD _ _ sa (pf_new FI AI (am_nsec FI AI s_0) LB_0 k U (l + 1) ltac:(clear - L1 LEN26 OL CUR O1; lia)) NS3).
    -
      intros m2 cur' o1 l1 o l o3 l3 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 CR' O1 L1 OL1 OO LL OL3 L3 OC INV2 CTX2 PSR2 FE2 PL2 EC2 MC2 MV. apply evt_done.
      pose proof CTX2 as (_ & _ & TXT2 & SHP2 & _).
      destruct (rmove_ek (pa_blocks FI AI t) s_0 LB_0 m1 m2 MV SHP2 HR1 OSUB KSUB) as [EKA HR2].
      pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
      pose proof INV2 as (ST2 & _ & MI2 & AE2 & (QB & QAL) & VR2). destruct VR2 as (_ & _ & _ & _ & _ & _ & _ & _ & (stc & RF2 & LIVE2)).
      pose proof TOK as (TK1 & TK2 & TK3 & _).
      destruct P1F as (PF & HS & CNT & LEN & CRX & BUD1). destruct SIDE as (_ & ENTP & UB0 & UBN & _ & _ & _ & XB & LEN26 & _).
      pose proof (rw_cells_bytes_at asegs _ _ _ TXT2) as TBY. cbn [cells_bytes cbytes] in TBY. rewrite app_nil_r in TBY.
      set (src := firstn (Z.to_nat l) (skipn (Z.to_nat o) (pa_bs FI AI t))).
      assert (SRCL : Z.of_nat (length src) = l) by (unfold src; rewrite length_firstn, length_skipn; clear - LBS0 TK3 CUR OO LL OL3 L3 OC CR'; lia).
      assert (SRCB : bytes_at asegs m2 (pa_A FI AI t + o) src).
      { pose proof (bytes_skipnQ m2 _ _ o TBY ltac:(clear - LBS0 TK3 CUR OO LL OL3 L3 OC CR'; lia)) as B1.
        rewrite <- (firstn_skipn (Z.to_nat l) (skipn (Z.to_nat o) (pa_bs FI AI t))) in B1. apply bytes_at_app in B1. exact (proj1 B1). }
      unfold H_pparse_reql.strcallstQ, H_pparse_seg.pregsQ.
      eapply (aj_bind FI AI J).
      { eapply (H_str_alloc.str_alloc_spec_A IC FI AI J AC ASL) with (lo := lo) (st := stc) (SRC := pa_A FI AI t + o) (n := l) (src := src) (bsrc := (kA, pa_A FI AI t, pa_cap FI AI t + 1));
          [exact HR2| exact RF2| exact AE2| exact ST2| exact CLO| unfold A0_RT_STACK; clear - LO QB; lia| exact QAL| clear - QTOP QB; lia| exact MI2| exact SRCB| exact SRCL
           | clear - LEN26 CUR OO LL OL3 L3 OC CR'; lia
           | apply (am_budget_le_at FI AI s_0 LB_0 _ _ (proj1 PBUD)); clear - LEN CRX CUR OO LL OL3 L3 OC CR'; lia
           | exact KIN| cbn [blk_addr fst snd]; clear - CUR OO; lia| cbn [blk_addr blk_size fst snd]; clear - TK3 OO LL OL3 L3 OC CR'; lia| reflexivity| reflexivity]. }
      intros sa LBa msa PO. unfold str_alloc_post_A in PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & k & U & -> & (MI3 & ST3 & AE3 & RF3 & AP) & -> & HR3 & UCH & NS3).
      rewrite ret_pc_even by lia.
      assert (INV3 : pinvQS qshadowU q' m3) by (apply (pinv_stepA qshadowU eq_refl [] LB_0 q' m2 m3 stc INV2 (apx_of_apres FI AI [] LB_0 q' m2 m3 AP) (Forall_nil _) LIVE2 RF3 ST3 MI3 AE3)).
      pose proof (apres_ek s_0 LB_0 LB_0 (pa_blocks FI AI t) q' stc m2 m3 AP RF2 LIVE2 QB HR2 OSUB OSUB KSUB KSUB SHP2) as EK23.
      assert (KIN3 : In (kA, pa_A FI AI t, pa_cap FI AI t + 1) ((k, U, l + 1) :: LB_0)) by (right; exact KIN).
      assert (OKIN : In (kA, pa_A FI AI t, pa_cap FI AI t + 1) (pa_blocks FI AI t)) by (unfold pa_blocks; rewrite OKM; cbn [okbA]; apply in_or_app; right; left; reflexivity).
      pose proof (pctx_ek [] _ sa _ _ _ _ cur' _ kA m2 m3 CTX2 EK23 (Forall_nil _) I I I OKIN HR3 KIN3 ltac:(clear - TK3; lia)) as CTX3.
      pose proof (ploc_stepA LB_0 q' _ _ _ _ _ _ m2 m3 PL2 AP) as PL3.

      destruct (pctx_back LB_0 m2 _ _ _ cur' _ kA CTX2 KIN TK3 ltac:(unfold LMAX_A; clear - CAPB; lia) NUL) as (_ & _ & CL2).
      pose proof (ek_ppstat _ _ m1 m2 mws EKA WPA_ok MWL STAT1 CL2) as STAT2.
      destruct (pctx_back _ m3 _ _ _ cur' _ kA CTX3 KIN3 TK3 ltac:(unfold LMAX_A; clear - CAPB; lia) NUL) as (_ & _ & CL3).
      pose proof (ek_ppstat _ _ m2 m3 mws EK23 (Forall_nil _) MWL STAT2 CL3) as STAT3.
      destruct (pstat_of_pp m3 STAT3) as (PSR3 & PSU3 & SHFV3 & _).
      pose proof (am_fsenv FI AI _ _ _ HR3) as FE3.

      eka EKA UBC. ek0 EK23 UBC. eka EKA C448. ek0 EK23 C448. eka EKA V2. ek0 EK23 V2. eka EKA V3. ek0 EK23 V3. ek0 EK23 EC2. ek0 EK23 MC2.
      destruct (rw_cells_forget asegs m1 _ _ UC) as (junk & UJ). rewrite UCS in UJ. eka EKA UJ. ek0 EK23 UJ.
      destruct (ublk_facts sa _ m3 k U l src HR3 (or_introl eq_refl) ltac:(clear - LL; lia) UCH SRCL) as (slack & U1 & U2 & U3 & U4 & U5 & SHU & UBY & UR).

      pose proof CTX3 as (_ & _ & TXT3 & _).
      pose proof (rw_cells_bytes_at asegs _ _ _ TXT3) as TBY3. cbn [cells_bytes cbytes] in TBY3. rewrite app_nil_r in TBY3.
      destruct (H2KitA.block_slackA FI AI sa _ m3 (kA, pa_A FI AI t, pa_cap FI AI t + 1) _ HR3 KIN3 TBY3 ltac:(cbn [blk_size snd]; exact LBS0)) as (sl & kE & SLB & SL7 & SLAL).
      cbn [blk_addr blk_size fst snd] in SLB, SLAL.
      assert (BCR : exists bcr, nth_error (pa_bs FI AI t) (Z.to_nat (o3 + l3)) = Some bcr).
      { destruct (nth_error (pa_bs FI AI t) (Z.to_nat (o3 + l3))) as [bcr|] eqn:E; [exists bcr; reflexivity|]. apply nth_error_None in E. exfalso. clear - E LBS0 TK3 OC CR' OO LL OL3 L3 CUR. lia. }
      destruct BCR as (bcr & BCR).
      apply aj_cps.
      eapply (segCQ q' (pa_A FI AI t) (pa_len FI AI t) (pa_cap FI AI t) cur' U l o1 l1 o3 l3 (pa_meth FI AI t) (pa_pos FI AI t) (pa_bs FI AI t) src slack junk sl
                (wz (pa_A FI AI t + o)) (wz (pa_ub FI AI t)) (wz (pa_err FI AI t)) (wz (pa_maj FI AI t)) (wz (pa_min FI AI t)) bcr);
        [exact INV3| exact CTX3| exact TOK| exact CAPB| exact PSU3| exact PSR3| exact (conj SLB (conj SL7 (ex_intro _ kE SLAL)))| exact FE3| reflexivity| exact SHFV3| exact PL3
         | clear - CUR O1; lia| exact L1| clear - OL1 TK3; lia| clear - CUR OO LL OL3; lia| exact L3| clear - OC CR'; lia| exact BCR
         | exact UBC| exact UJ| exact V2| exact V3| exact EC2| exact MC2| exact C448| exact SRCL| clear - LL LEN26 OL3 L3 OC CR' CUR OO; lia
         | exact U1| exact U2| exact U3| exact U4| exact U5| exact SHU| exact UBY|].
      intros m4 r meth' pos' junk' v1' v2' e' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 RP INV4 CTX4 UBC4 UC4 V2n V3n EC4 MCn PC4 KZ MV4. apply evt_done.
      pose proof CTX4 as (_ & _ & _ & SHP4 & _).
      destruct (pa_rest_idj t kA OKM ND1) as [IDR IDK].
      assert (RSUB : bsub FI AI (pa_rest t) LB_0) by (intros b Hb; exact (OSUB b (pa_rest_sub t b Hb))).
      assert (RSUB3 : bsub FI AI (pa_rest t) ((k, U, l + 1) :: LB_0)) by (intros b Hb; right; exact (RSUB b Hb)).
      assert (KSUB3 : bsub FI AI LBK ((k, U, l + 1) :: LB_0)) by (intros b Hb; right; exact (KSUB b Hb)).
      destruct (wmove_ek _ WPC [(kA, pa_A FI AI t, pa_cap FI AI t + 1)] (pa_rest t) sa _ m3 m4 MV4 SHP4 (rWC_cls kA (pa_A FI AI t) (pa_cap FI AI t) ltac:(clear - TK3; lia)) WPC_ok WPC_in HR3
                  ltac:(intros b [<-|[]]; exact KIN3) RSUB3 KSUB3 IDR IDK) as [EK34 HR4].
      pose proof (ekeep_trans WPR _ m1 m2 m4 (ekeep_weaken _ WPR _ m1 m2 (ekeep_sub _ _ (pa_rest t) m1 m2 EKA (pa_rest_sub t)) WPR_of_A)
                    (ekeep_trans WPR _ m2 m3 m4 (ekeep_weaken _ WPR _ m2 m3 (ekeep_sub _ _ (pa_rest t) m2 m3 EK23 (pa_rest_sub t)) WPR_of_nil) (ekeep_weaken _ WPR _ m3 m4 EK34 WPR_of_C))) as EK14.
      destruct (pctx_back _ m4 _ _ _ cur' _ kA CTX4 KIN3 TK3 ltac:(unfold LMAX_A; clear - CAPB; lia) NUL) as (PSC4 & PMSG4 & CL4).
      apply H_presp_seg.rw_cells_C4_s32vA in V2n. apply H_presp_seg.rw_cells_C4_s32vA in V3n.
      assert (EE : exists err', e' = wz err' /\ 0 <= err' < 2^31).
      { destruct RP as [(_ & _ & _ & [-> |[-> | ->]])|(_ & _ & _ & ->)]; eexists; (split; [reflexivity|]); first [exact ER| clear; lia]. }
      destruct EE as (err' & -> & ER').
      assert (MR' : 0 <= meth' <= 12) by (destruct RP as [(_ & _ & -> & _)|(_ & _ & M11 & _)]; [exact MR| clear - M11; lia]).
      assert (PR' : 0 <= pos' <= 4) by (destruct RP as [(_ & -> & _)|(_ & -> & _)]; [exact CR3| clear; lia]).
      set (t4 := t_req t cur' meth' err' pos' [CB 216 junk'] (P0.H_presp_B.s32v v1') (P0.H_presp_B.s32v v2') U [(k, U, l + 1)]).
      assert (PP4 : p_parserA FI AI m4 ((k, U, l + 1) :: LB_0) P t4).
      { apply (pp_req (pa_rest t) LB_0 _ m1 m4 t); [exact EK14| exact PP1| intros b Hb; exact Hb| intros b Hb; right; exact Hb| exact PSC4| rewrite OKM; exact PMSG4| clear - CR' CUR; lia
          | exact MCn| exact MR'| split; [exact UC4| reflexivity]| exact V2n| exact V3n| apply P0.H_presp_B.s32v_range| apply P0.H_presp_B.s32v_range| exact EC4| exact ER'| exact PC4| exact PR'
          | split; [exact UBC4| clear - UR; lia]| cbn [ubo blk_addr fst]; split; [reflexivity| clear - UR; lia]]. }
      assert (QX4 : QX sa ((k, U, l + 1) :: LB_0) m4 t4).
      { eapply (QX_move WPR _ s_0 LB_0 m1 t sa _ m4 t4); [exact QX1| exact EK14| exact WPR_ok| exact HR4| exact PP4| reflexivity| | | exact CL4].
        - unfold t4. rewrite (pa_blocks_req t _ _ _ _ _ _ _ _ _ UBN). intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| right; exact (KSUB b Hb)].
          apply in_app_or in Hb. destruct Hb as [Hb|[<-|[]]]; [right; exact (OSUB b Hb)| left; reflexivity].
        - unfold t4. rewrite (pa_blocks_req t _ _ _ _ _ _ _ _ _ UBN). apply nd_insert; [exact ND1|].
          pose proof (am_blocks_nodup FI AI sa _ m3 HR3) as NDL. apply (nd_cons (k, U, l + 1) LB_0) in NDL. destruct NDL as [NIN _].
          intros a b [<-|[]] Hb. apply (NIN _ b (or_introl eq_refl)). exact (SUB1 b Hb). }
      assert (P14 : P1 sa ((k, U, l + 1) :: LB_0) t4).
      { split; [rewrite NS3; apply pf_new; clear - LL LEN26 OL3 L3 OC CR' CUR OO; lia|]. split; [exact HS|].
        split; [unfold t4; rewrite (pa_blocks_req t _ _ _ _ _ _ _ _ _ UBN), length_app; cbn [length]; clear - CNT; lia|].
        split; [exact LEN|]. split; [unfold t4; cbn [t_req pa_cur pa_len]; clear - CRX CR' CUR; lia|].
        rewrite NS3. exact (proj2 PBUD _ _ sa (pf_new FI AI (am_nsec FI AI s_0) LB_0 k U (l + 1) ltac:(clear - LL LEN26 OL3 L3 OC CR' CUR OO; lia)) NS3). }
      assert (RR : 0 <= r <= 5) by (clear - RP; lia).
      apply aj_cps. apply (rejoinQ q' r z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m4 _ INV4 RR).
      +
        intros m5 R4 INV5 MU5 WM5. apply evt_done.
        apply (K2 q' sa _ m5 t4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sf_move sa _ m4 m5 t4 QX4 MU5 WM5) P14 INV5).
        * apply (sf_chain sa _ m4 m5 t4 _ _ QX4 MU5 WM5). destruct EK14 as (_ & _ & _ & _ & _ & _ & K7 & _). exact (K7 _ _ CH1).
        * destruct RP as [(R3 & _)|(_ & -> & M11 & _)]; [exfalso; clear - R3 R4; lia|].
          unfold E2, t4. cbn [t_req pa_pos pa_okm pa_meth pa_entp pa_X pa_len pa_cur].
          split; [reflexivity|]. split; [exists kA; exact OKM|]. split; [clear - M11; lia|]. split; [exact ENTP|]. clear - XB CR' CUR. lia.
      + intros m5 RN INV5 MU5 WM5. apply evt_done.
        exact (exitJ q' r sa _ m5 t4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sf_move sa _ m4 m5 t4 QX4 MU5 WM5) (QP_of_P1 sa _ t4 P14) INV5 RR).
  Qed.

  #[using="m0 POK RF0 mws MWL ws WSL"] Lemma pinv_stepAF : forall shd, Z.of_nat (cells_size shd) = 16 -> forall (W : list ivl) (LBc : BL) q' m m2 (stc st' : fsstate FI),
    pinvQS shd q' m -> apxF FI AI W LBc q' stc m m2 ->
    (forall X n, (q' <= X \/ (FSB FI <= X /\ X + n <= FSB FI + A0_FS_SIZE /\ (X + n <= P \/ P + 504 <= X)) \/ (SF <= X /\ X + n <= SF + 16)) -> 0 <= n -> disjoint_from W X n) ->
    fs_live FI stc = fs_newff FI st 1 :: fs_live FI st -> fs_live FI st' = fs_live FI stc -> RFAKE FI st' m2 ->
    stk asegs m2 lo q' -> mem_inv asegs m2 -> asan_env asegs m2 ->
    pinvQS shd q' m2.
  Proof.
    intros shd HSZ W LBc q' m m2 stc st' (ST & (j0 & j160 & j192 & QC) & MI & AE & (QB & QAL) & VR) AP DJW LIVE1 LIVE2 RF2 ST2 MI2 AE2.
    destruct VR as (Hq & GAP & FRhi & (w0 & FH) & (jf & FT1) & FT2 & SHF & FLG & _).
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof (fsb_ok FI) as (B1 & B2 & _).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1 & SHF2 & PAF & PAFL & PF1 & PF2).
    destruct (elive_of stc LIVE1) as (LVF & LVS & LVL & LVP & LSUB).
    assert (A0S : A0_FS_FRAMES = 36864) by reflexivity.
    assert (TRS : forall X cs, q' <= X -> rw_cells asegs m X cs -> rw_cells asegs m2 X cs).
    { intros X cs HX C. apply (apxF_rw_cells FI AI W LBc q' stc m m2 X cs AP C); [apply fclient_range_above; exact HX| apply DJW; [left; exact HX| lia]]. }
    assert (TRF : forall X cs, F <= X -> X + Z.of_nat (cells_size cs) <= F + 128 -> rw_cells asegs m X cs -> rw_cells asegs m2 X cs).
    { intros X cs H1 H2 C. apply (apxF_rw_cells FI AI W LBc q' stc m m2 X cs AP C); [apply fclient_range_lb; apply (Contracts.lb_sub _ _ _ _ _ LVF); lia| apply DJW; [right; left; lia| lia]]. }
    unfold H_pparse_seg.pinvQS, H_pparse_seg.prestQ.
    split; [exact ST2|].
    split; [exists j0, j160, j192; apply TRS; [clear; lia| exact QC]|].
    split; [exact MI2|]. split; [exact AE2|]. split; [exact (conj QB QAL)|].
    split; [exact Hq|].
    split. { eapply (stk_gagree (fun a => fclient FI AI LBc q' stc a /\ outside W a)); [intros a Ha [Hc Ho]; exact (AP a Ha Hc Ho)| exact GAP|].
             intros a Ha. split; [left; clear - Ha; lia|]. eapply disjoint_outside; [apply (DJW a 1); [left; clear - Ha; lia| lia]| lia]. }
    split; [apply TRS; [clear - QB; lia| exact FRhi]|].
    split; [exists w0; apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FH]|].
    split; [exists jf; apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FT1]|].
    split; [apply TRF; [clear; lia| simpl_sizes; clear; lia| exact FT2]|].
    split. { apply (apxF_rw_cells FI AI W LBc q' stc m m2 _ _ AP SHF); [apply fclient_range_ls; rewrite HSZ; exact LVS| apply DJW; [right; right; rewrite HSZ; lia| lia]]. }
    split. { apply (apxF_rw_cells FI AI W LBc q' stc m m2 _ _ AP FLG); [apply fclient_range_lf; exact LVL| apply DJW; [right; left; simpl_sizes; lia| simpl_sizes; lia]]. }
    exists st'. split; [exact RF2| rewrite LIVE2; exact LIVE1].
  Qed.

  #[using="mws MWL ws ras WSL TRH"] Lemma ra_bigQ : 4096 <= bv_unsigned ra.
  Proof.
    pose proof TRH as T. unfold A0_TRACES in T. cbn [In] in T.
    repeat (destruct T as [T|T]; [first [discriminate T| injection T; intros; lia]|]). destruct T.
  Qed.
  #[using="POK mws MWL ws QTOP WSL TRH"] Lemma chain_consQ : forall shd q' m, pinvQS shd q' m -> fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras ->
    fpchain m (am_stack_top FI AI) q' (bv_unsigned (wz q)) (bv_unsigned ra :: ras).
  Proof.
    intros shd q' m INV CH. pose proof INV as (_ & _ & _ & _ & (QB & QAL) & HR). destruct HR as (_ & _ & FRhi & _).
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & _).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (proj1 (rw_cells_app asegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra]) FRhi) as [_ T2].
    replace (q + -104 + Z.of_nat (cells_size [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) with (q - 16) in T2 by (simpl_sizes; lia).
    pose proof (proj1 (rw_cells_app asegs m (q - 16) [C8 s0] [C8 ra]) T2) as [T3 T4].
    replace (q - 16 + Z.of_nat (cells_size [C8 s0])) with (q - 8) in T4 by (simpl_sizes; lia).
    pose proof (rw_cells_bytes_at asegs _ _ _ T3) as B3. cbn [cells_bytes cbytes] in B3. rewrite app_nil_r in B3.
    pose proof (rw_cells_bytes_at asegs _ _ _ T4) as B4. cbn [cells_bytes cbytes] in B4. rewrite app_nil_r in B4.
    pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
    rewrite unsigned_lit by lia. cbn [fpchain]. unfold valid_frame, rd64.
    pose proof (bv_unsigned_in_range _ ra) as RR. pose proof (bv_unsigned_in_range _ s0) as SR. unfold bv_modulus in RR, SR.
    split; [split; [lia|]; split; [lia| clear - AL16; Z.div_mod_to_equations; lia]|]. split; [lia|].
    split; [split; [rewrite Z_to_bv_bv_unsigned; exact B4| exact RR]|]. split; [exact ra_bigQ|].
    exists (bv_unsigned s0). split; [split; [rewrite Z_to_bv_bv_unsigned; exact B3| exact SR]| exact CH].
  Qed.

  #[using="Type"] Lemma mownA_in : forall m (LB LB' : BL) A cap ok bs, mownA FI AI m LB A cap ok bs -> bsub FI AI (okbA FI AI ok A cap) LB' -> mownA FI AI m LB' A cap ok bs.
  Proof. intros m LB LB' A cap [k|] bs H SUB; cbn [mownA okbA] in *; [destruct H as [_ H2]; split; [apply SUB; left; reflexivity| exact H2]| exact H]. Qed.
  Definition LBKc (t : pstA FI AI) : BL := okbA FI AI (pa_sok FI AI t) (pa_SA FI AI t) (pa_scap FI AI t) ++ pa_UB FI AI t ++ LBK.
  #[using="Type"] Lemma pa_blocks_c : forall t, pa_blocks FI AI t ++ LBK = hl_blocks FI AI (pa_ns FI AI t) (pa_hs FI AI t) ++ okbA FI AI (pa_okm FI AI t) (pa_A FI AI t) (pa_cap FI AI t) ++ LBKc t.
  Proof. intros t. unfold pa_blocks, LBKc. rewrite <- !app_assoc. reflexivity. Qed.
  #[using="mws MWL ws WSL"] Lemma pa_blocks_len : forall m (t : pstA FI AI) (kA : K), p_hlist FI AI m P (pa_ns FI AI t) (pa_hs FI AI t) (pa_X FI AI t) -> pa_okm FI AI t = Some kA ->
    Z.of_nat (length (pa_blocks FI AI t)) = 4 * Z.of_nat (length (pa_hs FI AI t)) + 1 + Z.of_nat (length (okbA FI AI (pa_sok FI AI t) (pa_SA FI AI t) (pa_scap FI AI t) ++ pa_UB FI AI t)).
  Proof. intros m t kA PHL OKM. unfold pa_blocks. rewrite OKM. cbn [okbA]. rewrite !length_app, (H_phdr.p_hlist_len FI AI m P _ _ _ PHL). cbn [length]. lia. Qed.

  Definition t_ent (t : pstA FI AI) cur A len cap (okm : option K) bs meth ns hs X eb el err hack pos entp clen csz esp : pstA FI AI :=
    mkPSA FI AI cur A len cap okm bs meth (pa_uc FI AI t) (pa_rm FI AI t) (pa_sc FI AI t) (pa_SA FI AI t) (pa_slen FI AI t) (pa_scap FI AI t) (pa_sok FI AI t) (pa_sbs FI AI t)
          (pa_isreq FI AI t) (pa_maj FI AI t) (pa_min FI AI t) ns hs X eb el err hack pos entp clen csz esp (pa_ub FI AI t) (pa_UB FI AI t).

  Definition WPE : list ivl := H_pent_kit.pent_WA P.
  #[using="mws MWL ws WSL"] Lemma WPE_ok : Forall wpok WPE.
  Proof. unfold WPE, H_pent_kit.pent_WA, wpok, H_pparse_seg.inP, H_pparse_seg.inER. repeat (constructor; [first [left; cbn [fst snd]; lia| right; cbn [fst snd]; lia]|]). constructor. Qed.
  #[using="mws MWL ws WSL"] Lemma WPE_in : Forall (fun iv : ivl => inside (pparse_WA P) (fst iv) (snd iv - fst iv)) WPE.
  Proof. unfold WPE, H_pent_kit.pent_WA, pparse_WA. repeat (constructor; [cbn [inside fst snd]; first [left; lia| right; left; lia]|]). constructor. Qed.
  #[using="mws MWL ws WSL"] Lemma WPE_cls : Forall (acls WPE []) (H_pent_kit.pent_WA P).
  Proof.
    unfold WPE, H_pent_kit.pent_WA, acls.
    repeat (constructor; [cbn [fst snd inside]; split; [lia| left; first [left; lia| right; left; lia| right; right; left; lia| right; right; right; left; lia
                                                                          | right; right; right; right; left; lia| right; right; right; right; right; left; lia]]|]). constructor.
  Qed.

  Definition E3 (t : pstA FI AI) : Prop :=
    pa_pos FI AI t = 3 /\ (exists kA : K, pa_okm FI AI t = Some kA) /\ pa_meth FI AI t <= 11 /\ pa_entp FI AI t = 1
    /\ pa_X FI AI t + 2 * (pa_len FI AI t - pa_cur FI AI t) <= 2^27 + 64.

  #[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 POK RF0 FCO MWL HR0 KSUB0 QTOP GMX WSL HID ZSTAT GLR TRH TRE GERM"] Lemma pentJ : forall q' (s : PS) (LB : BL) m (t : pstA FI AI) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31,
    QX s LB m t -> P2 s LB t -> pinvQ q' m -> fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras -> E3 t ->
    AJ FI AI J POST (loopstQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m) s LB.
  Proof.
    intros q' s LB m t x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 QXF P2F INV CH (POS3 & (kA & OKM) & M11 & ENTP & XB).
    pose proof QXF as (HR & PP & ISR & SUB & ND & STAT & SHP & SHZ & SHR & _).
    pose proof PP as (PSC & PMSG & CUR & PMETH & PURI & PRS & PSM & PVER & PHL & PENT & PCTL & PURL & UBO).
    rewrite OKM in PMSG.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof INV as (ST & _ & MI & AE & (QB & QAL) & VR). destruct VR as (_ & _ & _ & _ & _ & _ & _ & _ & (stc & RF & LIVEc)).
    destruct (elive_of stc LIVEc) as (_ & _ & _ & LVP & LSUB).
    pose proof PCTL as (CTLC & _ & _ & PR & _).
    destruct (pctl_split m _ _ _ _ _ _ _ CTLC) as (_ & _ & C448 & _).
    pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
    pose proof STAT as (PHS & GS & SHFC & SHFR & PSTE & _).
    destruct (pstat_of_pp m STAT) as (_ & _ & _ & SHSEP & _ & _ & SHE).
    destruct P2F as (N1 & LB1 & d & PF & HL & D0 & DC & LC & TG7 & TG6 & CNT & EBUD).
    destruct (QX_clow s LB m t QXF) as (ev & CLOW).
    apply aj_cps.
    apply (loopQ q' (pa_pos FI AI t) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m _ MI C448 ltac:(apply (proj1 SHP); clear; lia) PR);
      try (intros Hx; exfalso; clear - Hx POS3; lia).
    intros _. apply evt_done.
    unfold H_pparse_seg.ajcallstQ, H_pparse_seg.pregsQ.
    rewrite (pa_blocks_c t), OKM in SUB, ND.
    eapply (aj_bind FI AI J).
    { eapply (H_pent.pent_spec_A IC FI AI J AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 GL GLR GERM (wz 0x8ab28) q') with (st := stc) (lo := lo) (LBK := LBKc t) (P := P)
               (cur := pa_cur FI AI t) (A := pa_A FI AI t) (len := pa_len FI AI t) (cap := pa_cap FI AI t) (kA := kA) (bs := pa_bs FI AI t) (ns := pa_ns FI AI t) (hs := pa_hs FI AI t)
               (X := pa_X FI AI t) (meth := pa_meth FI AI t) (isreq := pa_isreq FI AI t) (maj := pa_maj FI AI t) (min := pa_min FI AI t) (rm := pa_rm FI AI t) (sc := pa_sc FI AI t)
               (err := pa_err FI AI t) (hack := pa_hack FI AI t) (pos := pa_pos FI AI t) (entp := pa_entp FI AI t) (clen := pa_clen FI AI t) (csz := pa_csz FI AI t) (esp := pa_esp FI AI t)
               (gmax := gmax) (eb := pa_ebw FI AI t) (el := pa_elw FI AI t) (ev := ev) (canary := canary) (ws := ws) (cslack := cslack) (ras := bv_unsigned ra :: ras);
        [exact HR| exact RF| exact (fs_call_ok_push FI st stc (wz A0_TP) 4%nat _ FCO LIVEc)| exact AE| exact ST| exact CLO| clear - LO QB; lia| exact QAL| clear - QTOP QB; lia| exact MI| exact LVP| exact PHI| exact PAL| exact SHP
         | exact PSC| exact PMSG| exact CUR| exact PENT| exact PCTL| exact PHL| split; [exact (proj1 PMETH)| clear - M11 PMETH; destruct PMETH as [_ R]; lia]| exact PVER| exact PRS| exact SUB| exact ND| exact XB
         | rewrite ENTP; change (H_pent_kit.pe_meas0 gmax 1 (pa_elw FI AI t) + 1) with (2 * gmax + 4 + 1); eapply (H_pent_kit.ebud_mono FI AI); [| | exact EBUD]; [clear; lia| clear - DC; lia]
         | rewrite ENTP; unfold H_pent_kit.ent_okA; split; [intros Hx; exfalso; clear - Hx; lia| split; [intros [Hx|Hx]; discriminate Hx| intros Hx; discriminate Hx]]
         | clear - GMX; lia| exact PSTE| exact CLOW| exact SHE| exact GS| exact SHSEP| exact SHFC| exact SHFR| exact WSL| exact HID| exact PHS| exact ZSTAT
         | apply (shz_sub m _ _ _ _ SHZ); [clear; lia| apply sh_mono; clear - QB; lia]| apply (shr_sub m _ _ _ _ SHR); [clear; lia| pose proof (sh_mono q' q ltac:(clear - QB; lia)); lia]
         | exact (chain_consQ qshadow q' m INV CH)| rewrite unsigned_lit by lia; exact TRE| reflexivity]. }
    intros sq LBq msq PO. unfold H_pent_kit.pent_post_A in PO.
    destruct PO as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & stq & r & cur' & A' & len' & cap' & okm' & bs' & eb' & el' & err' & hack' & pos' & entp' & clen' & csz' & esp' & X' & meth' & ns' & hs'
                    & -> & MI1 & ST1 & AE1 & RF1 & LIVE1 & APF & HR1 & SUBq & NDq & (k & d2 & ES & KR & D2R & TG7q & CNTq) & HSUMq & PSC1 & PMSG1 & CUR1 & PENT1 & PCTL1 & PHL1 & PMETH1 & PVER1 & PRS1
                    & SHP1 & SHZ1 & SHR1 & PSTE1 & CL1 & _ & RR & RN4 & OKN).
    rewrite ret_pc_even by lia.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1' & SHF2' & PAF & PAFL & PF1 & PF2).
    assert (SHB : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000) by (unfold sh, SHADOW_OFF in *; clear - B1 B2 B4 ACR; split; Z.div_mod_to_equations; lia).
    assert (PSH : P + 504 <= SF \/ SF + 16 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    set (OB := okbA FI AI (pa_sok FI AI t) (pa_SA FI AI t) (pa_scap FI AI t) ++ pa_UB FI AI t).
    assert (OBc : bsub FI AI OB (LBKc t)) by (intros b Hb; unfold LBKc; unfold OB in Hb; rewrite app_assoc; apply in_or_app; left; exact Hb).
    assert (KSUBc : bsub FI AI LBK (LBKc t)) by (intros b Hb; unfold LBKc; apply in_or_app; right; apply in_or_app; right; exact Hb).
    assert (CSUB : bsub FI AI (LBKc t) LB) by (intros b Hb; apply SUB; apply in_or_app; right; apply in_or_app; right; exact Hb).
    pose proof (ekeep_apxF (H_pent_kit.pent_WA P) WPE [] OB (LBKc t) s LB q' stc m m1 APF ltac:(clear - CLO LO QB; lia) ltac:(clear - QB; lia) LSUB WPE_cls WPE_ok WPE_in HR
                  (fun b Hb => False_ind _ Hb) OBc (fun b Hb => CSUB b (OBc b Hb)) KSUBc (fun b Hb => CSUB b (KSUBc b Hb)) (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha) SHP1) as EK.
    assert (INV1 : pinvQ q' m1).
    { apply (pinv_stepAF qshadow eq_refl (H_pent_kit.pent_WA P) (LBKc t) q' m m1 stc stq INV APF); [| exact LIVEc| exact LIVE1| exact RF1| exact ST1| exact MI1| exact AE1].
      intros Xa n HX Hn. unfold H_pent_kit.pent_WA. cbn [disjoint_from fst snd]. repeat split; try exact I; lia. }
    set (t' := t_ent t cur' A' len' cap' okm' bs' meth' ns' hs' X' eb' el' err' hack' pos' entp' clen' csz' esp').
    Ltac dje := let PLOx := fresh "PLOx" in pose proof POK as (_ & _ & _ & _ & PLOx & _); unfold WPE, H_pent_kit.pent_WA; cbn [disjoint_from fst snd]; repeat split; lia.
    assert (PP1 : p_parserA FI AI m1 LBq P t').
    { unfold p_parserA, t', t_ent. cbn [pa_cur pa_A pa_len pa_cap pa_okm pa_bs pa_meth pa_uc pa_rm pa_sc pa_SA pa_slen pa_scap pa_sok pa_sbs pa_isreq pa_maj pa_min
        pa_ns pa_hs pa_X pa_ebw pa_elw pa_err pa_hack pa_pos pa_entp pa_clen pa_csz pa_esp pa_ub pa_UB].
      split; [exact PSC1|]. split; [exact PMSG1|]. split; [exact CUR1|].
      split; [split; [exact (proj1 PMETH1)| destruct PMETH1 as [_ R]; clear - R; lia]|].
      split; [exact (ek_uri _ _ m m1 _ EK ltac:(dje) PURI)|]. split; [exact PRS1|].
      split. { destruct (ek_smsg _ _ LB m m1 _ _ _ _ _ EK ltac:(dje) ltac:(intros b Hb; unfold OB; apply in_or_app; left; exact Hb) PSM) as (H1 & H2 & H3).
               split; [exact H1|]. split; [| exact H3]. apply (mownA_in m1 LB LBq _ _ _ _ H2). intros b Hb. apply SUBq. apply in_or_app; right. apply in_or_app; right. unfold LBKc. apply in_or_app; left. exact Hb. }
      split; [exact PVER1|]. split; [exact PHL1|]. split; [exact PENT1|]. split; [exact PCTL1|].
      split; [exact (ek_url _ _ m m1 _ EK ltac:(dje) PURL)| exact UBO]. }
    assert (QX1 : QX sq LBq m1 t').
    { eapply (QX_move WPE _ s LB m t sq LBq m1 t'); [exact QXF| exact EK| exact WPE_ok| exact HR1| exact PP1| reflexivity| | | exact CL1].
      - rewrite (pa_blocks_c t'). exact SUBq.
      - rewrite (pa_blocks_c t'). exact NDq. }
    assert (QP1 : QP sq LBq t').
    { unfold QP. rewrite ENTP in KR. change (H_pent_kit.pe_meas0 gmax 1 (pa_elw FI AI t)) with (2 * gmax + 4) in KR.
      split; [exists N1, LB1, (am_nsec FI AI s), LB, d, k, d2; split; [exact PF|]; split; [exact HL|]; split; [exact ES|];
              split; [clear - KR; lia|]; split; [exact D0|]; split; [clear - D2R; lia|]; split; [clear - D2R DC; lia|];
              unfold t'; cbn [t_ent pa_hs]; clear - TG7 TG7q; lia|].
      split; [unfold t'; cbn [t_ent pa_hs]; clear - TG6 HSUMq; lia|].
      destruct okm' as [kq|]; [| exfalso; apply OKN; reflexivity].
      pose proof (pa_blocks_len m t kA PHL OKM) as L1. pose proof (pa_blocks_len m1 t' kq PHL1 eq_refl) as L2.
      unfold t' in L2 at 2 3 4 5 6. cbn [t_ent pa_hs pa_sok pa_SA pa_scap pa_UB] in L2. clear - CNT CNTq L1 L2. lia. }
    assert (RR6 : 0 <= r <= 6) by (clear - RR; lia).
    apply aj_cps. apply (retQ 0x8ab28 q' r t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 _ (or_intror (or_intror eq_refl)) RR6).
    - intros R4. exfalso. exact (RN4 R4).
    - intros _. apply evt_done. exact (exitJ q' r sq LBq m1 t' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ QX1 QP1 INV1 RR).
  Qed.

  Definition t_hdr (t : pstA FI AI) cur meth pos ns hs X : pstA FI AI :=
    mkPSA FI AI cur (pa_A FI AI t) (pa_len FI AI t) (pa_cap FI AI t) (pa_okm FI AI t) (pa_bs FI AI t) meth (pa_uc FI AI t) (pa_rm FI AI t) (pa_sc FI AI t)
          (pa_SA FI AI t) (pa_slen FI AI t) (pa_scap FI AI t) (pa_sok FI AI t) (pa_sbs FI AI t) (pa_isreq FI AI t) (pa_maj FI AI t) (pa_min FI AI t)
          ns hs X (pa_ebw FI AI t) (pa_elw FI AI t) (pa_err FI AI t) (pa_hack FI AI t) pos (pa_entp FI AI t) (pa_clen FI AI t) (pa_csz FI AI t) (pa_esp FI AI t)
          (pa_ub FI AI t) (pa_UB FI AI t).
  Definition WPH : list ivl := [(P + 4, P + 8); (P + 288, P + 344); (P + 448, P + 452); (P + 488, P + 496)]%Z.
  #[using="mws MWL ws WSL"] Lemma WPH_ok : Forall wpok WPH.
  Proof. unfold WPH, wpok, H_pparse_seg.inP. repeat (constructor; [left; cbn [fst snd]; lia|]). constructor. Qed.
  #[using="mws MWL ws WSL"] Lemma WPH_in : Forall (fun iv : ivl => inside (pparse_WA P) (fst iv) (snd iv - fst iv)) WPH.
  Proof. unfold WPH, pparse_WA. repeat (constructor; [cbn [inside fst snd]; left; lia|]). constructor. Qed.
  #[using="mws MWL ws WSL"] Lemma phW_cls : forall (kA : K) A cap, 0 <= cap -> Forall (acls WPH [(kA, A, cap + 1)]) (H_phdr.phdr_WA P A cap).
  Proof.
    intros kA A cap Hc. unfold H_phdr.phdr_WA, WPH, acls.
    repeat apply Forall_cons; try apply Forall_nil; (split; [cbn [fst snd]; lia|]);
      [left; cbn [inside fst snd]; lia| left; cbn [inside fst snd]; lia| left; cbn [inside fst snd]; lia| left; cbn [inside fst snd]; lia|].
    right. exists (kA, A, cap + 1). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia.
  Qed.
  #[using="Type"] Lemma txt_idj : forall t (kA : K), pa_okm FI AI t = Some kA -> NoDup (map blk_id (pa_blocks FI AI t ++ LBK)) ->
    idj [(kA, pa_A FI AI t, pa_cap FI AI t + 1)] (okbA FI AI (pa_sok FI AI t) (pa_SA FI AI t) (pa_scap FI AI t) ++ pa_UB FI AI t) /\ idj [(kA, pa_A FI AI t, pa_cap FI AI t + 1)] LBK.
  Proof.
    intros t kA OKM ND. rewrite (pa_blocks_c t), OKM in ND. cbn [okbA] in ND.
    apply nd_app in ND. destruct ND as (_ & _ & ND2). apply (nd_app [(kA, pa_A FI AI t, pa_cap FI AI t + 1)]) in ND2. destruct ND2 as (_ & I3 & _).
    unfold LBKc in I3. rewrite app_assoc in I3. apply idj_app_r in I3. exact I3.
  Qed.

  #[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 POK RF0 FCO MWL HR0 KSUB0 QTOP GMX WSL HID ZSTAT GLR TRH TRE GERM"] Lemma hdrJ : CONT2.
  Proof.
    unfold CONT2. intros q' s LB m t x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 QXF P1F INV CH (POS2 & (kA & OKM) & M11 & ENTP & XB).
    pose proof QXF as (HR & PP & ISR & SUB & ND & STAT & SHP & SHZ & SHR & _).
    pose proof PP as (PSC & PMSG & CUR & PMETH & PURI & PRS & PSM & PVER & PHL & PENT & PCTL & PURL & UBO).
    rewrite OKM in PMSG.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof INV as (ST & _ & MI & AE & (QB & QAL) & VR). destruct VR as (_ & _ & _ & _ & _ & _ & _ & _ & (stc & RF & LIVEc)).
    destruct (elive_of stc LIVEc) as (_ & _ & _ & LVP & LSUB).
    pose proof PCTL as (CTLC & _ & _ & PR & _).
    destruct (pctl_split m _ _ _ _ _ _ _ CTLC) as (_ & _ & C448 & _).
    pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
    pose proof STAT as (PHS & _).
    destruct P1F as (PF & HS & CNT & LEN & CRX & BUD1).
    destruct (p_msg_facts FI AI m LB P _ _ _ (Some kA) _ s HR PMSG) as (HL & HCp & LBS0 & _ & SOME). unfold LMAX_A in HCp.
    destruct (SOME ltac:(discriminate)) as (S1 & S2 & S3 & S4 & S5 & S6).
    destruct (txt_idj t kA OKM ND) as [IDO IDK].
    apply aj_cps.
    apply (loopQ q' (pa_pos FI AI t) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m _ MI C448 ltac:(apply (proj1 SHP); clear; lia) PR);
      try (intros Hx; exfalso; clear - Hx POS2; lia).
    intros _. apply evt_done.
    unfold H_pparse_seg.ajcallstQ, H_pparse_seg.pregsQ.
    rewrite (pa_blocks_c t), OKM in SUB, ND. cbn [okbA app] in SUB, ND.
    assert (HSUB : bsub FI AI (hl_blocks FI AI (pa_ns FI AI t) (pa_hs FI AI t)) LB) by (intros b Hb; apply SUB; apply in_or_app; left; exact Hb).
    assert (KIN : In (kA, pa_A FI AI t, pa_cap FI AI t + 1) LB) by (apply SUB; apply in_or_app; right; left; reflexivity).
    assert (CSUB : bsub FI AI (LBKc t) LB) by (intros b Hb; apply SUB; apply in_or_app; right; right; exact Hb).
    eapply (aj_bind FI AI J).
    { eapply (H_phdr.phdr_spec_A IC FI AI J AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 (wz 0x8aad4) q') with (st := stc) (lo := lo) (LBK := LBKc t) (P := P)
               (cur := pa_cur FI AI t) (A := pa_A FI AI t) (len := pa_len FI AI t) (cap := pa_cap FI AI t) (kA := kA) (bs := pa_bs FI AI t) (ns := pa_ns FI AI t) (hs := pa_hs FI AI t)
               (X := pa_X FI AI t) (meth := pa_meth FI AI t) (isreq := pa_isreq FI AI t) (maj := pa_maj FI AI t) (min := pa_min FI AI t)
               (err := pa_err FI AI t) (hack := pa_hack FI AI t) (pos := pa_pos FI AI t) (entp := pa_entp FI AI t) (clen := pa_clen FI AI t) (csz := pa_csz FI AI t) (esp := pa_esp FI AI t)
               (ws := ws) (cslack := cslack) (ras := bv_unsigned ra :: ras);
        [exact HR| exact RF| exact (fs_call_ok_le FI stc (wz A0_TP) 4%nat 3%nat (fs_call_ok_push FI st stc (wz A0_TP) 4%nat _ FCO LIVEc) ltac:(clear; lia))| exact AE| exact ST| exact CLO| clear - LO QB; lia| exact QAL| clear - QTOP QB; lia| exact MI| exact LVP| exact PHI| exact PAL| exact SHP
         | exact PSC| exact PMSG| exact CUR| split; [exact (proj1 PMETH)| clear - M11 PMETH; destruct PMETH as [_ R]; lia]| exact PVER| exact PHL| exact PCTL| exact HSUB| exact CSUB| exact ND| exact XB
         | rewrite HS; apply (H_pent_kit.hbud_mono FI AI (pa_len FI AI t_0 - pa_cur FI AI t_0)); [clear - LEN CRX; lia| exact (proj1 BUD1)]
         | exact WSL| exact HID| exact PHS| exact ZSTAT
         | apply (shz_sub m _ _ _ _ SHZ); [clear; lia| apply sh_mono; clear - QB; lia]| apply (shr_sub m _ _ _ _ SHR); [clear; lia| pose proof (sh_mono q' q ltac:(clear - QB; lia)); lia]
         | exact (chain_consQ qshadow q' m INV CH)| rewrite unsigned_lit by lia; exact TRH| reflexivity]. }
    intros sq LBq msq PO. unfold H_phdr.phdr_post_A in PO.
    destruct PO as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & stq & r & cur' & meth' & pos' & d & ns' & hs'
                    & -> & MI1 & ST1 & AE1 & RF1 & LIVE1 & APF & HR1 & KIN1 & HSUB1 & KSUB1 & ND1 & HLS & DR & PSC1 & PMSG1 & PMETH1 & PVER1 & PHL1 & HSUM1 & HSD1 & CNT1 & CNL1 & PCTL1 & SHP1 & SHZ1 & SHR1 & MO & CR & RR & EXR).
    rewrite ret_pc_even by lia.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1' & SHF2' & PAF & PAFL & PF1 & PF2).
    assert (SHB : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000) by (unfold sh, SHADOW_OFF in *; clear - B1 B2 B4 ACR; split; Z.div_mod_to_equations; lia).
    assert (PSH : P + 504 <= SF \/ SF + 16 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    set (OB := okbA FI AI (pa_sok FI AI t) (pa_SA FI AI t) (pa_scap FI AI t) ++ pa_UB FI AI t).
    assert (OBc : bsub FI AI OB (LBKc t)) by (intros b Hb; unfold LBKc; unfold OB in Hb; rewrite app_assoc; apply in_or_app; left; exact Hb).
    assert (KSUBc : bsub FI AI LBK (LBKc t)) by (intros b Hb; unfold LBKc; apply in_or_app; right; apply in_or_app; right; exact Hb).
    pose proof (ekeep_apxF (H_phdr.phdr_WA P (pa_A FI AI t) (pa_cap FI AI t)) WPH [(kA, pa_A FI AI t, pa_cap FI AI t + 1)] OB (LBKc t) s LB q' stc m m1 APF
                  ltac:(clear - CLO LO QB; lia) ltac:(clear - QB; lia) LSUB (phW_cls kA (pa_A FI AI t) (pa_cap FI AI t) ltac:(clear - HL; lia)) WPH_ok WPH_in HR
                  ltac:(intros b [<-|[]]; exact KIN) OBc (fun b Hb => CSUB b (OBc b Hb)) KSUBc (fun b Hb => CSUB b (KSUBc b Hb)) IDO IDK SHP1) as EK.
    assert (INV1 : pinvQ q' m1).
    { apply (pinv_stepAF qshadow eq_refl (H_phdr.phdr_WA P (pa_A FI AI t) (pa_cap FI AI t)) (LBKc t) q' m m1 stc stq INV APF); [| exact LIVEc| exact LIVE1| exact RF1| exact ST1| exact MI1| exact AE1].
      intros Xa n HX Hn. unfold H_phdr.phdr_WA. cbn [disjoint_from fst snd].
      clear - HX Hn CLO LO QB PLO PHI B1 B2 FLO FHI SFB SHB PSH S1 S2 S5 S6 ACR HL. repeat split; try exact I; lia. }
    set (t' := t_hdr t cur' meth' pos' ns' hs' (pa_X FI AI t + 2 * (cur' - pa_cur FI AI t))).
    Ltac djh := let PLOx := fresh "PLOx" in pose proof POK as (_ & _ & _ & _ & PLOx & _); unfold WPH; cbn [disjoint_from fst snd]; repeat split; lia.
    assert (PP1 : p_parserA FI AI m1 LBq P t').
    { unfold p_parserA, t', t_hdr. cbn [pa_cur pa_A pa_len pa_cap pa_okm pa_bs pa_meth pa_uc pa_rm pa_sc pa_SA pa_slen pa_scap pa_sok pa_sbs pa_isreq pa_maj pa_min
        pa_ns pa_hs pa_X pa_ebw pa_elw pa_err pa_hack pa_pos pa_entp pa_clen pa_csz pa_esp pa_ub pa_UB].
      split; [exact PSC1|]. split; [rewrite OKM; exact PMSG1|]. split; [clear - CR CUR; lia|].
      split; [split; [exact (proj1 PMETH1)| destruct PMETH1 as [_ R]; clear - R; lia]|].
      split; [exact (ek_uri _ _ m m1 _ EK ltac:(djh) PURI)|]. split; [exact (ek_rs _ _ m m1 _ _ EK ltac:(djh) PRS)|].
      split. { destruct (ek_smsg _ _ LB m m1 _ _ _ _ _ EK ltac:(djh) ltac:(intros b Hb; unfold OB; apply in_or_app; left; exact Hb) PSM) as (H1 & H2 & H3).
               split; [exact H1|]. split; [| exact H3]. apply (mownA_in m1 LB LBq _ _ _ _ H2). intros b Hb. apply KSUB1. unfold LBKc. apply in_or_app; left. exact Hb. }
      split; [exact PVER1|]. split; [exact PHL1|]. split; [exact (ek_ent _ _ m m1 _ _ EK ltac:(djh) PENT)|]. split; [exact PCTL1|].
      split; [exact (ek_url _ _ m m1 _ EK ltac:(djh) PURL)| exact UBO]. }
    assert (CL1 : exists ev, clow canary ev m1) by (apply (ek_clow _ _ m m1 EK WPH_ok ltac:(djh) (QX_clow s LB m t QXF))).
    assert (QX1 : QX sq LBq m1 t').
    { eapply (QX_move WPH _ s LB m t sq LBq m1 t'); [exact QXF| exact EK| exact WPH_ok| exact HR1| exact PP1| reflexivity| | | exact CL1].
      - rewrite (pa_blocks_c t'). unfold t', t_hdr, LBKc. cbn [pa_ns pa_hs pa_okm pa_A pa_cap pa_sok pa_SA pa_scap pa_UB]. rewrite OKM. cbn [okbA app].
        intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|[<-|Hb]]; [exact (HSUB1 b Hb)| exact KIN1| exact (KSUB1 b Hb)].
      - rewrite (pa_blocks_c t'). unfold t', t_hdr, LBKc. cbn [pa_ns pa_hs pa_okm pa_A pa_cap pa_sok pa_SA pa_scap pa_UB]. rewrite OKM. cbn [okbA app]. exact ND1. }
    assert (P21 : P2 sq LBq t').
    { pose proof (pfirst_nsec _ _ _ _ PF) as NS.
      exists (am_nsec FI AI s), LB, d. unfold t'. cbn [t_hdr pa_len pa_cur pa_hs].
      split; [exact PF|]. split; [exact HLS|]. split; [clear - DR; lia|]. split; [clear - DR CR CRX LEN; lia|]. split; [clear - CR; lia|].
      split; [rewrite <- HS; clear - CNT1 NS; lia|]. split; [rewrite <- HS; clear - HSUM1 CR CRX LEN; lia|].
      split. { pose proof (pa_blocks_len m t kA PHL OKM) as L1. pose proof (pa_blocks_len m1 (t_hdr t cur' meth' pos' ns' hs' (pa_X FI AI t + 2 * (cur' - pa_cur FI AI t))) kA PHL1 OKM) as L2.
               cbn [t_hdr pa_hs pa_sok pa_SA pa_scap pa_UB] in L2. clear - CNT CNL1 L1 L2. lia. }
      apply (proj2 BUD1 d _ _ sq _ HLS ltac:(clear - DR CR CRX LEN; lia) eq_refl).
      - exact (H_phdr.p_hlist_cgG FI AI _ _ _ _ _ PHL1).
      - rewrite <- HS. pose proof (HCount.cgG_step FI AI (pa_hs FI AI t) hs' (am_nsec FI AI sq - am_nsec FI AI s) d ltac:(clear - CNT1; lia) HSD1) as CPL.
        clear - CPL. unfold CG_A, CG_B, CG_SL in *. lia. }
    assert (CH1 : fpchain m1 (am_stack_top FI AI) q (bv_unsigned s0) ras) by (destruct EK as (_ & _ & _ & _ & _ & _ & K7 & _); exact (K7 _ _ CH)).
    assert (RR6 : 0 <= r <= 6) by (clear - RR; lia).
    apply aj_cps. apply (retQ 0x8aad4 q' r t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 _ (or_intror (or_introl eq_refl)) RR6).
    - intros R4. apply evt_done.
      apply (pentJ q' sq LBq m1 t' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ QX1 P21 INV1 CH1).
      destruct EXR as [(_ & PE)|[(R0 & _)|(RN & _)]]; [| exfalso; unfold PARSE_SUCCESS in R0; clear - R0 R4; lia| exfalso; unfold PARSE_OK in RN; clear - RN R4; lia].
      unfold E3, t'. cbn [t_hdr pa_pos pa_okm pa_meth pa_entp pa_X pa_len pa_cur].
      split; [exact PE|]. split; [exists kA; exact OKM|]. split; [destruct PMETH1 as [_ R]; clear - R; lia|]. split; [exact ENTP|]. clear - XB CR. lia.
    - intros RN. apply evt_done. exact (exitJ q' r sq LBq m1 t' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ QX1 (QP_of_P2 sq LBq t' P21) INV1 RR).
  Qed.

  #[using="Type"] Lemma nd_replace : forall (X S Y : BL) (b : BLK), NoDup (map blk_id (X ++ S ++ Y)) -> idj [b] (X ++ Y) -> NoDup (map blk_id (X ++ [b] ++ Y)).
  Proof.
    intros X S Y b ND IB. apply nd_app in ND. destruct ND as (NX & IXY & ND2). apply nd_app in ND2. destruct ND2 as (_ & _ & NY).
    apply idj_app_r in IXY. destruct IXY as [_ IXY]. apply idj_app_r in IB. destruct IB as [IBX IBY].
    apply nd_app. split; [exact NX|]. split; [apply idj_app_r; split; [apply idj_sym; exact IBX| exact IXY]|].
    apply (nd_cons b Y). split; [exact IBY| exact NY].
  Qed.
  Definition t_resp (t : pstA FI AI) cur sc maj min SA slen scap (sok : option K) sbs pos : pstA FI AI :=
    mkPSA FI AI cur (pa_A FI AI t) (pa_len FI AI t) (pa_cap FI AI t) (pa_okm FI AI t) (pa_bs FI AI t) (pa_meth FI AI t) (pa_uc FI AI t) (pa_rm FI AI t) sc
          SA slen scap sok sbs (pa_isreq FI AI t) maj min (pa_ns FI AI t) (pa_hs FI AI t) (pa_X FI AI t) (pa_ebw FI AI t) (pa_elw FI AI t) (pa_err FI AI t) (pa_hack FI AI t) pos
          (pa_entp FI AI t) (pa_clen FI AI t) (pa_csz FI AI t) (pa_esp FI AI t) (pa_ub FI AI t) (pa_UB FI AI t).
  Definition WPP : list ivl := [(P + 224, P + 288); (P + 440, P + 452); (P + 488, P + 496); (ERRNO_A, ERRNO_A + 4)]%Z.
  #[using="mws MWL ws WSL"] Lemma WPP_ok : Forall wpok WPP.
  Proof. unfold WPP, wpok, H_pparse_seg.inP, H_pparse_seg.inER. repeat (constructor; [first [left; cbn [fst snd]; lia| right; cbn [fst snd]; lia]|]). constructor. Qed.
  #[using="mws MWL ws WSL"] Lemma WPP_in : Forall (fun iv : ivl => inside (pparse_WA P) (fst iv) (snd iv - fst iv)) WPP.
  Proof. unfold WPP, pparse_WA. repeat (constructor; [cbn [inside fst snd]; first [left; lia| right; left; lia]|]). constructor. Qed.

  Definition WPT (okm : option K) (A cap : Z) : list ivl := WPP ++ match okm with Some _ => [(A, A + (cap + 1))] | None => [] end.
  #[using="mws MWL ws WSL"] Lemma WPT_cls : forall (okm : option K) A cap, 0 <= cap -> Forall (acls WPP (okbA FI AI okm A cap)) (WPT okm A cap).
  Proof.
    intros okm A cap Hc. unfold WPT, WPP, acls. apply Forall_app. split.
    - constructor; [cbn [fst snd inside]; split; [lia| left; left; lia]|].
      constructor; [cbn [fst snd inside]; split; [lia| left; right; left; lia]|].
      constructor; [cbn [fst snd inside]; split; [lia| left; right; right; left; lia]|].
      constructor; [cbn [fst snd inside]; split; [lia| left; right; right; right; left; lia]| constructor].
    - destruct okm as [kA|]; [| constructor]. constructor; [| constructor]. cbn [fst snd]. split; [lia|]. right. exists (kA, A, cap + 1). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia.
  Qed.
  #[using="mws MWL ws WSL"] Lemma WPT_sub : forall (okm : option K) A cap bn, (okm = None -> A = 0 /\ bn = 0) -> (okm <> None -> bn = cap + 1) -> sub_fp (H_presp.presp_WA P A bn) (WPT okm A cap).
  Proof.
    intros okm A cap bn HN HS x Hx. unfold H_presp.presp_WA, WPT, WPP in *.
    destruct okm as [kA|]; [rewrite (HS ltac:(discriminate))| destruct (HN eq_refl) as [-> ->]]; cbn [app outside fst snd] in *; repeat split; try lia; try tauto.
  Qed.

  #[using="POK mws MWL ws WSL"] Lemma ek_clow_e : forall WP OB m m', ekeep WP OB m m' -> Forall wpok WP -> (exists ev, clow canary ev m) -> (exists ev', rw_cells asegs m' ERRNO_A [C4 ev']) ->
    exists ev, clow canary ev m'.
  Proof.
    intros WP OB m m' EK HW (ev & _ & CL2 & CL3) (ev' & CE). pose proof EK as (K1 & _). exists ev'. unfold clow, A0_got_ssp, A0_ssp_guard in *.
    split; [exact CE|].
    split; [apply (ek_scell WP OB m m' _ _ EK HW); [stat_band| simpl_sizes; lia| exact CL2]|].
    apply (K1 _ _); [right; split; [stat_band| simpl_sizes; lia]| apply (dj_wpok_low2 WP _ _ HW); simpl_sizes; lia| exact CL3].
  Qed.

  #[using="mws MWL ws WSL"] Lemma cnt_arith : forall lb b0 l0 x s u a' : nat, (lb + b0 <= l0 + (x + (s + u)))%nat -> (a' + s <= lb + 1)%nat -> (a' + b0 <= l0 + (x + (1 + u)))%nat.
  Proof. intros. lia. Qed.

  #[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 POK RF0 FCO MWL HR0 KSUB0 QTOP GMX WSL HID ZSTAT GLR TRH TRE PBUD GERM"] Lemma prespJ : forall q' m (t : pstA FI AI) x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    QX s_0 LB_0 m t -> P1 s_0 LB_0 t -> pinvQ q' m -> fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras -> pp_sideA FI AI t ->
    AJ FI AI J POST (ajcallstQ 0x879d0 0x8ab08 q' x5 x6 x7 (wz 1) x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m) s_0 LB_0.
  Proof.
    intros q' m t x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 QXF P1F INV CH SIDE.
    pose proof QXF as (HR & PP & ISR & SUB & ND & STAT & SHP & SHZ & SHR & _).
    pose proof PP as (PSC & PMSG & CUR & PMETH & PURI & PRS & PSM & PVER & PHL & PENT & PCTL & PURL & UBO).
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof INV as (ST & _ & MI & AE & (QB & QAL) & VR). destruct VR as (_ & _ & _ & _ & _ & _ & _ & _ & (stc & RF & LIVEc)).
    destruct (elive_of stc LIVEc) as (_ & _ & _ & LVP & LSUB).
    pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
    destruct P1F as (PF & HS & CNT & LEN & CRX & BUD1).
    destruct SIDE as (_ & ENTP & UB0 & UBN & M11 & SCAPB & SNUL & XB & LEN26 & SCAP0 & CURZ).
    destruct (pstat_of_pp m STAT) as (_ & _ & _ & SHSEP & _ & _ & _).
    pose proof STAT as (_ & _ & _ & _ & _ & SHFR & SHFS & _).
    destruct (QX_clow s_0 LB_0 m t QXF) as (ev & CLE & CLG & CLS).
    destruct (p_msg_facts FI AI m LB_0 P _ _ _ _ _ s_0 HR PMSG) as (HL & HCp & LBS0 & NONE & SOME). unfold LMAX_A in HCp.

    set (HLB := hl_blocks FI AI (pa_ns FI AI t) (pa_hs FI AI t)) in *.
    set (MB := okbA FI AI (pa_okm FI AI t) (pa_A FI AI t) (pa_cap FI AI t)) in *.
    set (SB := okbA FI AI (pa_sok FI AI t) (pa_SA FI AI t) (pa_scap FI AI t)) in *.
    assert (EQB : pa_blocks FI AI t ++ LBK = (HLB ++ MB) ++ SB ++ (pa_UB FI AI t ++ LBK)) by (unfold pa_blocks, HLB, MB, SB; rewrite <- !app_assoc; reflexivity).
    rewrite EQB in SUB, ND.
    pose proof ND as ND0. apply nd_app in ND0. destruct ND0 as (NDX & IXSY & NDSY). apply nd_app in NDSY. destruct NDSY as (NDS & ISY & NDY).
    apply idj_app_r in IXSY. destruct IXSY as [IXS IXY].
    assert (KEEP : forall b, In b ((HLB ++ MB) ++ pa_UB FI AI t ++ LBK) -> In b (lb_keepA FI AI (pa_sok FI AI t) LB_0)).
    { intros b Hb. assert (HIN : In b LB_0) by (apply SUB; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply in_or_app; right; exact Hb]).
      destruct (pa_sok FI AI t) as [ks|] eqn:SOK; cbn [lb_keepA]; [| exact HIN]. apply (in_lb_remove FI AI); [exact HIN|].
      unfold SB in IXS, ISY. cbn [okbA] in IXS, ISY. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - exact (IXS b _ Hb (or_introl eq_refl)).
      - intros E. exact (ISY _ b (or_introl eq_refl) Hb (eq_sym E)). }
    set (LBKp := HLB ++ pa_UB FI AI t ++ LBK).
    assert (KPSUB : bsub FI AI LBKp (lb_keepA FI AI (pa_sok FI AI t) LB_0)).
    { intros b Hb. apply KEEP. unfold LBKp in Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb| right; exact Hb]. }
    unfold H_pparse_seg.ajcallstQ, H_pparse_seg.pregsQ.
    eapply (aj_bind FI AI J).
    { eapply (H_presp.presp_spec_A IC FI AI J AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 (wz 0x8ab08) q') with (st := stc) (lo := lo) (LBK := LBKp) (P := P)
               (cur := pa_cur FI AI t) (A := pa_A FI AI t) (len := pa_len FI AI t) (cap := pa_cap FI AI t) (okm := pa_okm FI AI t) (bs := pa_bs FI AI t)
               (SA := pa_SA FI AI t) (slen := pa_slen FI AI t) (scap := pa_scap FI AI t) (sok := pa_sok FI AI t) (sbs := pa_sbs FI AI t)
               (rm := pa_rm FI AI t) (sc := pa_sc FI AI t) (isreq := pa_isreq FI AI t) (maj := pa_maj FI AI t) (min := pa_min FI AI t)
               (err := pa_err FI AI t) (hack := pa_hack FI AI t) (pos := pa_pos FI AI t) (entp := pa_entp FI AI t) (clen := pa_clen FI AI t) (csz := pa_csz FI AI t) (esp := pa_esp FI AI t)
               (ev := ev) (canary := canary);
        [exact HR| exact RF| exact (fs_call_ok_le FI stc (wz A0_TP) 4%nat 3%nat (fs_call_ok_push FI st stc (wz A0_TP) 4%nat _ FCO LIVEc) ltac:(clear; lia))| exact AE| exact ST| exact CLO| clear - LO QB; lia| exact QAL| clear - QTOP QB; lia| exact MI| exact LVP| exact PHI| exact PAL| exact SHP
         | exact PSC| exact PMSG| exact CUR| exact PRS| exact PVER
         | destruct PSM as (H1 & H2 & H3 & _); split; [exact H1|]; split; [exact H2|]; split; [exact H3|]; split; [exact SCAPB| exact SNUL]
         | exact PCTL
         | apply nd_app in NDX; destruct NDX as (_ & _ & NDM); apply nd_app; split; [exact NDM|]; split; [apply idj_app_l in IXS; exact (proj2 IXS)| exact NDS]
         | exact KPSUB
         | apply (am_budget_le_mono FI AI s_0 LB_0 _ _ (proj1 PBUD)); clear - SCAP0 CURZ LEN CRX; lia
         | exact CLE| exact CLG| exact CLS| exact SHSEP| exact SHFR| exact SHFS
         | apply (shz_sub m _ _ _ _ SHZ); [clear; lia| apply sh_mono; clear - QB; lia]| apply (shr_sub m _ _ _ _ SHR); [clear; lia| pose proof (sh_mono q' q ltac:(clear - QB; lia)); lia]
         | reflexivity]. }
    intros sq LBq msq PO. unfold H_presp.presp_post_A in PO.
    destruct PO as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & stq & r & cur' & sc' & maj' & min' & SA' & slen' & scap' & pos' & sok' & sbs'
                    & -> & MI1 & ST1 & AE1 & RF1 & LIVE1 & APF & HR1 & LBALT & PSC1 & PMSG1 & PRS1 & PVER1 & PSM1 & PCTL1 & (ev' & ERR1) & SHP1 & SHZ1 & SHR1 & RR & CR & SCAPR & SLENB & CASES).
    rewrite ret_pc_even by lia.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1' & SHF2' & PAF & PAFL & PF1 & PF2).
    assert (SHB : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000) by (unfold sh, SHADOW_OFF in *; clear - B1 B2 B4 ACR; split; Z.div_mod_to_equations; lia).
    assert (PSH : P + 504 <= SF \/ SF + 16 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    assert (APF' : apxF FI AI (WPT (pa_okm FI AI t) (pa_A FI AI t) (pa_cap FI AI t)) LBKp q' stc m m1).
    { apply (apxF_weaken FI AI _ _ LBKp LBKp q' q' stc stc m m1 APF); [| clear; lia| intros b Hb; exact Hb| intros g Hg; exact Hg].
      apply WPT_sub; [intros E; destruct (NONE E) as (-> & _ & _); rewrite E in LBS0; split; [reflexivity| exact LBS0]| intros E; destruct (pa_okm FI AI t); [exact LBS0| exfalso; apply E; reflexivity]]. }
    set (OB := HLB ++ pa_UB FI AI t).
    assert (OBp : bsub FI AI OB LBKp) by (intros b Hb; unfold LBKp; unfold OB in Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply in_or_app; left; exact Hb]).
    assert (KSUBp : bsub FI AI LBK LBKp) by (intros b Hb; unfold LBKp; apply in_or_app; right; apply in_or_app; right; exact Hb).
    assert (PSUB : bsub FI AI LBKp LB_0) by (intros b Hb; exact (lb_keepA_sub FI AI _ _ _ (KPSUB b Hb))).
    assert (MSUB : bsub FI AI MB LB_0) by (intros b Hb; apply SUB; apply in_or_app; left; apply in_or_app; right; exact Hb).
    assert (IMO : idj MB OB /\ idj MB LBK).
    { apply nd_app in NDX. destruct NDX as (_ & IHM & _). apply idj_app_l in IXY. destruct IXY as [_ IMY]. apply idj_app_r in IMY. destruct IMY as [IMU IMK].
      split; [apply idj_app_r; split; [apply idj_sym; exact IHM| exact IMU]| exact IMK]. }
    destruct IMO as [IMO IMK].
    pose proof (ekeep_apxF _ WPP MB OB LBKp s_0 LB_0 q' stc m m1 APF' ltac:(clear - CLO LO QB; lia) ltac:(clear - QB; lia) LSUB
                  (WPT_cls (pa_okm FI AI t) (pa_A FI AI t) (pa_cap FI AI t) ltac:(clear - HL; lia)) WPP_ok WPP_in HR MSUB OBp (fun b Hb => PSUB b (OBp b Hb)) KSUBp (fun b Hb => PSUB b (KSUBp b Hb)) IMO IMK SHP1) as EK.
    assert (INV1 : pinvQ q' m1).
    { apply (pinv_stepAF qshadow eq_refl _ LBKp q' m m1 stc stq INV APF'); [| exact LIVEc| exact LIVE1| exact RF1| exact ST1| exact MI1| exact AE1].
      intros Xa n HX Hn. unfold WPT, WPP. destruct (pa_okm FI AI t) as [kA|]; [destruct (SOME ltac:(discriminate)) as (S1 & S2 & S3 & S4 & S5 & S6)|]; cbn [app disjoint_from fst snd];
        clear - HX Hn CLO LO QB PLO PHI B1 B2 FLO FHI SFB SHB PSH ACR HL S1 S2 S5 S6 || clear - HX Hn CLO LO QB PLO PHI B1 B2 FLO FHI SFB SHB PSH ACR; repeat split; try exact I; lia. }
    set (t' := t_resp t cur' sc' maj' min' SA' slen' scap' sok' sbs' pos').
    Ltac djp1 := let PLOx := fresh "PLOx" in pose proof POK as (_ & _ & _ & _ & PLOx & _); unfold WPP; cbn [disjoint_from fst snd]; repeat split; lia.
    assert (PP1 : p_parserA FI AI m1 LBq P t').
    { unfold p_parserA, t', t_resp. cbn [pa_cur pa_A pa_len pa_cap pa_okm pa_bs pa_meth pa_uc pa_rm pa_sc pa_SA pa_slen pa_scap pa_sok pa_sbs pa_isreq pa_maj pa_min
        pa_ns pa_hs pa_X pa_ebw pa_elw pa_err pa_hack pa_pos pa_entp pa_clen pa_csz pa_esp pa_ub pa_UB].
      split; [exact PSC1|]. split; [exact PMSG1|]. split; [clear - CR CUR; lia|].
      split; [exact (ek_methw _ _ m m1 _ EK ltac:(djp1) PMETH)|]. split; [exact (ek_uri _ _ m m1 _ EK ltac:(djp1) PURI)|]. split; [exact PRS1|]. split; [exact PSM1|]. split; [exact PVER1|].
      split; [apply (ek_hlist _ _ m m1 _ _ _ EK PHL); [intros b Hb; unfold OB; apply in_or_app; left; exact Hb| djp1]|].
      split; [exact (ek_ent _ _ m m1 _ _ EK ltac:(djp1) PENT)|]. split; [exact PCTL1|].
      split; [exact (ek_url _ _ m m1 _ EK ltac:(djp1) PURL)| exact UBO]. }
    pose proof (ek_clow_e WPP OB m m1 EK WPP_ok (QX_clow s_0 LB_0 m t QXF) (ex_intro _ ev' ERR1)) as CL1.
    set (SB' := okbA FI AI sok' SA' scap').
    assert (EQB' : pa_blocks FI AI t' = (HLB ++ MB) ++ SB' ++ pa_UB FI AI t) by (unfold pa_blocks, t', t_resp, HLB, MB, SB'; cbn [pa_ns pa_hs pa_okm pa_A pa_cap pa_sok pa_SA pa_scap pa_UB]; rewrite <- !app_assoc; reflexivity).
    assert (EQBK' : pa_blocks FI AI t' ++ LBK = (HLB ++ MB) ++ SB' ++ pa_UB FI AI t ++ LBK) by (unfold pa_blocks, t', t_resp, HLB, MB, SB'; cbn [pa_ns pa_hs pa_okm pa_A pa_cap pa_sok pa_SA pa_scap pa_UB]; rewrite <- !app_assoc; reflexivity).
    assert (EQB0 : pa_blocks FI AI t = (HLB ++ MB) ++ SB ++ pa_UB FI AI t) by (unfold pa_blocks, HLB, MB, SB; rewrite <- !app_assoc; reflexivity).
    assert (ALT : (sok' = pa_sok FI AI t /\ LBq = LB_0 /\ SA' = pa_SA FI AI t /\ scap' = pa_scap FI AI t /\ am_nsec FI AI sq = am_nsec FI AI s_0)
                  \/ (r = 4 /\ exists k', sok' = Some k' /\ LBq = (k', SA', scap' + 1) :: lb_keepA FI AI (pa_sok FI AI t) LB_0 /\ am_nsec FI AI sq = am_nsec FI AI s_0 + nsec1 (scap' + 1))).
    { destruct CASES as [(R4 & _)|(RN & _ & Z1 & Z2 & Z3 & _ & Z4 & _ & Z5)]; [| left; repeat split; assumption].
      destruct LBALT as [Z|Z]; [left; exact Z| right; split; [exact R4| exact Z]]. }
    assert (BOOK : bsub FI AI (pa_blocks FI AI t' ++ LBK) LBq /\ NoDup (map blk_id (pa_blocks FI AI t' ++ LBK)) /\ P1 sq LBq t').
    { assert (CRX' : pa_cur FI AI t_0 <= cur' <= pa_len FI AI t) by (clear - CR CRX; lia).
      destruct ALT as [(-> & -> & -> & -> & NS)|(R4 & k' & -> & -> & NS)].
      - split; [rewrite EQBK'; exact SUB|]. split; [rewrite EQBK'; exact ND|].
        split; [rewrite NS; exact PF|]. split; [exact HS|]. split; [rewrite EQB'; rewrite EQB0 in CNT; exact CNT|]. split; [exact LEN|]. split; [exact CRX'|].
        pose proof (proj2 PBUD _ _ sq (pf_none FI AI _ _) NS) as BX. rewrite NS. exact BX.
      - assert (FRESH : idj [(k', SA', scap' + 1)] ((HLB ++ MB) ++ pa_UB FI AI t ++ LBK)).
        { pose proof (am_blocks_nodup FI AI sq _ m1 HR1) as NDL. apply (nd_cons (k', SA', scap' + 1)) in NDL. destruct NDL as [NIN _].
          intros a b [<-|[]] Hb. exact (NIN _ b (or_introl eq_refl) (KEEP b Hb)). }
        split; [rewrite EQBK'; unfold SB'; cbn [okbA]; intros b Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb];
                [right; apply KEEP; apply in_or_app; left; exact Hb| apply in_app_or in Hb; destruct Hb as [[<-|[]]|Hb]; [left; reflexivity| right; apply KEEP; apply in_or_app; right; exact Hb]]|].
        split; [rewrite EQBK'; unfold SB'; cbn [okbA]; exact (nd_replace _ SB _ _ ND FRESH)|].
        assert (NB : 1 <= scap' + 1 <= 2^26 + 6) by (destruct PSM1 as (_ & _ & SL' & _); pose proof (SLENB R4) as SLB; clear - SL' SLB SCAPR SCAP0 LEN26; lia).
        assert (PF' : pfirst FI AI (am_nsec FI AI s_0) LB_0 (am_nsec FI AI s_0 + nsec1 (scap' + 1)) ((k', SA', scap' + 1) :: lb_keepA FI AI (pa_sok FI AI t) LB_0)
                      /\ (length ((k', SA', (scap' + 1)%Z) :: lb_keepA FI AI (pa_sok FI AI t) LB_0) + length SB <= length LB_0 + 1)%nat).
        { unfold SB. destruct (pa_sok FI AI t) as [ks|] eqn:SOK; cbn [lb_keepA okbA length].
          - split; [apply pf_repl; exact NB|]. destruct PSM as (_ & OWN & _). cbn [mownA] in OWN. destruct OWN as [SIN _].
            pose proof (H_phdr.lb_remove_len FI AI ks LB_0 _ SIN eq_refl) as RL. clear - RL. rewrite !Nat.add_1_r. apply le_n_S. exact RL.
          - split; [apply pf_new; exact NB| clear; rewrite Nat.add_0_r, Nat.add_1_r; apply le_n]. }
        destruct PF' as [PF' LENQ].
        split; [rewrite NS; destruct PF as [N LB|N LB k0 A0 n0 Hn0|N LB k0 k1 A0 n0 Hn0]; exact PF'|]. split; [exact HS|].
        split; [rewrite EQB'; rewrite EQB0 in CNT; rewrite !length_app in *; exact (cnt_arith _ _ _ _ _ _ _ CNT LENQ)|]. split; [exact LEN|]. split; [exact CRX'|].
        pose proof (proj2 PBUD _ _ sq PF' NS) as BX. rewrite NS. exact BX. }
    destruct BOOK as (SUB1 & ND1 & P11).
    assert (QX1 : QX sq LBq m1 t') by (eapply (QX_move WPP _ s_0 LB_0 m t sq LBq m1 t'); [exact QXF| exact EK| exact WPP_ok| exact HR1| exact PP1| reflexivity| exact SUB1| exact ND1| exact CL1]).
    assert (CH1 : fpchain m1 (am_stack_top FI AI) q (bv_unsigned s0) ras) by (destruct EK as (_ & _ & _ & _ & _ & _ & K7 & _); exact (K7 _ _ CH)).
    assert (RR6 : 0 <= r <= 6) by (clear - RR; lia).
    apply aj_cps. apply (retQ 0x8ab08 q' r t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 _ (or_introl eq_refl) RR6).
    - intros R4. apply evt_done.
      apply (hdrJ q' sq LBq m1 t' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ QX1 P11 INV1 CH1).
      destruct CASES as [(_ & PH & _ & _ & _ & OKN)|(RN & _)]; [| exfalso; exact (RN R4)].
      unfold E2, t'. cbn [t_resp pa_pos pa_okm pa_meth pa_entp pa_X pa_len pa_cur].
      split; [exact PH|]. split; [destruct (pa_okm FI AI t) as [kA|]; [exists kA; reflexivity| exfalso; apply OKN; reflexivity]|]. split; [exact M11|]. split; [exact ENTP|]. clear - XB CR. lia.
    - intros RN. apply evt_done. exact (exitJ q' r sq LBq m1 t' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ QX1 (QP_of_P1 sq LBq t' P11) INV1 RR).
  Qed.

  #[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 STACK_MALLOC_3 SET_SHADOW_F5 POK RF0 FCO MWL MID HR0 KSUB0 QTOP GMX WSL HID ZSTAT GLR TRH TRE PBUD CUR0 GERM"] Lemma firstJ : forall q' m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31,
    QX s_0 LB_0 m t_0 -> pinvQ q' m -> fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras -> pp_sideA FI AI t_0 ->
    AJ FI AI J POST (loopstQ q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m) s_0 LB_0.
  Proof.
    intros q' m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 QXF INV CH SIDE.
    assert (P10 : P1 s_0 LB_0 t_0).
    { split; [apply pf_none|]. split; [reflexivity|]. split; [apply le_n|]. split; [reflexivity|]. split; [clear - CUR0; lia|].
      exact (proj2 PBUD _ _ s_0 (pf_none FI AI _ _) eq_refl). }
    pose proof QXF as (_ & PP & _ & _ & _ & _ & SHP & _).
    pose proof PP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PCTL & _).
    pose proof PCTL as (CTLC & _ & _ & PR & _).
    destruct (pctl_split m _ _ _ _ _ _ _ CTLC) as (_ & _ & C448 & _).
    pose proof INV as (_ & _ & MI & _).
    pose proof SIDE as (POS01 & _). unfold POS_REQUEST_LINE_A, POS_RESPONSE_LINE_A in POS01.
    apply aj_cps.
    apply (loopQ q' (pa_pos FI AI t_0) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 m _ MI C448 ltac:(apply (proj1 SHP); clear; lia) PR).
    - intros E0. apply evt_done. destruct (pa_okm FI AI t_0) as [kA|] eqn:OKM.
      + exact (reqlJ q' m t_0 kA _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdrJ QXF P10 INV CH OKM E0 SIDE).
      + exact (reql0J q' s_0 LB_0 m t_0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ QXF (QP_of_P1 s_0 LB_0 t_0 P10) INV OKM).
    - intros E1. apply evt_done. exact (prespJ q' m t_0 _ _ _ _ _ _ _ _ _ _ _ _ _ QXF P10 INV CH SIDE).
    - intros Hx. exfalso. clear - Hx POS01. lia.
    - intros Hx. exfalso. clear - Hx POS01. lia.
    - intros Hx. exfalso. clear - Hx POS01. lia.
  Qed.

  #[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 STACK_MALLOC_3 SET_SHADOW_F5 POK RF0 FCO FE0 MWL MID HR0 KSUB0 QTOP GMX WSL HID ZSTAT GLR TRH TRE PBUD CUR0 GERM"] Lemma pparse_core : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    QX s_0 LB_0 m0 t_0 -> pp_sideA FI AI t_0 -> fpchain m0 (am_stack_top FI AI) q (bv_unsigned s0) ras ->
    stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 ->
    AJ FI AI J POST
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz H_pparse_seg.parser_parse_entryA) fc None m0 (seg_rom asegs))
      s_0 LB_0.
  Proof.
    intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 QXF SIDE CH ST MI AE.
    pose proof QXF as (HR & PP & _ & SUB & ND & _).
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    assert (OSUB : bsub FI AI (pa_blocks FI AI t_0) LB_0) by (intros b Hb; apply SUB; apply in_or_app; left; exact Hb).
    apply aj_cps. apply (prologueQ t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 _ ST MI AE).
    intros q' m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 INV MU WM FK. apply evt_done.
    destruct (ekeep_fk [] [] [] (pa_blocks FI AI t_0) s_0 LB_0 q st m0 m MU WM FK ltac:(clear - LO; lia) (fun g Hg => Hg)
                (fun SW => shw_fkeep0 FI st m0 m P 504 SW FK RF0 PLB) (Forall_nil _) (Forall_nil _) (Forall_nil _) HR
                (fun b Hb => False_ind _ Hb) OSUB KSUB0 (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha)) as [EK HR'].
    apply (firstJ q' m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [| exact INV| destruct EK as (_ & _ & _ & _ & _ & _ & K7 & _); exact (K7 _ _ CH)| exact SIDE].
    eapply (QX_move [] _ s_0 LB_0 m0 t_0 s_0 LB_0 m t_0); [exact QXF| exact EK| apply Forall_nil| exact HR'
      | exact (ek_parser [] _ LB_0 m0 m t_0 EK I (fun b Hb => Hb) PP)| reflexivity| exact SUB| exact ND|].
    exact (ek_clow [] _ m0 m EK (Forall_nil _) I (QX_clow s_0 LB_0 m0 t_0 QXF)).
  Qed.
End PJ.

#[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 STACK_MALLOC_3 SET_SHADOW_F5"] Theorem pparse_spec_A : pparse_stmt_A FI AI J.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB LBK st P lo gmax canary ws mws cslack GL t ras.
  intros HR RF FCO AE ST CLO LO QAL QTOP MI PLB PHI PAL SHWP PP SIDE SUB ND PBUD WSL HID (MWL & MID) GMX GLR GERM STAT ZSTAT SHZ SHR CH TRH TRE ->.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  destruct (lb_geom FI st m P 504 RF PLB) as [PG1 PG2]. pose proof (fsb_ok FI) as (FB1 & _).
  assert (POK : H_pparse_seg.pq_okA FI q lo P st).
  { unfold H_pparse_seg.pq_okA. split; [exact CLO|]. split; [exact LO|]. split; [exact QAL|]. split; [clear - QTOP TK3; lia|].
    split; [clear - PG1 FB1; lia|]. split; [exact PHI|]. split; [exact PAL| exact PLB]. }
  assert (KSUB0 : bsub FI AI LBK LB) by (intros b Hb; apply SUB; apply in_or_app; right; exact Hb).
  pose proof PP as (_ & _ & CUR0 & _).
  eapply (pparse_core q lo P st ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m canary POK RF FCO (am_fsenv FI AI _ _ _ HR) mws MWL MID
            LBK gmax ws cslack ras GL s LB HR KSUB0 QTOP GMX WSL HID ZSTAT GLR t TRH TRE PBUD CUR0 GERM);
    [| exact SIDE| exact CH| exact ST| exact MI| exact AE].
  unfold QX. split; [exact HR|]. split; [exact PP|]. split; [reflexivity|]. split; [exact SUB|]. split; [exact ND|]. split; [exact STAT|].
  split; [exact SHWP|]. split; [exact SHZ|]. split; [exact SHR|]. apply (apxF_refl FI AI).
Qed.
End W.
