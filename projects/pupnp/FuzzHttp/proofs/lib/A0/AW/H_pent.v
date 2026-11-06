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
     H_match_A H_match_X H_UpnpPrintf H_membuffer_delete H2KitA HPrepA H_hlist_view H_phdr_seg H_phdr H_pent_seg H_pent_seg2 H_pent_kit.
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
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation PS := (aps FI AI).
Local Notation hdr := (hdr FI AI).
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Section PJ.
  Variables (q lo P : Z) (st : fsstate FI).
  Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem) (canary : word).
  Hypothesis POK : H_pent_seg.pe_okA FI q lo P st.
  Hypothesis RF0 : RFAKE FI st m0.
  Hypothesis FCO : fs_call_ok FI st (wz A0_TP) 4.
  Hypothesis FE0 : FSENV FI m0.
  Notation F := (H_pent_seg.eF FI st). Notation FL := (H_pent_seg.eFL FI st). Notation SF := (H_pent_seg.eSF FI st).

Local Notation pe_okA := (H_pent_seg.pe_okA FI q lo P st).
Local Notation eF := (H_pent_seg.eF FI st).

Local Notation pscr := (H_pent_seg.pscr FI P st).
Local Notation prestS := (H_pent_seg.prestS FI q st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation pinvS := (H_pent_seg.pinvS FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation pregs := (H_pent_seg.pregs FI q P st gp (wz A0_TP)).
Local Notation dispstA := (H_pent_seg.dispstA FI q P st gp (wz A0_TP) F_ fc).
Local Notation loopstA := (H_pent_seg.loopstA FI q P st gp (wz A0_TP) F_ fc).
Local Notation prologueE := (H_pent_seg.prologueE FI STACK_MALLOC_1 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO FE0).
Local Notation epostA := (H_pent_seg.epostA FI q lo st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc).
Local Notation pWE := (H_pent_seg.pWE FI q lo st).
Local Notation rframeE := (H_pent_seg.rframeE FI q lo st).
Local Notation exitF := (H_pent_seg.exitF FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).

Local Notation blkstA := (H_pent_seg.blkstA FI q P st gp (wz A0_TP) F_ fc).
Local Notation dispE := (H_pent_seg.dispE FI q lo P st gp (wz A0_TP) F_ fc POK).
Local Notation exitstA := (H_pent_seg.exitstA FI q st gp (wz A0_TP) F_ fc).
Local Notation loopE := (H_pent_seg.loopE FI q P st gp (wz A0_TP) F_ fc).
Local Notation retireE := (H_pent_seg.retireE FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation inP := (H_pent_seg.inP P).
Local Notation dj_inP := (H_pent_seg.dj_inP P).
Local Notation pinv_stepP := (H_pent_seg.pinv_stepP FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation pobj_rframe := (H_pent_seg.pobj_rframe FI q lo P st m0 POK RF0).
Local Notation blk4W := (H_pent_seg.blk4W P).
Local Notation blk4E := (H_pent_seg.blk4E FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation pinv_stepSh := (H_pent_seg.pinv_stepSh FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation repoisonE := (H_pent_seg.repoisonE FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation unpoisonE := (H_pent_seg.unpoisonE FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation outX := (H_pent_seg.outX FI).
Local Notation clsX := (H_pent_seg.clsX FI).
Local Notation dj_inPX := (H_pent_seg.dj_inPX FI P).
Local Notation pinv_stepX := (H_pent_seg.pinv_stepX FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation cb_split1E := (H_pent_seg.cb_split1E ra).
Local Notation epostA_mono := (H_pent_seg.epostA_mono FI q lo st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc).
Local Notation xobj_rframe := (H_pent_seg.xobj_rframe FI q lo P st m0 POK RF0).
Local Notation blk2W := (H_pent_seg.blk2W P).
Local Notation blk2post := (H_pent_seg.blk2post FI q lo P st).
Local Notation blk2E := (H_pent_seg.blk2E FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation eframe_facts := (H_pent_seg.eframe_facts FI q lo P st m0 POK RF0).
Local Notation elive := (H_pent_seg.elive FI P st).
Local Notation elive_of := (H_pent_seg.elive_of FI q lo P st m0 POK RF0).
Local Notation pinv_rf := (H_pent_seg.pinv_rf FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Notation inFJ := (H_pent_seg.inFJ FI st).
Local Notation inW3 := (H_pent_seg.inW3 FI P st).
Local Notation dj_W3 := (H_pent_seg.dj_W3 FI P st).
Local Notation app_W3 := (H_pent_seg.app_W3 FI q lo P st m0 POK RF0).
Local Notation fsw_W3 := (H_pent_seg.fsw_W3 FI q lo P st m0 POK RF0).
Local Notation out_W3 := (H_pent_seg.out_W3 FI q lo P st m0 POK RF0).
Local Notation pinv_stepF := (H_pent_seg.pinv_stepF FI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation fj_split := (H_pent_seg.fj_split FI st).
Local Notation fj_join := (H_pent_seg.fj_join FI st).
Local Notation eouts_shw := (H_pent_seg.eouts_shw FI q lo P st m0 POK RF0).
Local Notation txt_okA := (H_pent_seg.txt_okA FI).
Local Notation pctx := (H_pent_seg.pctx q lo P canary).
Local Notation clow_stepW := (H_pent_seg.clow_stepW canary).
Local Notation low_fsW := (H_pent_seg.low_fsW FI q lo P st POK).
Local Notation pctx_stepF := (H_pent_seg.pctx_stepF FI q lo P st m0 POK RF0 canary).
Local Notation pctx_stepP := (H_pent_seg.pctx_stepP FI q lo P st m0 POK RF0 canary).
Local Notation dj_FJER := (H_pent_seg.dj_FJER FI st).
Local Notation evf_ok := (H_pent_seg.evf_ok FI q lo P st m0 POK RF0).
Local Notation pregsG := (H_pent_seg.pregsG FI q P st gp (wz A0_TP)).
Local Notation ajcallstE := (H_pent_seg.ajcallstE FI q P st gp (wz A0_TP) F_ fc).
Local Notation ajretstE := (H_pent_seg.ajretstE FI q P st gp (wz A0_TP) F_ fc).
Local Notation hiER_fsW3 := (H_pent_seg.hiER_fsW3 FI q lo P st m0 POK RF0).
Local Notation blk1aE := (H_pent_seg.blk1aE FI q P st gp (wz A0_TP) F_ fc).
Local Notation blk1bE := (H_pent_seg.blk1bE FI q P st gp (wz A0_TP) F_ fc).
Local Notation blk6aE := (H_pent_seg.blk6aE FI q lo P st gp (wz A0_TP) F_ fc POK).
Local Notation blk6bE := (H_pent_seg.blk6bE FI q lo P st gp (wz A0_TP) F_ fc POK).
Local Notation blk6cW := (H_pent_seg.blk6cW P).
Local Notation blk6cE := (H_pent_seg.blk6cE FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0).
Local Notation blk3cW := (H_pent_seg.blk3cW P).
Local Notation blk3cE := (H_pent_seg.blk3cE FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 canary).
Local Notation blk3W := (H_pent_seg.blk3W FI P st).
Local Notation blk3W_ok := (H_pent_seg.blk3W_ok FI P st).
Local Notation blk3W_fcls := (H_pent_seg.blk3W_fcls FI q lo P st m0 POK RF0).
Local Notation blk3bE := (H_pent_seg.blk3bE FI IC STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary).
Local Notation retstA := (H_pent_seg.retstA FI q st gp (wz A0_TP) F_ fc).
Local Notation blk5W := (H_pent_seg.blk5W P).
Local Notation blk5W_ok := (H_pent_seg.blk5W_ok FI P st).
Local Notation blk5aE := (H_pent_seg.blk5aE FI IC STACK_MALLOC_0 STACK_MALLOC_1 q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 FCO canary).
Local Notation blk5cW := (H_pent_seg.blk5cW P).
Local Notation blk5cE := (H_pent_seg.blk5cE FI q lo P st ra gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 POK RF0 canary).

  Variables (LBK : BL) (isreq maj min rm sc gmax : Z) (ws : list word) (cslack : list byte) (ras : list Z) (GL : list (Z * Z)).
  Variables (s_0 : PS) (LB_0 : BL) (M0 c0 HS0 PH0 NB0 : Z).
  Hypothesis HR0 : RHEAP_A FI AI s_0 LB_0 m0.
  Hypothesis KSUB0 : bsub FI AI LBK LB_0.
  Hypothesis QTOP : q + 64 <= am_stack_top FI AI.
  Hypothesis GMX : 0 < gmax < 2^32.
  Hypothesis WSL : length ws = 66%nat.
  Hypothesis HID : forall i, 0 <= i < 33 -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id < 64.
  Hypothesis ZSTAT : am_static FI AI ZERO_ADDR_A (ZERO_ADDR_A + 32).
  Hypothesis TRACE : In (PC0_MALLOC :: 0x8847c :: 0x8a000 :: bv_unsigned ra :: ras) A0_TRACES.
  Hypothesis GLR : Forall (fun xn : Z * Z => 0x10000 <= fst xn /\ fst xn + snd xn <= 0x609000) GL.
  Hypothesis GERM : H_pent_kit.germ_stmt_A FI AI (H_pent_kit.gstA GL).

Local Notation germ_WA := (H_pent_kit.germ_WA FI AI).
Local Notation germ_post_A := (H_pent_kit.germ_post_A FI AI).
Local Notation germ_stmt_A := (H_pent_kit.germ_stmt_A FI AI).
Local Notation edel1 := (H_pent_kit.edel1 FI AI).
Local Notation edels := (H_pent_kit.edels FI AI).
Local Notation esteps := (H_pent_kit.esteps FI AI).
Local Notation ebud := (H_pent_kit.ebud FI AI).
Local Notation pent_post_A := (H_pent_kit.pent_post_A FI AI).
Local Notation pent_stmt_A := (H_pent_kit.pent_stmt_A FI AI J).
Local Notation esteps_trans := (H_pent_kit.esteps_trans FI AI).
Local Notation esteps_del1 := (H_pent_kit.esteps_del1 FI AI).
Local Notation esteps_hdr1 := (H_pent_kit.esteps_hdr1 FI AI).
Local Notation hbud_mono := (H_pent_kit.hbud_mono FI AI).
Local Notation ebud_hbud := (H_pent_kit.ebud_hbud FI AI).
Local Notation ebud_le_now := (H_pent_kit.ebud_le_now FI AI).
Local Notation hbud_after_lines := (H_pent_kit.hbud_after_lines FI AI).
Local Notation ebud_step := (H_pent_kit.ebud_step FI AI).
Local Notation ebud_mono := (H_pent_kit.ebud_mono FI AI).
Local Notation ebud_same := (H_pent_kit.ebud_same FI AI).
Local Notation pinv_stepA := (H_pent_kit.pinv_stepA FI AI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 POK RF0).
Local Notation stack_shadow_clientE := (H_pent_kit.stack_shadow_clientE FI AI AMS).
Local Notation sh_window_okE := (H_pent_kit.sh_window_okE FI q lo P st POK).
Local Notation imgsh_apxE := (H_pent_kit.imgsh_apxE FI AI AMS q lo P st m0 POK RF0).
Local Notation imgcell_apxE := (H_pent_kit.imgcell_apxE FI AI AMS q lo P st POK).
Local Notation pctx_stepA := (H_pent_kit.pctx_stepA FI AI AMS q lo P st m0 canary POK RF0 LBK).
Local Notation pstat_stepA := (H_pent_kit.pstat_stepA FI AI AMS q lo P st m0 POK RF0).
Local Notation delJ := (H_pent_kit.delJ IC FI AI J AC ASL AMS q lo P st ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary POK RF0).
Local Notation pctl_split := (H_pent_kit.pctl_split P).
Local Notation pctl_join := (H_pent_kit.pctl_join P).
Local Notation ent4_join := (H_pent_kit.ent4_join P).
Local Notation ent4_split := (H_pent_kit.ent4_split P).
Local Notation pctx_of := (H_pent_kit.pctx_of FI AI q lo P canary).
Local Notation aj_cps := (H_pent_kit.aj_cps FI AI J).
Local Notation estat := (H_pent_kit.estat q lo P canary gmax).
Local Notation estat2 := (H_pent_kit.estat2 ws cslack GL).
Local Notation EX := (H_pent_kit.EX FI AI q lo P st m0 canary LBK isreq maj min rm sc gmax s_0 LB_0 M0 c0 HS0 PH0 NB0).
Local Notation EI := (H_pent_kit.EI FI AI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 canary LBK isreq maj min rm sc gmax ws cslack ras GL s_0 LB_0 M0 c0 HS0 PH0 NB0).
Local Notation EX_done := (H_pent_kit.EX_done FI AI q lo P st ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary LBK isreq maj min rm sc gmax s_0 LB_0 M0 c0 HS0 PH0 NB0).
Local Notation wpok := (H_pent_kit.wpok P).
Local Notation ekeep := (H_pent_kit.ekeep FI AI q lo P st LBK).
Local Notation shw_munch_gen := (H_pent_kit.shw_munch_gen ws WSL).
Local Notation dj_wpok_low2 := (H_pent_kit.dj_wpok_low2 FI q lo P st POK ws WSL).
Local Notation dj_wpok_low := (H_pent_kit.dj_wpok_low FI q lo P st POK ws WSL).
Local Notation ek_pcell := (H_pent_kit.ek_pcell FI AI q lo P st LBK).
Local Notation ek_scell := (H_pent_kit.ek_scell FI AI q lo P st POK LBK ws WSL).
Local Notation ek_hlist := (H_pent_kit.ek_hlist FI AI q lo P st LBK ws WSL).
Local Notation ek_pstat := (H_pent_kit.ek_pstat FI AI q lo P st POK LBK gmax ws WSL).
Local Notation ek_clow := (H_pent_kit.ek_clow FI AI q lo P st canary POK LBK ws WSL).
Local Notation ek_stat := (H_pent_kit.ek_stat FI AI q lo P st canary POK LBK gmax ws WSL).
Local Notation ek_stat2 := (H_pent_kit.ek_stat2 FI AI q lo P st LBK ws cslack GL WSL GLR).
Local Notation ecls := (H_pent_kit.ecls FI AI q st).
Local Notation inside_wpok := (H_pent_kit.inside_wpok P ws WSL).
Local Notation inside_dj := (H_pent_kit.inside_dj ws WSL).
Local Notation ekeep_munch := (H_pent_kit.ekeep_munch FI AI ASL AMS q lo P st m0 POK RF0 LBK ws s_0 LB_0 HR0 KSUB0 WSL).
Local Notation apxF_weaken2 := (H_pent_kit.apxF_weaken2 FI AI).
Local Notation blk_not_fclient := (H_pent_kit.blk_not_fclient FI AI ASL q lo P st m0 POK RF0 LBK ws WSL).
Local Notation fcls := (H_pent_kit.fcls FI AI st).
Local Notation ekeep_fk := (H_pent_kit.ekeep_fk FI AI ASL AMS q lo P st m0 POK RF0 LBK ws s_0 LB_0 HR0 KSUB0 WSL).
Local Notation fpchain_keep := (H_pent_kit.fpchain_keep ws WSL).
Local Notation acls := (H_pent_kit.acls FI AI).
Local Notation ekeep_apxF := (H_pent_kit.ekeep_apxF FI AI ASL AMS q lo P st m0 POK RF0 LBK ws WSL).
Local Notation ekeep_trans := (H_pent_kit.ekeep_trans FI AI q lo P st LBK).
Local Notation ekeep_weaken := (H_pent_kit.ekeep_weaken FI AI q lo P st LBK).
Local Notation ekeep_sub := (H_pent_kit.ekeep_sub FI AI q lo P st LBK).
Local Notation ek_meth := (H_pent_kit.ek_meth FI AI q lo P st LBK ws WSL).
Local Notation ek_ent := (H_pent_kit.ek_ent FI AI q lo P st LBK ws WSL).
Local Notation ek_ctl := (H_pent_kit.ek_ctl FI AI q lo P st LBK ws WSL).
Local Notation ek_scan := (H_pent_kit.ek_scan FI AI q lo P st LBK ws WSL).
Local Notation ek_msg := (H_pent_kit.ek_msg FI AI q lo P st LBK ws WSL).
Local Notation EX_move := (H_pent_kit.EX_move FI AI q lo P st m0 canary POK LBK isreq maj min rm sc gmax ws s_0 LB_0 M0 c0 HS0 PH0 NB0 WSL).
Local Notation pWE_cls := (H_pent_kit.pWE_cls FI AI q lo P st POK ws WSL).
Local Notation exitJ := (H_pent_kit.exitJ FI AI J ASL AMS q lo P st ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary POK RF0 LBK isreq maj min rm sc gmax ws s_0 LB_0 M0 c0 HS0 PH0 NB0 HR0 KSUB0 WSL).
Local Notation pWE_clsG := (H_pent_kit.pWE_clsG FI AI q lo P st POK ws WSL).
Local Notation OB_sub := (H_pent_kit.OB_sub FI AI LBK).
Local Notation case4 := (H_pent_kit.case4 FI AI J ASL AMS q lo P st ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary POK RF0 LBK isreq maj min rm sc gmax ws s_0 LB_0 M0 c0 HS0 PH0 NB0 HR0 KSUB0 WSL).
Local Notation case2 := (H_pent_kit.case2 FI AI J ASL AMS q lo P st ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary POK RF0 LBK isreq maj min rm sc gmax ws s_0 LB_0 M0 c0 HS0 PH0 NB0 HR0 KSUB0 WSL).
Local Notation pe_measA_nonneg := (H_pent_kit.pe_measA_nonneg gmax ws GMX WSL).
Local Notation CONT := (H_pent_kit.CONT FI AI J q lo P st ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary LBK isreq maj min rm sc gmax ws cslack ras GL s_0 LB_0 M0 c0 HS0 PH0 NB0).
Local Notation EI_move := (H_pent_kit.EI_move FI AI q lo P st ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 canary POK LBK isreq maj min rm sc gmax ws cslack ras GL s_0 LB_0 M0 c0 HS0 PH0 NB0 GMX WSL GLR).
Local Notation pctx_back := (H_pent_kit.pctx_back FI AI q lo P canary).
Local Notation txt_ok_blk := (H_pent_kit.txt_ok_blk FI AI ws WSL).
Local Notation del_books := (H_pent_kit.del_books FI AI LBK).
Local Notation del_nul := (H_pent_kit.del_nul ws WSL).
Local Notation WP5 := (H_pent_kit.WP5 P).
Local Notation WP5_ok := (H_pent_kit.WP5_ok FI q lo P st POK).
Local Notation WP5_in := (H_pent_kit.WP5_in FI q lo P st POK).
Local Notation del_script := (H_pent_kit.del_script FI AI ws s_0 LB_0 WSL).
Local Notation case5 := (H_pent_kit.case5 IC FI AI J AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 q lo P st ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary POK RF0 FCO LBK isreq maj min rm sc gmax ws cslack ras GL s_0 LB_0 M0 c0 HS0 PH0 NB0 HR0 KSUB0 QTOP GMX WSL GLR).
Local Notation SIX := (H_pent_kit.SIX FI AI P canary LBK).
Local Notation sf_cls := (H_pent_kit.sf_cls FI AI q st ws WSL).
Local Notation six_sf := (H_pent_kit.six_sf FI AI ASL AMS q lo P st m0 canary POK RF0 LBK ws s_0 LB_0 HR0 KSUB0 WSL).
Local Notation repJ := (H_pent_kit.repJ FI AI J ASL AMS q lo P st ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary POK RF0 LBK isreq maj min rm sc gmax ws cslack ras GL s_0 LB_0 M0 c0 HS0 PH0 NB0 HR0 KSUB0 WSL).
Local Notation WP1 := (H_pent_kit.WP1 P).
Local Notation WP3 := (H_pent_kit.WP3 P).
Local Notation WP1_ok := (H_pent_kit.WP1_ok P ws WSL).
Local Notation WP1_in := (H_pent_kit.WP1_in FI q lo P st POK).
Local Notation WP3_ok := (H_pent_kit.WP3_ok FI q lo P st POK ws WSL).
Local Notation blk3W_cls := (H_pent_kit.blk3W_cls FI AI P st ws WSL).
Local Notation case3 := (H_pent_kit.case3 IC FI AI J AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 q lo P st ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary POK RF0 FCO LBK isreq maj min rm sc gmax ws cslack ras GL s_0 LB_0 M0 c0 HS0 PH0 NB0 HR0 KSUB0 QTOP GMX WSL GLR).
Local Notation WPg := (H_pent_kit.WPg P).
Local Notation vblocks := (H_pent_kit.vblocks FI AI).
Local Notation WPg_ok := (H_pent_kit.WPg_ok P ws WSL).
Local Notation WPg_in := (H_pent_kit.WPg_in FI q lo P st POK).
Local Notation hs_pure := (H_pent_kit.hs_pure FI AI).
Local Notation vblocks_sub := (H_pent_kit.vblocks_sub FI AI).
Local Notation germW_cls := (H_pent_kit.germW_cls FI AI P st ws WSL).
Local Notation germW_W3 := (H_pent_kit.germW_W3 FI AI q lo P st POK ws WSL).
Local Notation germW_djF := (H_pent_kit.germW_djF FI AI q lo P st m0 POK RF0 ws WSL).
Local Notation case1 := (H_pent_kit.case1 FI AI J ASL AMS q lo P st ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary POK RF0 FCO LBK isreq maj min rm sc gmax ws cslack ras GL s_0 LB_0 M0 c0 HS0 PH0 NB0 HR0 KSUB0 GMX WSL GLR GERM).
Local Notation ed_del := (H_pent_kit.ed_del FI AI).
Local Notation eds_nil := (H_pent_kit.eds_nil FI AI).
Local Notation eds_cons := (H_pent_kit.eds_cons FI AI).
Local Notation ess_nil := (H_pent_kit.ess_nil FI AI).
Local Notation ess_del := (H_pent_kit.ess_del FI AI).
Local Notation ess_hdr := (H_pent_kit.ess_hdr FI AI).
  Local Notation pinv := (pinvS eshadow).
  Local Notation POST := (pent_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s_0 LB_0 LBK P lo isreq maj min rm sc gmax M0 c0 HS0 PH0 NB0 canary m0).
  Local Notation pe_measA := (pe_meas0 gmax).

  Ltac plia := lazymatch goal with |- ?G => let H := fresh "PL" in assert (H : 0x609000 <= P -> G) by (clear; intros; lia); apply H; exact (proj1 (proj2 (proj2 (proj2 (proj2 POK))))) end.
  Ltac djw := unfold H_pent_seg.blk4W, H_pent_seg.blk2W, H_pent_seg.blk6cW, H_pent_seg.blk3cW, H_pent_seg.blk5cW; cbn [disjoint_from app fst snd]; simpl_sizes; repeat split; plia.
  Ltac wpokP := repeat apply Forall_cons; try apply Forall_nil; left; unfold H_pent_seg.inP; cbn [fst snd]; plia.
  Ltac winP := repeat apply Forall_cons; try apply Forall_nil; unfold H_pent_kit.pent_WA; cbn [inside fst snd]; plia.
  Ltac clsP := repeat (apply Forall_cons; [split; [cbn [fst snd]; plia| do 4 right; left; cbn [inside fst snd]; plia]|]).
  Ltac ekc EK H := apply (ek_pcell _ _ _ _ _ _ EK) in H; [| clear; lia| simpl_sizes; clear; lia| djw].

  #[using="m0 POK RF0 ws WSL"] Lemma pinv_stepAF : forall shd, Z.of_nat (cells_size shd) = 16 -> forall (W : list ivl) (LBc : BL) q' m m2 (stc st' : fsstate FI),
    pinvS shd q' m -> apxF FI AI W LBc q' stc m m2 ->
    (forall X n, (q' <= X \/ (FSB FI <= X /\ X + n <= FSB FI + A0_FS_SIZE /\ (X + n <= P \/ P + 504 <= X)) \/ (SF <= X /\ X + n <= SF + 16)) -> 0 <= n -> disjoint_from W X n) ->
    fs_live FI stc = fs_newff FI st 1 :: fs_live FI st -> fs_live FI st' = fs_live FI stc -> RFAKE FI st' m2 ->
    stk asegs m2 lo q' -> mem_inv asegs m2 -> asan_env asegs m2 ->
    pinvS shd q' m2.
  Proof.
    intros shd HSZ W LBc q' m m2 stc st' (ST & (j0 & j160 & QC) & MI & AE & (QB & QAL) & VR) AP DJW LIVE1 LIVE2 RF2 ST2 MI2 AE2.
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
    unfold H_pent_seg.pinvS, H_pent_seg.prestS.
    split; [exact ST2|].
    split; [exists j0, j160; apply TRS; [clear; lia| exact QC]|].
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

  #[using="ws ras WSL TRACE"] Lemma ra_bigE : 4096 <= bv_unsigned ra.
  Proof.
    pose proof TRACE as T. unfold A0_TRACES in T. cbn [In] in T.
    repeat (destruct T as [T|T]; [first [discriminate T| injection T; intros; lia]|]). destruct T.
  Qed.
  #[using="POK ws QTOP WSL TRACE"] Lemma chain_consE : forall shd q' m, pinvS shd q' m -> fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras ->
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
    split; [split; [rewrite Z_to_bv_bv_unsigned; exact B4| exact RR]|]. split; [exact ra_bigE|].
    exists (bv_unsigned s0). split; [split; [rewrite Z_to_bv_bv_unsigned; exact B3| exact SR]| exact CH].
  Qed.

  Definition WPh : list ivl := [(P + 4, P + 8); (P + 288, P + 344); (P + 448, P + 452); (P + 488, P + 496)]%Z.
  Definition WP6 : list ivl := [(P + 4, P + 8); (P + 288, P + 344); (P + 448, P + 452); (P + 488, P + 496); (P + 400, P + 432); (P + 384, P + 392)]%Z.
  Definition WP6b : list ivl := [(P + 448, P + 452); (P + 488, P + 496); (P + 400, P + 432); (P + 384, P + 392)]%Z.
  #[using="HC FI q lo st POK"] Lemma WPh_ok : Forall wpok WPh. Proof. unfold WPh. wpokP. Qed.
  #[using="HC FI q lo st POK"] Lemma WPh_in : Forall (fun iv : ivl => inside (pent_WA P) (fst iv) (snd iv - fst iv)) WPh. Proof. unfold WPh. winP. Qed.
  #[using="HC FI q lo st POK"] Lemma WP6_ok : Forall wpok WP6. Proof. unfold WP6. wpokP. Qed.
  #[using="ws WSL"] Lemma phW_cls : forall (kA : K) A cap, 0 <= cap -> Forall (acls WPh [(kA, A, cap + 1)]) (phdr_WA P A cap).
  Proof.
    intros kA A cap Hc. unfold H_phdr.phdr_WA, WPh, H_pent_kit.acls.
    repeat apply Forall_cons; try apply Forall_nil; (split; [cbn [fst snd]; lia|]);
      [left; cbn [inside fst snd]; lia| left; cbn [inside fst snd]; lia| left; cbn [inside fst snd]; lia| left; cbn [inside fst snd]; lia|].
    right. exists (kA, A, cap + 1). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia.
  Qed.
  Ltac dj6 := unfold WPh, WP6, WP6b, H_pent_seg.blk6cW; cbn [disjoint_from app fst snd]; simpl_sizes; repeat split; plia.
  Ltac ekc6 EK H := apply (ek_pcell _ _ _ _ _ _ EK) in H; [| clear; lia| simpl_sizes; clear; lia| dj6].
  Ltac wk6 := intros a n; unfold WPh, WP6, WP6b, H_pent_seg.blk6cW; cbn [disjoint_from]; clear; intros; repeat split; try exact I; lia.

  #[using="ws WSL"] Lemma del_scr1 : forall (s s' : PS) (LB LB' : BL) (kA k' : K) A cap A' cap',
    In (kA, A, cap + 1) LB -> 0 <= cap' <= cap ->
    ((k' = kA /\ LB' = LB /\ A' = A /\ cap' = cap /\ am_nsec FI AI s' = am_nsec FI AI s)
     \/ (LB' = (k', A', cap' + 1) :: lb_keepA FI AI (Some kA) LB /\ am_nsec FI AI s' = am_nsec FI AI s + nsec1 (cap' + 1))) ->
    exists k, esteps k 0 (am_nsec FI AI s) LB (am_nsec FI AI s') LB' /\ 0 <= k <= 1 /\ am_nsec FI AI s' - k <= am_nsec FI AI s /\ Z.of_nat (length LB') <= Z.of_nat (length LB).
  Proof.
    intros s s' LB LB' kA k' A cap A' cap' KIN CC [(-> & -> & -> & -> & E)|(-> & E)].
    - exists 0. split; [rewrite E; apply ess_nil| rewrite E; lia].
    - exists 1. split; [| rewrite E; pose proof (nsec1_range (cap' + 1)) as NR; pose proof (H_phdr.lb_remove_len FI AI kA LB _ KIN eq_refl) as RL; cbn [lb_keepA length]; clear - NR RL; lia]. rewrite E. cbn [lb_keepA]. apply esteps_del1. exact (ed_del (am_nsec FI AI s) LB kA k' A A' cap cap' KIN CC).
  Qed.

  #[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 POK RF0 FCO HR0 KSUB0 QTOP GMX WSL HID ZSTAT TRACE"] Lemma case6 : forall q' (s : PS) (LB : BL) m cur A len cap (kA : K) bs eb el err hack pos clen csz esp ns hs X meth x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    EI s LB m q' cur A len cap (Some kA) bs eb el err hack pos 6 clen csz esp ns hs X meth ->
    AJ FI AI J POST (blkstA q' 0x89fec x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m) s LB.
  Proof.
    intros q' s LB m cur A len cap kA bs eb el err hack pos clen csz esp ns hs X meth x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 EIF.
    pose proof EIF as (EXF & INV & XB & ST2 & (BUD & CB & HSS & (k0 & ES0 & K0 & KM & KC & KN)) & CH & EOK).
    pose proof (pe_measA_nonneg _ _ _ _ _ EOK) as MP.
    pose proof (ebud_hbud _ _ _ s LB BUD ltac:(clear - MP; lia)) as HBD.
    pose proof EXF as (HR & PSC & PMSG & CUR & PENT & PCTL & PHL & PMETH & PVER & PRS & SUB & ND & STAT & _ & SCR & HSF).
    pose proof STAT as (SHP & SHSEP & SHF1 & SHF2 & SHZ & SHR & CL & SHE & PST).
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & B5).
    destruct (OB_sub LB ns hs (Some kA) A cap SUB) as [OSUB KSUB].
    assert (HSUB : bsub FI AI (hl_blocks FI AI ns hs) LB) by (intros b Hb; apply SUB; apply in_or_app; left; exact Hb).
    destruct (p_msg_facts FI AI m LB P A len cap (Some kA) bs s HR PMSG) as (HL & HCp & LBS0 & _ & SOME). unfold LMAX_A in HCp.
    destruct (SOME ltac:(discriminate)) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof PMSG as (_ & [KIN _] & _ & _ & NUL).
    pose proof ND as ND0. apply nd_app in ND0. destruct ND0 as (_ & _ & ND2). apply (nd_app (okbA FI AI (Some kA) A cap) LBK) in ND2. destruct ND2 as (_ & ITK & _).
    destruct EOK as (E1 & _). specialize (E1 ltac:(lia)).
    pose proof PCTL as (CTLC & CR1 & CR2 & CR3 & CR4 & CR5 & CR6 & CR7).
    destruct (pctl_split m _ _ _ _ _ _ _ CTLC) as (C440 & C444 & C448 & C452 & C456 & C460 & C464 & C472).
    pose proof PENT as PENT0. unfold p_ent in PENT0. split_chunk PENT0 1%nat C384 C392.
    pose proof INV as (ST & PSCR & MI & AE & (QB & QAL) & VR). destruct VR as (_ & _ & _ & _ & _ & _ & _ & _ & (stc & RF & LIVEc)).
    destruct (elive_of stc LIVEc) as (_ & _ & _ & LVP & LSUB).
    destruct eframe_facts as (FLO & FHI & FAL & FLLO & FLHI & SFB & SHF1' & SHF2' & PAF & PAFL & PF1 & PF2).
    assert (SHB : 0x7fff8000 <= sh (FSB FI) /\ sh (FSB FI) + A0_FS_SHSIZE <= 0x10007fff8000) by (unfold sh, SHADOW_OFF in *; clear - B1 B2 B4 ACR; split; Z.div_mod_to_equations; lia).
    assert (PSH : P + 504 <= SF \/ SF + 16 <= P) by (pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PLB ltac:(lia) ltac:(lia)); lia).
    pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
    destruct ST2 as (PHS & GS).
    apply aj_cps. apply (blk6aE q' cur x1 x5 x6 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m _ PSCR MI SHP PSC). apply evt_done.
    unfold H_pent_seg.ajcallstE, H_pent_seg.pregsG.
    eapply (aj_bind FI AI J).
    { eapply (H_phdr.phdr_spec_A IC FI AI J AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 (wz 0x8a000) q') with (st := stc) (lo := lo) (LBK := LBK) (P := P) (cur := cur) (A := A) (len := len) (cap := cap)
               (kA := kA) (bs := bs) (ns := ns) (hs := hs) (X := X) (meth := meth) (isreq := isreq) (maj := maj) (min := min) (err := err) (hack := hack) (pos := pos) (entp := 6) (clen := clen) (csz := csz) (esp := esp)
               (ws := ws) (cslack := cslack) (ras := bv_unsigned ra :: ras);
        [exact HR| exact RF| exact (fs_call_ok_push FI st stc (wz A0_TP) 3%nat _ FCO LIVEc)| exact AE| exact ST| exact CLO| lia| exact QAL| lia| exact MI| exact LVP| exact PHI| exact PAL| exact SHP| exact PSC| exact PMSG| exact CUR
         | exact PMETH| exact PVER| exact PHL| exact PCTL| exact HSUB| exact KSUB| exact ND| exact XB| exact HBD| exact WSL| exact HID| exact PHS| exact ZSTAT
         | apply (shz_sub m _ _ _ _ SHZ); [lia| apply sh_mono; lia]| apply (shr_sub m _ _ _ _ SHR); [lia| pose proof (sh_mono q' q ltac:(lia)); lia]
         | exact (chain_consE eshadow q' m INV CH)| rewrite unsigned_lit by lia; exact TRACE| reflexivity]. }
    intros sq LBq ms' PO. unfold H_phdr.phdr_post_A in PO.
    destruct PO as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & stq & r & cur' & meth' & pos' & d & ns' & hs'
                    & -> & MI1 & ST1 & AE1 & RF1 & LIVE1 & APF & HR1 & KIN1 & HSUB1 & KSUB1 & ND1 & HLS & DR & PSC1 & PMSG1 & PMETH1 & PVER1 & PHL1 & HSUM1 & HSD1 & CNT1 & CNL1 & PCTL1 & SHP1 & _ & _ & MO & CR & RR & EXR).
    rewrite ret_pc_even by lia.

    pose proof (ekeep_apxF (phdr_WA P A cap) WPh [(kA, A, cap + 1)] [] LBK s LB q' stc m m1 APF ltac:(lia) ltac:(lia) LSUB (phW_cls kA A cap ltac:(lia)) WPh_ok WPh_in HR
                  ltac:(intros b [<-|[]]; exact KIN) (fun b Hb => False_ind _ Hb) (fun b Hb => False_ind _ Hb) (fun b Hb => Hb) KSUB (fun a b Ha Hb => False_ind _ Hb) ITK SHP1) as EKh.
    assert (INV1 : pinv q' m1).
    { apply (pinv_stepAF eshadow eq_refl (phdr_WA P A cap) LBK q' m m1 stc stq INV APF); [| exact LIVEc| exact LIVE1| exact RF1| exact ST1| exact MI1| exact AE1].
      intros Xa n HX Hn. unfold H_phdr.phdr_WA. cbn [disjoint_from]. repeat split; try exact I; lia. }
    assert (SUB1 : bsub FI AI (hl_blocks FI AI ns' hs' ++ okbA FI AI (Some kA) A cap ++ LBK) LBq).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (HSUB1 b Hb)|]. apply in_app_or in Hb. destruct Hb as [[<-|[]]|Hb]; [exact KIN1| exact (KSUB1 b Hb)]. }
    assert (ESH : esteps k0 d (am_nsec FI AI s_0) LB_0 (am_nsec FI AI sq) LBq).
    { replace k0 with (k0 + 0) by (clear; lia). replace d with (0 + d) by (clear; lia). exact (esteps_trans k0 0 _ _ _ _ ES0 0 d _ _ (esteps_hdr1 d _ _ _ _ HLS)). }
    assert (DB : 0 <= d <= c0) by (clear - DR CR CB; lia).
    pose proof (ek_clow _ _ m m1 EKh WPh_ok ltac:(dj6) CL) as CL1.
    pose proof (ek_stat _ _ m m1 EKh WPh_ok STAT CL1) as STAT1.
    pose proof (ek_ent _ _ m m1 _ _ EKh ltac:(dj6) PENT) as PENT1.
    assert (EXF1 : EX sq LBq m1 cur' A len cap (Some kA) bs eb el err hack pos' 6 clen csz esp ns' hs' (X + 2 * (cur' - cur)) meth').
    { eapply (EX_move WPh _ s LB m cur A len cap (Some kA) bs eb el err hack pos 6 clen csz esp ns hs X meth sq LBq m1); [exact EXF| exact EKh| exact WPh_ok
        | dj6| dj6| exact HR1| exact PSC1| exact PMSG1| lia| exact PENT1| exact PCTL1| exact PHL1| exact PMETH1| exact SUB1| exact ND1| exact CL1| exists k0, d; split; [exact ESH| clear - K0 KM KC KN CNT1 CNL1 MP DB; lia]| clear - HSUM1 HSS CB CR CUR; lia]. }
    pose proof PCTL1 as (CTLC1 & _ & _ & PR1 & _).
    destruct (pctl_split m1 _ _ _ _ _ _ _ CTLC1) as (C440q & C444q & C448q & C452q & C456q & C460q & C464q & C472q).
    apply aj_cps.
    apply (blk6bE q' r cur cur' (wz pos') t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 (wz 3) t3 t4 t5 t6 m1 _ (proj1 (proj2 INV1)) QB MI1 SHP1 RR ltac:(lia) ltac:(lia) C448q PSC1).
    -
      intros N4 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z28 z29 z30 z31. apply evt_done.
      apply (exitJ 0x8a1f4 q' r sq LBq m1 cur' A len cap (Some kA) bs eb el err hack pos' 6 clen csz esp ns' hs' (X + 2 * (cur' - cur)) meth'); [discriminate| unfold retire_pc; lia| exact EXF1| exact INV1| | lia| exact N4].
      intros _. split; [intros _; lia|]. split; [intros [Hx|Hx]; discriminate Hx| intros Hx; discriminate Hx].
    -
      intros E4 m2 z5 z6 z7 z13 z14 z15 z16 z17 z28 z29 z30 z31 MU2 WM2 MI2 C448n. apply evt_done.
      destruct (OB_sub LBq ns' hs' (Some kA) A cap SUB1) as [OSUB1 _].
      destruct (ekeep_munch [(P + 448, P + 452)]%Z [(P + 448, P + 452)]%Z [] (hl_blocks FI AI ns' hs' ++ okbA FI AI (Some kA) A cap) sq LBq m1 m2 MU2 WM2) as [EKp HR2];
        [clsP; apply Forall_nil| wpokP| winP| exact HR1| intros b []| exact OSUB1| exact KSUB1| intros a b []| intros a b []|].
      assert (INV2 : pinv q' m2).
      { apply (pinv_stepP eshadow eq_refl q' m1 m2 [(P + 448, P + 452)]%Z INV1 MU2 WM2 MI2). apply Forall_cons; [unfold H_pent_seg.inP; cbn [fst snd]; lia| apply Forall_nil]. }
      Ltac djp := cbn [disjoint_from app fst snd]; simpl_sizes; repeat split; plia.
      pose proof (ek_scan _ _ m1 m2 cur' EKp ltac:(djp) PSC1) as PSC2.
      assert (PMSG2 : p_msg FI AI m2 LBq P A len cap (Some kA) bs) by (apply (ek_msg _ _ LBq m1 m2 A len cap (Some kA) bs EKp ltac:(djp)); [intros b Hb; apply in_or_app; right; exact Hb| exact PMSG1]).
      assert (WPp_ok : Forall wpok [(P + 448, P + 452)]%Z) by wpokP.
      destruct (ek_clow _ _ m1 m2 EKp WPp_ok ltac:(djp) CL1) as (ev2 & CLOW2).
      pose proof (ek_stat _ _ m1 m2 EKp WPp_ok STAT1 (ex_intro _ ev2 CLOW2)) as (SHP2 & SHSEP2 & SHF12 & SHF22 & SHZ2 & SHR2 & _ & SHE2 & PST2).
      destruct (pctx_of sq LBq m2 A len cap kA bs cur' ev2 HR2 PSC2 PMSG2 SHP2 SHSEP2 SHF12 SHF22 SHZ2 SHR2 CLOW2 SHE2) as (CTX2 & TOK2 & KIN2 & _).
      destruct (pinv_rf eshadow q' m2 INV2) as (stc2 & RF2 & LIVE2). destruct (elive_of stc2 LIVE2) as (_ & _ & _ & _ & LSUB2).
      eapply (delJ eshadow eq_refl 0x8a050 q' cur (cur' - cur) A len cap cur' gmax bs kA sq LBq m2); [exact INV2| exact CTX2| exact PST2| exact HR2| exact KIN2| exact QTOP| lia
        | apply (hbud_after_lines (len - cur) _ d s sq LB LBq _ HBD HLS);
            [clear - DR CR; lia
            | pose proof (HCount.cgG_step FI AI hs hs' (am_nsec FI AI sq - am_nsec FI AI s) d ltac:(clear - CNT1; lia) HSD1) as CPL;
              pose proof (H_phdr.p_hlist_cgG FI AI _ _ _ _ _ PHL1) as GP; clear - CPL GP; unfold CG_A, CG_B, CG_SL in *; lia
            | unfold A0_MAXREQ; clear - HCp; lia]| exact HL| lia| lia| lia| apply ret_pc_even; lia|].
      intros sd LB3 m3 A3 len3 cap3 k3 bs3 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 INV3 CTX3 PST3 HR3 KIN3 APX LBC LENC3 CAPLE LENCASES.
      assert (NUL3 : nth_error bs3 (Z.to_nat len3) = Some (Z_to_bv 8 0) /\ len3 - cur <= len - cur' /\ 0 <= cur <= len3).
      { destruct LENCASES as [(L0 & -> & ->)|(_ & LEN3 & FN)]; [split; [rewrite L0 in NUL; exact NUL| clear - L0 CUR CR; lia]|].
        split; [exact (del_nul bs bs3 cur (cur' - cur) len len3 cap LBS0 ltac:(clear - CUR; lia) ltac:(clear - CR; lia) ltac:(clear - CR; lia) ltac:(clear - HL; lia) LEN3 FN)| clear - LEN3 CUR CR; lia]. }
      destruct NUL3 as (NUL3 & LEN3 & CUR3).
      assert (LBC' : (k3 = kA /\ LB3 = LBq /\ A3 = A /\ cap3 = cap) \/ LB3 = (k3, A3, cap3 + 1) :: lb_keepA FI AI (Some kA) LBq) by (destruct LBC as [(Z1 & Z2 & Z3 & Z4 & _)|(Z1 & _)]; [left; auto| right; exact Z1]).
      destruct (del_books sd LBq LB3 m3 ns' hs' kA k3 A cap A3 cap3 HR3 SUB1 ND1 LBC') as (SUB3 & ND3 & KH & KK).
      destruct (del_scr1 sq sd LBq LB3 kA k3 A cap A3 cap3 KIN2 ltac:(lia) LBC) as (kd & ES3 & KD).
      assert (ESF : esteps (k0 + kd) d (am_nsec FI AI s_0) LB_0 (am_nsec FI AI sd) LB3).
      { replace d with (d + 0) by (clear; lia). exact (esteps_trans k0 d _ _ _ _ ESH kd 0 _ _ ES3). }
      destruct (OB_sub LB3 ns' hs' (Some k3) A3 cap3 SUB3) as [OSUB3 KSUB3].
      pose proof CTX3 as (PSC3c & MBC3 & _ & SHP3 & _).
      pose proof (ekeep_apxF [(P + 400, P + 400 + 32)]%Z [(P + 400, P + 400 + 32)]%Z [] (hl_blocks FI AI ns' hs') (lb_keepA FI AI (Some kA) LBq) sq LBq q' stc2 m2 m3
                    (apxF_of_apx FI AI _ _ _ q' q' stc2 stc2 m2 m2 m3 APX RF2 ltac:(lia) (fun b Hb => Hb) (fun g Hg => Hg)) ltac:(lia) ltac:(lia) LSUB2
                    ltac:(repeat apply Forall_cons; try apply Forall_nil; split; [cbn [fst snd]; lia| left; cbn [inside fst snd]; lia]) ltac:(wpokP) ltac:(winP) HR2
                    (fun b Hb => False_ind _ Hb) KH HSUB1 KK KSUB1 (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha) SHP3) as EK2.
      pose proof (txt_ok_blk sd LB3 m3 k3 A3 len3 cap3 HR3 KIN3 LENC3 ltac:(unfold LMAX_A; lia)) as TOK3.
      pose proof TOK3 as (T1 & T2 & _).
      pose proof C384 as C384'. ekc6 EKh C384'. ekc EKp C384'. ekc EK2 C384'.
      pose proof C472q as C472'. ekc EKp C472'. ekc EK2 C472'.
      apply aj_cps. eapply evt_mono.
      { exact (blk6cE q' A3 len3 cap3 cur cur' esp eb w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m3 INV3 SHP3 CR7 ltac:(lia) ltac:(lia) C384' MBC3 C472' PSC3c). }
      intros ms4 (r0 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m4 & st4 & -> & MI4 & LIVE4 & RF4 & ST4 & AE4 & (MU4 & WM4 & C384n & MBC4 & _ & PSC4) & ->).
      apply (aj_ret FI AI J).
      destruct (ekeep_munch (blk6cW ++ pWE) blk6cW [] (hl_blocks FI AI ns' hs' ++ okbA FI AI (Some k3) A3 cap3) sd LB3 m3 m4 MU4 WM4) as [EK4 HR4];
        [apply Forall_app; split; [unfold H_pent_seg.blk6cW; clsP; apply Forall_nil| apply pWE_clsG]| unfold H_pent_seg.blk6cW; wpokP| unfold H_pent_seg.blk6cW; winP| exact HR3
         | intros b []| exact OSUB3| exact KSUB3| intros a b []| intros a b []|].

      assert (HLSUB : forall okx, bsub FI AI (hl_blocks FI AI ns' hs') (hl_blocks FI AI ns' hs' ++ okx)) by (intros okx b Hb; apply in_or_app; left; exact Hb).
      pose proof (ekeep_trans WP6b _ m1 m2 m4 (ekeep_weaken _ WP6b _ m1 m2 (ekeep_sub _ _ (hl_blocks FI AI ns' hs') m1 m2 EKp (HLSUB _)) ltac:(wk6))
                    (ekeep_trans WP6b _ m2 m3 m4 (ekeep_weaken _ WP6b _ m2 m3 EK2 ltac:(wk6)) (ekeep_weaken _ WP6b _ m3 m4 (ekeep_sub _ _ (hl_blocks FI AI ns' hs') m3 m4 EK4 (HLSUB _)) ltac:(wk6)))) as EKb.
      pose proof (ekeep_trans WP6 [] m m1 m4 (ekeep_weaken _ WP6 _ m m1 EKh ltac:(wk6)) (ekeep_weaken _ WP6 _ m1 m4 (ekeep_sub _ _ [] m1 m4 EKb (fun b Hb => False_ind _ Hb)) ltac:(wk6))) as EK.
      destruct (pctx_back LB3 m3 A3 len3 cap3 cur' bs3 k3 CTX3 KIN3 LENC3 ltac:(unfold LMAX_A; lia) NUL3) as (_ & PMSG3 & CL3).
      pose proof C392 as C392'. ekc6 EK C392'. join_chunks C384n C392' PENT4.
      pose proof C440q as C440'. ekc6 EKb C440'. pose proof C444q as C444'. ekc6 EKb C444'. pose proof C452q as C452'. ekc6 EKb C452'. pose proof C456q as C456'. ekc6 EKb C456'.
      pose proof C460q as C460'. ekc6 EKb C460'. pose proof C464q as C464'. ekc6 EKb C464'. pose proof C472q as C472n. ekc6 EKb C472n.
      ekc EK2 C448n. ekc EK4 C448n.
      pose proof (pctl_join m4 err hack 4 6 clen csz esp C440' C444' C448n C452' C456' C460' C464' C472n) as CTL4.
      eapply (EX_done sd LB3 m4 st4 cur A3 len3 cap3 (Some k3) bs3 _ _ err hack 4 6 clen csz esp ns' hs' (X + 2 * (cur' - cur)) meth' 0); [discriminate| | exact MI4| exact ST4| exact AE4| exact RF4| exact LIVE4| | lia| lia].
      + eapply (EX_move WP6 _ s LB m cur A len cap (Some kA) bs eb el err hack pos 6 clen csz esp ns hs X meth sd LB3 m4); [exact EXF| exact EK| exact WP6_ok
          | dj6| dj6| exact HR4| exact PSC4
          | split; [exact MBC4|]; destruct (ek_msg _ _ LB3 m3 m4 A3 len3 cap3 (Some k3) bs3 EK4 ltac:(djw) ltac:(intros b Hb; apply in_or_app; right; exact Hb) PMSG3) as (_ & OWN' & R'); split; [exact OWN'| exact R']
          | exact CUR3| exact PENT4
          | split; [exact CTL4| repeat (split; [first [assumption| clear; lia]|]); assumption]
          | apply (ek_hlist _ _ m1 m4 ns' hs' _ EKb PHL1); [intros b Hb; exact Hb| dj6]
          | exact (ek_meth _ _ m1 m4 meth' EKb ltac:(dj6) PMETH1)
          | exact SUB3| exact ND3
          | exact (ek_clow _ _ m3 m4 EK4 ltac:(unfold H_pent_seg.blk6cW; wpokP) ltac:(djw) CL3)
          | exists (k0 + kd), d; split; [exact ESF| clear - K0 KM KC KN CNT1 CNL1 MP DB KD; lia]| clear - HSUM1 HSS CB CR CUR; lia].
      + intros _. split; [intros _; lia|]. split; [intros [Hx|Hx]; discriminate Hx| intros Hx; discriminate Hx].
  Qed.

  #[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 POK RF0 FCO HR0 KSUB0 QTOP GMX WSL HID ZSTAT TRACE GLR GERM"] Lemma loopJ : forall (n : nat) (s : PS) (LB : BL) m q' cur A len cap (kA : K) bs eb el err hack pos entp clen csz esp ns hs X meth
      x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31,
    EI s LB m q' cur A len cap (Some kA) bs eb el err hack pos entp clen csz esp ns hs X meth -> pe_measA entp el < Z.of_nat n ->
    AJ FI AI J POST (dispstA q' x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m) s LB.
  Proof.
    induction n as [|n IH]; intros s LB m q' cur A len cap kA bs eb el err hack pos entp clen csz esp ns hs X meth
                                  x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 EIF HM.
    { exfalso. pose proof EIF as (_ & _ & _ & _ & _ & _ & EOK). pose proof (pe_measA_nonneg _ _ _ _ _ EOK). lia. }
    assert (HCN : CONT (pe_measA entp el)).
    { unfold H_pent_kit.CONT. intros sx LBx mx qx curx Ax lenx capx kx bsx ebx elx errx hackx posx entpx clenx cszx espx nsx hsx Xx methx
                                     z1 z5 z6 z10 z11 z12 z13 z14 z15 z16 z17 z26 z28 z29 z30 z31 EIX HMX.
      eapply (IH sx LBx mx qx curx Ax lenx capx kx bsx ebx elx errx hackx posx entpx clenx cszx espx nsx hsx Xx methx); [exact EIX| lia]. }
    pose proof EIF as (EXF & INV & _ & _ & _ & _ & EOK).
    pose proof EXF as (_ & _ & _ & _ & _ & PCTL & _ & _ & _ & _ & _ & _ & (SHP & _) & _).
    pose proof PCTL as (CTLC & _ & _ & _ & ER & _).
    destruct (pctl_split m _ _ _ _ _ _ _ CTLC) as (_ & _ & _ & C452 & _).
    pose proof INV as (_ & PSCR & MI & _).
    assert (ACC : acc m (P + 452 + 4 - 1)) by (apply (proj1 SHP); lia).
    destruct (Z.eq_dec entp 0) as [E0|NZ].
    - subst entp. apply aj_cps.
      apply (H_pent_seg2.dispXE FI q lo P st gp (wz A0_TP) F_ fc POK q' x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m _ PSCR MI C452 ACC).
      intros z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z28 z29 z30 z31. apply evt_done.
      apply (exitJ 0x8a1f4 q' 3 s LB m cur A len cap (Some kA) bs eb el err hack pos 0 clen csz esp ns hs X meth); [discriminate| unfold retire_pc; lia| exact EXF| exact INV| intros Hx; exfalso; apply Hx; reflexivity| lia| lia].
    - apply aj_cps.
      apply (dispE q' entp x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m _ PSCR MI C452 ACC ltac:(lia)).
      intros z1 z5 z6 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31. apply evt_done.
      assert (CASES : entp = 1 \/ entp = 2 \/ entp = 3 \/ entp = 4 \/ entp = 5 \/ entp = 6) by lia.
      destruct CASES as [->|[->|[->|[->|[->| ->]]]]]; unfold H_pent_seg.pjt_tgt; cbn [Z.eqb Pos.eqb].
      + exact (case1 q' s LB m cur A len cap kA bs eb el err hack pos clen csz esp ns hs X meth z1 z5 z6 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 HCN EIF).
      + exact (case2 q' s LB m cur A len cap (Some kA) bs eb el err hack pos clen csz esp ns hs X meth z1 z5 z6 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 ltac:(discriminate) EXF INV EOK).
      + exact (case3 q' s LB m cur A len cap kA bs eb el err hack pos clen csz esp ns hs X meth z1 z5 z6 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 HCN EIF).
      + exact (case4 q' s LB m cur A len cap (Some kA) bs eb el err hack pos clen csz esp ns hs X meth z1 z5 z6 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 ltac:(discriminate) EXF INV EOK).
      + exact (case5 q' s LB m cur A len cap kA bs eb el err hack pos clen csz esp ns hs X meth z1 z5 z6 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 HCN EIF).
      + exact (case6 q' s LB m cur A len cap kA bs eb el err hack pos clen csz esp ns hs X meth z1 z5 z6 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 EIF).
  Qed.

  #[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2 POK RF0 FCO FE0 HR0 KSUB0 QTOP GMX WSL HID ZSTAT TRACE GLR GERM"] Lemma pent_core : forall cur A len cap (kA : K) bs eb el err hack pos entp clen csz esp ns hs X meth (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    EX s_0 LB_0 m0 cur A len cap (Some kA) bs eb el err hack pos entp clen csz esp ns hs X meth ->
    X + 2 * (len - cur) <= 2^27 + 64 -> estat2 m0 -> ebud (pe_measA entp el + 1) (len - cur) (HCount.cgG FI AI hs) s_0 LB_0 -> pe_measA entp el <= M0 -> len - cur <= c0 -> H_phdr.hsumA FI AI hs <= HS0 ->
    5 * am_nsec FI AI s_0 <= PH0 + HCount.phiH FI AI hs -> Z.of_nat (length LB_0) <= NB0 + 4 * Z.of_nat (length hs) ->
    fpchain m0 (am_stack_top FI AI) q (bv_unsigned s0) ras -> ent_okA gmax entp cur esp csz el ->
    stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 ->
    AJ FI AI J POST
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz H_pent_seg.parse_entity_entryA) fc None m0 (seg_rom asegs))
      s_0 LB_0.
  Proof.
    intros cur A len cap kA bs eb el err hack pos entp clen csz esp ns hs X meth t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EXF XB ST2 BUD MB0 CB0 HSS0 PHS0 NBS0 CH EOK ST MI AE.
    pose proof EXF as (HR & PSC & PMSG & CUR & PENT & PCTL & PHL & PMETH & _ & _ & SUB & ND & (SHP & _ & _ & _ & _ & _ & CL & _) & _ & SCR & HSF).
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB).
    destruct (OB_sub LB_0 ns hs (Some kA) A cap SUB) as [OSUB KSUB].
    apply aj_cps. apply (prologueE t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 _ ST MI AE).
    intros q' m x1 x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 INV MU WM FK. apply evt_done.
    destruct (ekeep_fk [] [] [] (hl_blocks FI AI ns hs ++ okbA FI AI (Some kA) A cap) s_0 LB_0 q st m0 m MU WM FK ltac:(lia) (fun g Hg => Hg)
                (fun SW => shw_fkeep0 FI st m0 m P 504 SW FK RF0 PLB) (Forall_nil _) (Forall_nil _) (Forall_nil _) HR
                (fun b Hb => False_ind _ Hb) OSUB KSUB (fun a b Ha => False_ind _ Ha) (fun a b Ha => False_ind _ Ha)) as [EK HR'].
    eapply (loopJ (Z.to_nat (pe_measA entp el + 1)) s_0 LB_0 m q' cur A len cap kA bs eb el err hack pos entp clen csz esp ns hs X meth);
      [| pose proof (pe_measA_nonneg _ _ _ _ _ EOK); lia].
    unfold H_pent_kit.EI. split; [| split; [exact INV| split; [exact XB| split; [exact (ek_stat2 _ _ m0 m EK ST2)| split; [split; [exact BUD| split; [exact CB0| split; [exact HSS0| exists 0; split; [apply ess_nil| split; [lia| split; [lia| split; [clear - PHS0; lia| exact NBS0]]]]]]]| split; [| exact EOK]]]]]].
    - eapply (EX_move [] _ s_0 LB_0 m0 cur A len cap (Some kA) bs eb el err hack pos entp clen csz esp ns hs X meth s_0 LB_0 m);
        [exact EXF| exact EK| apply Forall_nil| exact I| exact I| exact HR'
         | exact (ek_scan _ _ m0 m cur EK I PSC)
         | apply (ek_msg _ _ LB_0 m0 m A len cap (Some kA) bs EK I); [intros b Hb; apply in_or_app; right; exact Hb| exact PMSG]
         | exact CUR
         | exact (ek_ent _ _ m0 m eb el EK I PENT)
         | exact (ek_ctl _ _ m0 m _ _ _ _ _ _ _ EK I PCTL)
         | apply (ek_hlist _ _ m0 m ns hs X EK PHL); [intros b Hb; apply in_or_app; left; exact Hb| exact I]
         | exact (ek_meth _ _ m0 m meth EK I PMETH)
         | exact SUB| exact ND
         | exact (ek_clow _ _ m0 m EK (Forall_nil _) I CL)
         | exact SCR| exact HSF].
    - destruct EK as (_ & _ & _ & _ & _ & _ & K7 & _). exact (K7 _ _ CH).
  Qed.
End PJ.

#[using="IC AC ASL AMS STACK_MALLOC_0 STACK_MALLOC_1 STACK_MALLOC_2"] Theorem pent_spec_A : forall (GL : list (Z * Z)),
  Forall (fun xn : Z * Z => 0x10000 <= fst xn /\ fst xn + snd xn <= 0x609000) GL -> H_pent_kit.germ_stmt_A FI AI (H_pent_kit.gstA GL) -> H_pent_kit.pent_stmt_A FI AI J GL.
Proof.
  intros GL GLR GERM ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB LBK st
         P lo cur A len cap kA bs ns hs X meth isreq maj min rm sc err hack pos entp clen csz esp gmax eb el ev canary ws cslack ras.
  intros HR RF FCO AE ST CLO LO QAL QTOP MI PLB PHI PAL SHWP PSC PMSG HCUR PENT PCTL PHL PMETH PVER PRS SUB ND XB BUD EOK GMX PST CLOW SHE GS SHSEP SHF1 SHF2 WSL HID STAT ZSTAT SHZ SHR CH TRACE ->.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  destruct (lb_geom FI st m P 504 RF PLB) as [PG1 PG2]. pose proof (fsb_ok FI) as (FB1 & _).
  assert (POK : H_pent_seg.pe_okA FI q lo P st).
  { unfold H_pent_seg.pe_okA. split; [exact CLO|]. split; [exact LO|]. split; [exact QAL|]. split; [clear - QTOP TK3; lia|].
    split; [clear - PG1 FB1; lia|]. split; [exact PHI|]. split; [exact PAL| exact PLB]. }
  assert (KSUB0 : bsub FI AI LBK LB) by (intros b Hb; apply SUB; apply in_or_app; right; apply in_or_app; right; exact Hb).
  eapply (pent_core q lo P st ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m canary POK RF FCO (am_fsenv FI AI _ _ _ HR)
            LBK isreq maj min rm sc gmax ws cslack ras GL s LB (H_pent_kit.pe_meas0 gmax entp el) (len - cur) (H_phdr.hsumA FI AI hs) (5 * am_nsec FI AI s - HCount.phiH FI AI hs) (Z.of_nat (length LB) - 4 * Z.of_nat (length hs)) HR KSUB0 QTOP GMX WSL HID ZSTAT TRACE GLR GERM
            cur A len cap kA bs eb el err hack pos entp clen csz esp ns hs X meth);
    [| exact XB| split; [exact STAT| exact GS]| exact BUD| lia| lia| lia| clear; lia| clear; lia| exact CH| exact EOK| exact ST| exact MI| exact AE].
  unfold H_pent_kit.EX. split; [exact HR|]. split; [exact PSC|]. split; [exact PMSG|]. split; [exact HCUR|]. split; [exact PENT|]. split; [exact PCTL|].
  split; [exact PHL|]. split; [exact PMETH|]. split; [exact PVER|]. split; [exact PRS|]. split; [exact SUB|]. split; [exact ND|].
  split; [unfold H_pent_kit.estat; split; [exact SHWP|]; split; [exact SHSEP|]; split; [exact SHF1|]; split; [exact SHF2|]; split; [exact SHZ|]; split; [exact SHR|];
          split; [exists ev; exact CLOW|]; split; [exact SHE| exact PST]|].
  split; [apply (apxF_refl FI AI)|]. assert (MP : 0 <= H_pent_kit.pe_meas0 gmax entp el).
  { destruct EOK as (_ & E2 & _). unfold H_pent_kit.pe_meas0. destruct (entp =? 1) eqn:Q1; [lia|].
    destruct (entp =? 3) eqn:Q3; [apply Z.eqb_eq in Q3; destruct (E2 (or_introl Q3)) as (elen & -> & R); rewrite unsigned_lit by lia; lia|].
    destruct (entp =? 5) eqn:Q5; [apply Z.eqb_eq in Q5; destruct (E2 (or_intror Q5)) as (elen & -> & R); rewrite unsigned_lit by lia; lia| lia]. }
  split; [exists 0, 0; split; [apply H_pent_kit.ess_nil|]; clear - MP HCUR; lia| clear - HCUR; lia].
Qed.

End W.
