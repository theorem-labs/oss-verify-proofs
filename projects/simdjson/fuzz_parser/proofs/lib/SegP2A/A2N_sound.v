(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec Mem RunConst FP MState.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanEmbed AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHM AMEMH ABR_mem SFPA_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2 S2WalkVC S2WalkVCok.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import S2WalkVCT S2WalkVC2 S2TabA A2N_defs A2N_cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Section A2NS.
  Context {rc : runConstT}.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNGh : ExecF.footprint) (st : astate) (LB : list ablock).
  Variables data idxs : list Z.
  Local Notation GP := (gp2 SG data idxs).
  Local Notation hmH := (AHM.hmH AI L RNGh st LB).
  Local Notation hmA := (AHM.hmA AI LB).
  Local Notation hmC := (AHM.hmC AI LB).
  Local Notation hmR := AHM.hmR.
  Local Notation hmF := (AHM.hmF RNGh).
  Local Notation hmS := (AHM.hmS L RNGh).
  Hypothesis SFPCAS_ok : SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS SFPCAS.
  Hypothesis PFFCAS_ok : SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS PFFCAS.

  (* [comment removed for export] *)
  Lemma summ_okH_HSC : forall S, SP.summ_okH SG GP hmH hmA hmC hmR S -> SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS S.
  Proof.
    intros S H E M rom ms H1 H2 H3 _ _ H6 H7 H8.
    destruct (H E M rom ms H1 H2 H3 H6 H7 H8) as (ms' & X & E' & M' & Hms & R).
    exists ms', X, E', M'. split; [exact (SP.fpu_of SG hmF _ _ _ _ Hms) | exact R].
  Qed.

  Lemma a2n_cs : forall S, In S (SP.p_cs A2N) -> SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS S.
  Proof.
    intros S HS. cbn [SP.p_cs A2N SP.PGH SP.PGX] in HS. destruct HS as [<-|[<-|[<-|[<-|[]]]]].
    - exact (summ_okH_HSC _ (ABR.mcag_ok AI L RNGh st LB GP 0x9a5d0 ltac:(lia) ltac:(reflexivity))).
    - exact (summ_okH_HSC _ (ABR.msagp_ok AI L RNGh st LB GP 32 0x9a5e0 ltac:(lia) ltac:(lia) ltac:(reflexivity))).
    - exact SFPCAS_ok.
    - exact PFFCAS_ok.
  Qed.

  Variable Cnd : env -> Prop.
  Hypothesis HCG : forall E E2, SP.gagree (SP.p_G A2N) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2.
  Hypothesis HCW : forall E, Cnd E -> SP.wins_client hmC E (SP.p_W A2N).
  Hypothesis HCR : forall E, Cnd E -> forall w, In w (SP.p_CR A2N) -> forall z, fst (SP.win_den E w) <= z < snd (SP.win_den E w) -> hmA z.
  Hypothesis HIK : forall E M0, Cnd E -> hmH M0 -> know_ok SG E M0 (SP.p_IK A2N).
  Hypothesis HSTK : forall E, Cnd E -> SP.hs_ok hmS E (SP.p_PS A2N) (SP.p_W A2N).

  Theorem a2n_sound : forall T E M rom ms, In T (SP.p_tm A2N ++ SP.p_xt A2N) -> hmR rom -> SX.aw_genuine E (SP.p_A A2N) -> Cnd E ->
    hmH M -> ST.tm_okF SG T E M rom ms -> SG.gholds GP E M (ST.t_ghost T) ->
    exists ms', ExecF.mstepsF SG (SP.fpu hmF (SP.p_A A2N) E) ms ms' /\ SP.prun_postH SG GP hmH hmA A2N E M rom ms'.
  Proof.
    exact (SP.pcheck_soundHSC SG GP gfp2 (wvc_okL SG 1048512 0x23640) (gp2_frame SG data idxs)
             (wvc_okL_sound SG data idxs 1048512 ltac:(lia) 0x23640 ltac:(lia) d2v_img_asan)
             hmH hmA hmC hmR (AHM.HMC_sub AI LB) (AHM.HMF AI L RNGh st LB) hmF hmS (AHM.HMS_mono L RNGh) A2N A2N_IT 4000 true A2N_hints Cnd
             a2n_cert (SP.itab_ranges_sound SG _) ltac:(intros TA []) a2n_cs HCG HCW HCR HIK HSTK).
  Qed.

  (* [comment removed for export] *)
  Theorem a2n_run : forall T, In T (SP.p_tm A2N ++ SP.p_xt A2N) ->
    forall E m rom R (F : bvmap 5 word) (fc : bv 32), hmR rom -> SX.aw_genuine E (SP.p_A A2N) -> Cnd E -> hmH m ->
    PIosRegs.rfull R -> regs_ok E (ST.t_regs T) R -> know_ok SG E m (ST.t_know T) -> SG.gholds GP E m (ST.t_ghost T) ->
    mem_inv SG m -> frm0 fc ->
    ExecF.evtF SG (SP.fpu hmF (SP.p_A A2N) E) (SLib.xpostH SG GP hmH hmA A2N E m rom) (MS R F (Z_to_bv 64 (ST.t_pc T)) fc None m rom).
  Proof.
    intros T HinT E m rom R F fc HRom HAG HCnd HHM HF HR HK HG MI HZ.
    assert (HT : ST.tm_okF SG T E m rom (MS R F (Z_to_bv 64 (ST.t_pc T)) fc None m rom)).
    { split; [exact HZ|]. split; [exact HF|]. exists R. cbn [ST.tstate s_pc s_regs s_log s_know mem_denot].
      split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK]. }
    destruct (a2n_sound T E m rom _ HinT HRom HAG HCnd HHM HT HG) as (ms' & HmsF & X & E' & m' & HinX & HX & HGX & Hg & Hb & HH & FR).
    pose proof (ExecF.mstepsF_msteps SG _ _ _ HmsF) as Hms.
    destruct HX as (HZ' & _ & R' & Hms' & HR' & _ & HK'). cbn [ST.tstate s_pc s_regs s_log s_know mem_denot] in Hms', HR', HK'.
    assert (Hms2 : ms' = MS R' (ms_fregs ms') (Z_to_bv 64 (ST.t_pc X)) (ms_fcsr ms') None m' rom).
    { rewrite Hms' at 1. destruct ms'; reflexivity. }
    pose proof (msteps_wrel SG _ _ Hms) as HW. rewrite Hms2 in HW. cbn [ms_mem MS] in HW.
    exists ms'. split; [exact HmsF|].
    exists X, E', m', R', (ms_fregs ms'), (ms_fcsr ms'). split; [exact HinX|]. split; [exact Hms2|]. split; [exact HZ'|].
    split; [rewrite Hms2 in Hms; exact (msteps_rfull SG _ _ Hms HF)|]. split; [exact HR'|]. split; [exact HK'|]. split; [exact HGX|].
    split; [exact Hg|]. split; [exact Hb|]. split; [exact HH|]. split; [exact FR|].
    split; [exact (wrel_wmono SG _ _ HW)|]. split; [exact (wrel_mem_inv SG _ _ HW MI)|].
    exact (wrel_stk SG _ _ HW).
  Qed.
End A2NS.
