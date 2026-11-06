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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHM SFPA_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA2 Require Import A2_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Section A2R.
  Context {rc : runConstT}.
  Variable AI : AMallocIface.

  (* [comment removed for export] *)
  Definition A2SOUND_T : Prop :=
    forall (L : alayout) (RNGh : ExecF.footprint) (st : astate) (LB : list ablock) (data idxs : list Z),
    SP.summ_okHSC SG (gp2 SG data idxs) (AHM.hmH AI L RNGh st LB) (AHM.hmA AI LB) (AHM.hmC AI LB) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh) SFPAS ->
    SP.summ_okHSC SG (gp2 SG data idxs) (AHM.hmH AI L RNGh st LB) (AHM.hmA AI LB) (AHM.hmC AI LB) AHM.hmR (AHM.hmF RNGh) (AHM.hmS L RNGh) PFFAS ->
    forall Cnd : env -> Prop,
    (forall E E2, SP.gagree (SP.p_G A2) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2) ->
    (forall E, Cnd E -> SP.wins_client (AHM.hmC AI LB) E (SP.p_W A2)) ->
    (forall E, Cnd E -> forall w, In w (SP.p_CR A2) -> forall z, fst (SP.win_den E w) <= z < snd (SP.win_den E w) -> AHM.hmA AI LB z) ->
    (forall E M0, Cnd E -> AHM.hmH AI L RNGh st LB M0 -> know_ok SG E M0 (SP.p_IK A2)) ->
    (forall E, Cnd E -> SP.hs_ok (AHM.hmS L RNGh) E (SP.p_PS A2) (SP.p_W A2)) ->
    forall T E M rom ms, In T (SP.p_tm A2 ++ SP.p_xt A2) -> AHM.hmR rom -> SX.aw_genuine E (SP.p_A A2) -> Cnd E ->
    AHM.hmH AI L RNGh st LB M -> ST.tm_okF SG T E M rom ms -> SG.gholds (gp2 SG data idxs) E M (ST.t_ghost T) ->
    exists ms', ExecF.mstepsF SG (SP.fpu (AHM.hmF RNGh) (SP.p_A A2) E) ms ms'
             /\ SP.prun_postH SG (gp2 SG data idxs) (AHM.hmH AI L RNGh st LB) (AHM.hmA AI LB) A2 E M rom ms'.

  Hypothesis A2SOUND : A2SOUND_T.
  Variables (L : alayout) (RNGh : ExecF.footprint) (st : astate) (LB : list ablock).
  Variables data idxs : list Z.
  Local Notation GP := (gp2 SG data idxs).
  Local Notation hmH := (AHM.hmH AI L RNGh st LB).
  Local Notation hmA := (AHM.hmA AI LB).
  Local Notation hmC := (AHM.hmC AI LB).
  Local Notation hmR := AHM.hmR.
  Local Notation hmF := (AHM.hmF RNGh).
  Local Notation hmS := (AHM.hmS L RNGh).
  Hypothesis SFPAS_ok : SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS SFPAS.
  Hypothesis PFFAS_ok : SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS PFFAS.
  Variable Cnd : env -> Prop.
  Hypothesis HCG : forall E E2, SP.gagree (SP.p_G A2) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2.
  Hypothesis HCW : forall E, Cnd E -> SP.wins_client hmC E (SP.p_W A2).
  Hypothesis HCR : forall E, Cnd E -> forall w, In w (SP.p_CR A2) -> forall z, fst (SP.win_den E w) <= z < snd (SP.win_den E w) -> hmA z.
  Hypothesis HIK : forall E M0, Cnd E -> hmH M0 -> know_ok SG E M0 (SP.p_IK A2).
  Hypothesis HSTK : forall E, Cnd E -> SP.hs_ok hmS E (SP.p_PS A2) (SP.p_W A2).

  (* [comment removed for export] *)
  Theorem a2_run : forall T, In T (SP.p_tm A2 ++ SP.p_xt A2) ->
    forall E m rom R (F : bvmap 5 word) (fc : bv 32), hmR rom -> SX.aw_genuine E (SP.p_A A2) -> Cnd E -> hmH m ->
    PIosRegs.rfull R -> regs_ok E (ST.t_regs T) R -> know_ok SG E m (ST.t_know T) -> SG.gholds GP E m (ST.t_ghost T) ->
    mem_inv SG m -> frm0 fc ->
    ExecF.evtF SG (SP.fpu hmF (SP.p_A A2) E) (SLib.xpostH SG GP hmH hmA A2 E m rom) (MS R F (Z_to_bv 64 (ST.t_pc T)) fc None m rom).
  Proof using All.
    intros T HinT E m rom R F fc HRom HAG HCnd HHM HF HR HK HG MI HZ.
    assert (HT : ST.tm_okF SG T E m rom (MS R F (Z_to_bv 64 (ST.t_pc T)) fc None m rom)).
    { split; [exact HZ|]. split; [exact HF|]. exists R. cbn [ST.tstate s_pc s_regs s_log s_know mem_denot].
      split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK]. }
    destruct (A2SOUND L RNGh st LB data idxs SFPAS_ok PFFAS_ok Cnd HCG HCW HCR HIK HSTK T E m rom _ HinT HRom HAG HCnd HHM HT HG)
      as (ms' & HmsF & X & E' & m' & HinX & HX & HGX & Hg & Hb & HH & FR).
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
End A2R.
