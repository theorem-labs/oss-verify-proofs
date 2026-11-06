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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib SegVCx SegDig SegDigOk.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHMB AMEMHB ABR_memB SFPB_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2 S2WalkVC S2WalkVCok.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import S2WalkVCT S2WalkVC2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import S2TabB.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2N Require Import B2N_defs B2N_cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition glow (l : list ST.gatom) : bool := forallb (fun g => Nat.ltb (ST.g_id g) 20) l.

Lemma gholds_gpx_of : forall segs GP E M l, glow l = true -> SG.gholds GP E M l -> SG.gholds (SDG.gpx segs GP) E M l.
Proof.
  intros segs GP E M l HL H. unfold SG.gholds in *. apply Forall_forall. intros g Hg.
  pose proof (proj1 (Forall_forall _ _) H g Hg) as X. pose proof (proj1 (forallb_forall _ _) HL g Hg) as Hl.
  apply Nat.ltb_lt in Hl. unfold SDG.gpx. destruct (Nat.leb 20 (ST.g_id g)) eqn:E20; [apply Nat.leb_le in E20; lia | exact X].
Qed.

Lemma gholds_gpx_to : forall segs GP E M l, glow l = true -> SG.gholds (SDG.gpx segs GP) E M l -> SG.gholds GP E M l.
Proof.
  intros segs GP E M l HL H. unfold SG.gholds in *. apply Forall_forall. intros g Hg.
  pose proof (proj1 (Forall_forall _ _) H g Hg) as X. pose proof (proj1 (forallb_forall _ _) HL g Hg) as Hl.
  apply Nat.ltb_lt in Hl. unfold SDG.gpx in X. destruct (Nat.leb 20 (ST.g_id g)) eqn:E20; [apply Nat.leb_le in E20; lia | exact X].
Qed.

Lemma b2n_glow_T0 : glow (ST.t_ghost T0) = true.
Proof. reflexivity. Qed.
Lemma b2n_glow_ex : forall X, In X (SP.p_ex B2N) -> glow (ST.t_ghost X) = true.
Proof. intros X HX. cbn [SP.p_ex B2N SP.PGH SP.PGX] in HX. destruct HX as [<-|[<-|[<-|[]]]]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma b2n_xpost_low : forall GP hmH hmA E m rom ms,
  SLib.xpostH SG (SDG.gpx SG GP) hmH hmA B2N E m rom ms -> SLib.xpostH SG GP hmH hmA B2N E m rom ms.
Proof.
  intros GP hmH hmA E m rom ms (X & E' & m' & R' & F' & fc' & HX & Hms & Hz & Hrf & Hr & Hk & Hg & R).
  exists X, E', m', R', F', fc'. split; [exact HX|]. split; [exact Hms|]. split; [exact Hz|]. split; [exact Hrf|].
  split; [exact Hr|]. split; [exact Hk|]. split; [exact (gholds_gpx_to SG GP E' m' _ (b2n_glow_ex X HX) Hg) | exact R].
Qed.

Section B2NS.
  Context {rc : runConstT}.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNGh : ExecF.footprint) (st : astate) (LB : list ablock).
  Variables data idxs : list Z.
  Local Notation GP0 := (gp2 SG data idxs).
  Local Notation GP := (SDG.gpx SG (gp2 SG data idxs)).
  Local Notation hmH := (AHMB.hmH AI L RNGh st LB).
  Local Notation hmA := (AHMB.hmA AI LB).
  Local Notation hmC := (AHMB.hmC AI LB).
  Local Notation hmR := AHMB.hmR.
  Local Notation hmF := (AHMB.hmF RNGh).
  Local Notation hmS := (AHMB.hmS L RNGh).

  (* [comment removed for export] *)
  Lemma summ_okHSC_gfree : forall GP1 GP2 S, ST.t_ghost (SP.sm_pre S) = [] -> Forall (fun X => ST.t_ghost X = []) (SP.sm_post S) ->
    SP.summ_okHSC SG GP1 hmH hmA hmC hmR hmF hmS S -> SP.summ_okHSC SG GP2 hmH hmA hmC hmR hmF hmS S.
  Proof.
    intros GP1 GP2 S Hpre Hpost H E M rom ms H1 H2 H3 H4 H5 H6 H7 _.
    assert (G0 : SG.gholds GP1 E M (ST.t_ghost (SP.sm_pre S))) by (rewrite Hpre; apply Forall_nil).
    destruct (H E M rom ms H1 H2 H3 H4 H5 H6 H7 G0) as (ms' & X & E' & M' & Hms & HX & HT & _ & R).
    exists ms', X, E', M'. split; [exact Hms|]. split; [exact HX|]. split; [exact HT|]. split; [|exact R].
    rewrite (proj1 (Forall_forall _ _) Hpost X HX). apply Forall_nil.
  Qed.

  Hypothesis SFPCBS_ok : SP.summ_okHSC SG GP0 hmH hmA hmC hmR hmF hmS SFPCBS.
  Hypothesis PFFCBS_ok : SP.summ_okHSC SG GP0 hmH hmA hmC hmR hmF hmS PFFCBS.

  (* [comment removed for export] *)
  Lemma summ_okH_HSC : forall S, SP.summ_okH SG GP hmH hmA hmC hmR S -> SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS S.
  Proof.
    intros S H E M rom ms H1 H2 H3 _ _ H6 H7 H8.
    destruct (H E M rom ms H1 H2 H3 H6 H7 H8) as (ms' & X & E' & M' & Hms & R).
    exists ms', X, E', M'. split; [exact (SP.fpu_of SG hmF _ _ _ _ Hms) | exact R].
  Qed.

  Lemma b2n_cs : forall S, In S (SP.p_cs B2N) -> SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS S.
  Proof.
    intros S HS. cbn [SP.p_cs B2N SP.PGH SP.PGX] in HS. destruct HS as [<-|[<-|[<-|[<-|[]]]]].
    - exact (summ_okH_HSC _ (ABRB.mcag_ok AI L RNGh st LB GP 0x9b564 ltac:(lia) ltac:(reflexivity))).
    - exact (summ_okH_HSC _ (ABRB.msagp_ok AI L RNGh st LB GP 32 0x9b588 ltac:(lia) ltac:(lia) ltac:(reflexivity))).
    - apply (summ_okHSC_gfree GP0 GP SFPCBS); [reflexivity | cbn; repeat constructor | exact SFPCBS_ok].
    - apply (summ_okHSC_gfree GP0 GP PFFCBS); [reflexivity | cbn; repeat constructor | exact PFFCBS_ok].
  Qed.

  Variable Cnd : env -> Prop.
  Hypothesis HCG : forall E E2, SP.gagree (SP.p_G B2N) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2.
  Hypothesis HCW : forall E, Cnd E -> SP.wins_client hmC E (SP.p_W B2N).
  Hypothesis HCR : forall E, Cnd E -> forall w, In w (SP.p_CR B2N) -> forall z, fst (SP.win_den E w) <= z < snd (SP.win_den E w) -> hmA z.
  Hypothesis HIK : forall E M0, Cnd E -> hmH M0 -> know_ok SG E M0 (SP.p_IK B2N).
  Hypothesis HSTK : forall E, Cnd E -> SP.hs_ok hmS E (SP.p_PS B2N) (SP.p_W B2N).

  Theorem b2n_sound : forall T E M rom ms, In T (SP.p_tm B2N ++ SP.p_xt B2N) -> hmR rom -> SX.aw_genuine E (SP.p_A B2N) -> Cnd E ->
    hmH M -> ST.tm_okF SG T E M rom ms -> SG.gholds GP E M (ST.t_ghost T) ->
    exists ms', ExecF.mstepsF SG (SP.fpu hmF (SP.p_A B2N) E) ms ms' /\ SP.prun_postH SG GP hmH hmA B2N E M rom ms'.
  Proof.
    exact (SP.pcheck_soundHSC SG GP (SDG.gfpx gfp2)
             (SVX.gvc_enrich SVX.bc_enrich (SDG.gsplit SG (wvc_okL SG 1048512 0x236c0)))
             (SDG.gpx_frame SG GP0 gfp2 (gp2_frame SG data idxs))
             (SVX.gvc_enrich_ok SG GP SVX.bc_enrich _ (SVX.bc_enrich_ok SG)
                (SDGok.gsplit_ok SG GP0 _ (wvc_okL_sound SG data idxs 1048512 ltac:(lia) 0x236c0 ltac:(lia) d2v_img_both)))
             hmH hmA hmC hmR (AHMB.HMC_sub AI LB) (AHMB.HMF AI L RNGh st LB) hmF hmS (AHMB.HMS_mono L RNGh)
             B2N B2N_IT 4000 true B2N_hints Cnd
             b2n_cert (SP.itab_ranges_sound SG _) ltac:(intros TA []) b2n_cs HCG HCW HCR HIK HSTK).
  Qed.

  (* [comment removed for export] *)
  Theorem b2n_run : forall T, In T (SP.p_tm B2N ++ SP.p_xt B2N) ->
    forall E m rom R (F : bvmap 5 word) (fc : bv 32), hmR rom -> SX.aw_genuine E (SP.p_A B2N) -> Cnd E -> hmH m ->
    PIosRegs.rfull R -> regs_ok E (ST.t_regs T) R -> know_ok SG E m (ST.t_know T) -> SG.gholds GP E m (ST.t_ghost T) ->
    mem_inv SG m -> frm0 fc ->
    ExecF.evtF SG (SP.fpu hmF (SP.p_A B2N) E) (SLib.xpostH SG GP hmH hmA B2N E m rom) (MS R F (Z_to_bv 64 (ST.t_pc T)) fc None m rom).
  Proof.
    intros T HinT E m rom R F fc HRom HAG HCnd HHM HF HR HK HG MI HZ.
    assert (HT : ST.tm_okF SG T E m rom (MS R F (Z_to_bv 64 (ST.t_pc T)) fc None m rom)).
    { split; [exact HZ|]. split; [exact HF|]. exists R. cbn [ST.tstate s_pc s_regs s_log s_know mem_denot].
      split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK]. }
    destruct (b2n_sound T E m rom _ HinT HRom HAG HCnd HHM HT HG) as (ms' & HmsF & X & E' & m' & HinX & HX & HGX & Hg & Hb & HH & FR).
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
End B2NS.
Print Assumptions b2n_run.
