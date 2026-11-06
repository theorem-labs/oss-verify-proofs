(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore CatSim.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec Mem RunConst.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import AsanEmbed AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegVCx.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHMB SFPB_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2 S2WalkVC S2WalkVCok.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import S2WalkVCT S2WalkVC2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require Import S2TabB B2_defs B2_cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Section B2S.
  Context {rc : runConstT}.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNGh : ExecF.footprint) (st : astate) (LB : list ablock).
  Variables data idxs : list Z.
  Local Notation GP := (gp2 SG data idxs).
  Local Notation hmH := (AHMB.hmH AI L RNGh st LB).
  Local Notation hmA := (AHMB.hmA AI LB).
  Local Notation hmC := (AHMB.hmC AI LB).
  Local Notation hmR := AHMB.hmR.
  Local Notation hmF := (AHMB.hmF RNGh).
  Local Notation hmS := (AHMB.hmS L RNGh).
  Hypothesis SFPBS_ok : SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS SFPBS.
  Hypothesis PFFBS_ok : SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS PFFBS.

  Lemma b2_cs : forall S, In S (SP.p_cs B2) -> SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS S.
  Proof.
    intros S HS. cbn [SP.p_cs B2 SP.PGH SP.PGX] in HS. destruct HS as [<-|[<-|[]]]; [exact SFPBS_ok | exact PFFBS_ok].
  Qed.

  Variable Cnd : env -> Prop.
  Hypothesis HCG : forall E E2, SP.gagree (SP.p_G B2) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2.
  Hypothesis HCW : forall E, Cnd E -> SP.wins_client hmC E (SP.p_W B2).
  Hypothesis HCR : forall E, Cnd E -> forall w, In w (SP.p_CR B2) -> forall z, fst (SP.win_den E w) <= z < snd (SP.win_den E w) -> hmA z.
  Hypothesis HIK : forall E M0, Cnd E -> hmH M0 -> know_ok SG E M0 (SP.p_IK B2).
  Hypothesis HSTK : forall E, Cnd E -> SP.hs_ok hmS E (SP.p_PS B2) (SP.p_W B2).

  Theorem b2_sound : forall T E M rom ms, In T (SP.p_tm B2 ++ SP.p_xt B2) -> hmR rom -> SX.aw_genuine E (SP.p_A B2) -> Cnd E ->
    hmH M -> ST.tm_okF SG T E M rom ms -> SG.gholds GP E M (ST.t_ghost T) ->
    exists ms', ExecF.mstepsF SG (SP.fpu hmF (SP.p_A B2) E) ms ms' /\ SP.prun_postH SG GP hmH hmA B2 E M rom ms'.
  Proof.
    exact (SP.pcheck_soundHSC SG GP gfp2 (SVX.gvc_trimp 90 (SVX.gvc_enrich SVX.bc_enrich (wvc_okL SG 1048512 0x236c0)))
             (gp2_frame SG data idxs)
             (SVX.gvc_trimp_ok SG GP 90 _
                (SVX.gvc_enrich_ok SG GP SVX.bc_enrich _ (SVX.bc_enrich_ok SG)
                   (wvc_okL_sound SG data idxs 1048512 ltac:(lia) 0x236c0 ltac:(lia) d2v_img_both)))
             hmH hmA hmC hmR (AHMB.HMC_sub AI LB) (AHMB.HMF AI L RNGh st LB) hmF hmS (AHMB.HMS_mono L RNGh)
             B2 B2_IT 4000 true B2_hints Cnd
             b2_cert (SP.itab_ranges_sound SG _) ltac:(intros TA []) b2_cs HCG HCW HCR HIK HSTK).
  Qed.
End B2S.
Print Assumptions b2_sound.
