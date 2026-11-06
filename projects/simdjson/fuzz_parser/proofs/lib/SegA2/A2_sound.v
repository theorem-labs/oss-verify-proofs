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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegVCx.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHM SFPA_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2 S2WalkVC S2WalkVCok.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import S2WalkVCT S2WalkVC2 S2TabA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA2 Require Import A2_defs A2_cert.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Section A2S.
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
  Hypothesis SFPAS_ok : SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS SFPAS.
  Hypothesis PFFAS_ok : SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS PFFAS.

  Lemma a2_cs : forall S, In S (SP.p_cs A2) -> SP.summ_okHSC SG GP hmH hmA hmC hmR hmF hmS S.
  Proof.
    intros S HS. cbn [SP.p_cs A2 SP.PGH SP.PGX] in HS. destruct HS as [<-|[<-|[]]]; [exact SFPAS_ok | exact PFFAS_ok].
  Qed.

  Variable Cnd : env -> Prop.
  Hypothesis HCG : forall E E2, SP.gagree (SP.p_G A2) E E2 -> eb E = eb E2 -> Cnd E -> Cnd E2.
  Hypothesis HCW : forall E, Cnd E -> SP.wins_client hmC E (SP.p_W A2).
  Hypothesis HCR : forall E, Cnd E -> forall w, In w (SP.p_CR A2) -> forall z, fst (SP.win_den E w) <= z < snd (SP.win_den E w) -> hmA z.
  Hypothesis HIK : forall E M0, Cnd E -> hmH M0 -> know_ok SG E M0 (SP.p_IK A2).
  Hypothesis HSTK : forall E, Cnd E -> SP.hs_ok hmS E (SP.p_PS A2) (SP.p_W A2).

  Theorem a2_sound : forall T E M rom ms, In T (SP.p_tm A2 ++ SP.p_xt A2) -> hmR rom -> SX.aw_genuine E (SP.p_A A2) -> Cnd E ->
    hmH M -> ST.tm_okF SG T E M rom ms -> SG.gholds GP E M (ST.t_ghost T) ->
    exists ms', ExecF.mstepsF SG (SP.fpu hmF (SP.p_A A2) E) ms ms' /\ SP.prun_postH SG GP hmH hmA A2 E M rom ms'.
  Proof.
    exact (SP.pcheck_soundHSC SG GP gfp2 (SVX.gvc_trimp 90 (wvc_okL SG 1048512 0x23640)) (gp2_frame SG data idxs)
             (SVX.gvc_trimp_ok SG GP 90 _ (wvc_okL_sound SG data idxs 1048512 ltac:(lia) 0x23640 ltac:(lia) d2v_img_asan))
             hmH hmA hmC hmR (AHM.HMC_sub AI LB) (AHM.HMF AI L RNGh st LB) hmF hmS (AHM.HMS_mono L RNGh)
             A2 A2_IT 4000 true A2_hints Cnd
             a2_cert (SP.itab_ranges_sound SG _) ltac:(intros TA []) a2_cs HCG HCW HCR HIK HSTK).
  Qed.
End A2S.
Print Assumptions a2_sound.
