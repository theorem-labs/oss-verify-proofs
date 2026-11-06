(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface ADepot_iface ARep ALayout AHeapP
     AFake_iface AFake_sm0 AFake_arep AFake_sm1k AFake_arep1k AFake_sm2 AFake2_iface AFake2_arep AH_fi_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Inst.
  Variable DI : ADepotIface.
  Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
  Hypothesis HL : ahole_laws (AFake_arep.AH DI AQ ASEC).
  Variable CI : list (Z * Z).
  Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P (AFake_arep.AH DI AQ ASEC).
  Hypothesis EC : aci AI = CI.

  (* [comment removed for export] *)
  #[using="DI AQ ASEC HL CI CI_OK E EC"] Lemma stack_malloc_0_AI' : stack_malloc_0_stmtk AI fflag afake_rng 0.
  Proof.
    unfold stack_malloc_0_stmtk, sm_stmtk. intros until lo. intros AHx LE MI ST BOT LO SPT TP RSTK RI RFS.
    rewrite E in AHx. unfold AFI_SM0. change 0x3c5b0 with ASTKMALLOC0.
    eapply evtF_mono; [eapply (stack_malloc_0_P DI AQ ASEC HL CI CI_OK); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast|].
    { intros F n. exact (fake_lek_zero_not_in 0 LB F n LE). }
    cbv beta. intros ms' PO. unfold sm0_postP in PO. unfold sm_post.
    destruct PO as (F & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & j0 & j1 & j2 & junk & EQ & MI' & ST' & HPR & AH' & REST).
    exists F, x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m', j0, j1, j2, junk.
    rewrite E, EC. repeat (split; [assumption|]). exact REST.
  Qed.

  (* [comment removed for export] *)
  #[using="DI AQ ASEC HL CI CI_OK E EC"] Lemma stack_malloc_1_AI' : forall k, Z.of_nat k < 8192 -> stack_malloc_1_stmtk AI fflag afake_rng k.
  Proof. intros k KB. exact (stack_malloc_1k_AI DI AQ ASEC HL CI CI_OK AI E EC k KB). Qed.

  (* [comment removed for export] *)
  #[using="DI AQ ASEC HL CI CI_OK E EC"] Lemma stack_malloc_2_AI' : stack_malloc_2_stmtk AI fflag afake_rng 0.
  Proof.
    unfold stack_malloc_2_stmtk, sm_stmtk. intros until lo. intros AHx LE MI ST BOT LO SPT TP RSTK RI RFS.
    rewrite E in AHx. unfold AFI_SM2. change 0x3c8b4 with ASTKMALLOC2.
    eapply evtF_mono; [eapply (stack_malloc_2_P DI AQ ASEC HL CI CI_OK); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast|].
    { intros F n. exact (fake_lek_zero_not_in 2 LB F n LE). }
    cbv beta. intros ms' PO. unfold sm2_postP in PO. unfold sm_post.
    destruct PO as (F & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & j0 & j1 & j2 & junk & EQ & MI' & ST' & HPR & AH' & REST).
    exists F, x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m', j0, j1, j2, junk.
    rewrite E, EC. repeat (split; [assumption|]). exact REST.
  Qed.

  (* [comment removed for export] *)
  #[using="DI AQ ASEC CI CI_OK E EC"] Lemma fake_flag_AI : fake_flag_law AI fflag.
  Proof.
    unfold fake_flag_law. intros L RNG st LB m cls F N AHx Hin. rewrite E in AHx. rewrite EC.
    eapply fake_flag_P; eassumption.
  Qed.

  #[using="DI AQ ASEC HL E"] Lemma fake_release_AI : fake_release_law AI fflag.
  Proof. unfold fake_release_law. intros L RNG st LB m cls F N AHx. rewrite E in AHx |- *. eapply fake_release_P; eassumption. Qed.
End Inst.
End CANSEC1.
