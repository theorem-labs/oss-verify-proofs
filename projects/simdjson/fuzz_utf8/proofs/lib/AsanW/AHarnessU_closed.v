(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessU ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface ADepot_iface ARep ALayout AHeapP AFake_iface AFake_arep
     APoisonR_iface F_annot_grow AAtexit_iface AH_opnew AH_opdelete_top AU_kit AU_iface AU_consts AHarnessU_iface AU_parts_iface AU_fake_arep AU_first_M AU_fuzz_M AU_vdtor_M.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Inst.
  Variable DI : ADepotIface.
  Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
  Hypothesis HL : ahole_laws (AFake_arep.AH DI AQ ASEC).
  Variable CI : list (Z * Z).
  Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
  (* [comment removed for export] *)
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P (AFake_arep.AH DI AQ ASEC).
  Hypothesis EC : aci AI = CI.
  Hypothesis IMG_CI : forall iv, In iv client_ranges -> In iv (aci AI).
  Hypothesis AI_kind : forall L RNG st LB m p A n, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n.
  Hypothesis AI_premap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> premap_cells m.
  (* [comment removed for export] *)
  Hypothesis AI_lsan : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells asegs m 0x6a3798 [C4 (Z_to_bv 64 0)].
  Hypothesis AI_frame_lsan : forall L RNG st LB m m' W, AHEAP AI L RNG st LB m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => aclient_range (aci AI) LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ iv = (0x6a3798, 0x6a379c)) W ->
    rw_cells asegs m' 0x6a3798 [C4 (Z_to_bv 64 0)] -> AHEAP AI L RNG st LB m'.

  (* [comment removed for export] *)
  Lemma AGROW : annot_grow_stmtA.
  Proof. exact annot_grow_full. Qed.

  (* [comment removed for export] *)
  Lemma fake_flag_AI : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges (aci AI) (fflag L cls F).
  Proof. intros L RNG st LB m cls F N AHx Hin. rewrite E in AHx. rewrite EC. eapply fake_flag_P; eassumption. Qed.

  Lemma fake_release_AI : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
    AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
  Proof. intros L RNG st LB m cls F N AHx. rewrite E in AHx |- *. eapply fake_release_P; eassumption. Qed.

  (* [comment removed for export] *)
  Lemma stack_malloc_1_AI : stack_malloc_1_stmt AI fflag afake_rng.
  Proof.
    unfold stack_malloc_1_stmt. intros until lo. intros AHx NOFK MI ST BOT LO SPT TP RSTK RI RFS.
    rewrite E in AHx.
    eapply evtF_mono; [eapply stack_malloc_1_P; try eassumption; unfold SM_STACK, SM1_STACK in *; lia|].
    cbv beta. intros ms' PO. unfold sm1_postP in PO. unfold sm1_post.
    destruct PO as (F & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & j0 & j1 & j2 & junk & EQ & MI' & ST' & HPR & AH' & REST).
    exists F, x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m', j0, j1, j2, junk.
    rewrite E, EC. repeat (split; [assumption|]). exact REST.
  Qed.

  (* [comment removed for export] *)
  Lemma RSI : rsi_stmt AI.
  Proof. exact (rsi_proof AI IMG_CI (opnew_proofA AI)). Qed.

  (* [comment removed for export] *)
  Theorem fuzz_oneU_closedF : fuzz_oneU_stmt AI afake_rng.
  Proof.
    exact (fuzz_oneU_proof AI fflag afake_rng IMG_CI stack_malloc_1_AI fake_flag_AI fake_release_AI RSI acxa_atexit_proof AI_lsan AI_frame_lsan).
  Qed.

  (* [comment removed for export] *)
  Theorem avdtor_closedF : avdtor_stmt AI.
  Proof. exact (avdtor_proof AI IMG_CI (opdelete_data_proofA AI) AGROW AI_kind AI_premap). Qed.
End Inst.
End CANSEC1.
