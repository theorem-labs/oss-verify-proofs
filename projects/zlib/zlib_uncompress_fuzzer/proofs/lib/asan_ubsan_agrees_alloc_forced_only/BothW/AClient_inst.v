(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells AProto ABase AMalloc_iface ADepot_iface ARep ALayout AHeapP AQConst ARepQ ASec F_adepot
     AFake_iface AFake_arep AFake_arep0L AFake_arep2L ADriver_iface AInstance AInstanceM AInstanceF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BIface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Inst.
  Variable DI : ADepotIface.
  Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
  Hypothesis HL : ahole_laws (AH DI AQ ASEC).
  Variable CI : list (Z * Z).
  Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P (AH DI AQ ASEC).
  Hypothesis EC : aci AI = CI.

  Lemma fake_flag_AI : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges (aci AI) (fflag L cls F).
  Proof. intros L RNG st LB m cls F N AHx Hin. rewrite E in AHx. rewrite EC. eapply fake_flag_P; eassumption. Qed.

  Lemma fake_release_AI : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
    AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
  Proof. intros L RNG st LB m cls F N AHx. rewrite E in AHx |- *. eapply fake_release_P; eassumption. Qed.

  Local Ltac sm_close E EC PO :=
    let F := fresh "F" in
    destruct PO as (F & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & j0 & j1 & j2 & junk & EQ & MI' & ST' & HPR & AH' & REST);
    exists F, x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m', j0, j1, j2, junk;
    rewrite E, EC; repeat (split; [assumption|]); exact REST.

  Lemma SM0_AI : SM0_stmt AI fflag afake_rng.
  Proof.
    unfold SM0_stmt, sm_stmt. intros until lo. intros AHx NOFK MI ST BOT LO SPT TP RSTK RI RFS.
    rewrite E in AHx. unfold ASM0.
    eapply evtF_mono; [eapply stack_malloc_0_P1; try eassumption; unfold U2BIface.SM_STACK, AFake_arep.SM_STACK in *; lia|].
    cbv beta. intros ms' PO. unfold sm0_postP in PO. unfold sm_post. sm_close E EC PO.
  Qed.
  Lemma SM2_AI : SM2_stmt AI fflag afake_rng.
  Proof.
    unfold SM2_stmt, sm_stmt. intros until lo. intros AHx NOFK MI ST BOT LO SPT TP RSTK RI RFS.
    rewrite E in AHx. unfold ASM2.
    eapply evtF_mono; [eapply stack_malloc_2_P1; try eassumption; unfold U2BIface.SM_STACK, AFake_arep.SM_STACK in *; lia|].
    cbv beta. intros ms' PO. unfold sm2_postP in PO. unfold sm_post. sm_close E EC PO.
  Qed.
End Inst.

Section OfFree.
  Hypothesis FREE : afree_stmt aci_I AHEAP_I.
  Notation AIF := (AI_of FREE).
  Local Ltac inst_args := first [exact AH_laws | exact (AI_of_CI_OK FREE) | exact (AI_of_E FREE) | reflexivity].
  Lemma inst_fake_flag : forall L RNG st LB m cls F N,
    AHEAP AIF L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges (aci AIF) (fflag L cls F).
  Proof. intros L RNG st LB m cls F N AHx Hin. eapply (fake_flag_AI adepot_iface AQUAR ASEC_of); [inst_args ..| exact AHx| exact Hin]. Qed.
  Lemma inst_fake_release : forall L RNG st LB m cls F N,
    AHEAP AIF L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
    AHEAP AIF L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
  Proof. intros L RNG st LB m cls F N AHx. eapply (fake_release_AI adepot_iface AQUAR ASEC_of); [inst_args ..| exact AHx]. Qed.
  Lemma inst_SM0 : SM0_stmt AIF fflag afake_rng.
  Proof. eapply (SM0_AI adepot_iface AQUAR ASEC_of); inst_args. Qed.
  Lemma inst_SM2 : SM2_stmt AIF fflag afake_rng.
  Proof. eapply (SM2_AI adepot_iface AQUAR ASEC_of); inst_args. Qed.
  Definition inst_rng_fs_mono := afake_rng_mono.

  Lemma inst_OBC : exists iv, In iv (aci AIF) /\ fst iv <= 0x60c1c0 /\ 0x60c1c0 + 262144 <= snd iv.
  Proof. exists (0x60c1c0, 0x65c1c0). split; [apply AI_of_DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia]. Qed.
  Lemma inst_VCL : exists iv, In iv (aci AIF) /\ fst iv <= 141152 /\ 141160 <= snd iv.
  Proof. exists (0x22760, 0x22780). split; [apply AI_of_DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia]. Qed.
  Lemma inst_TABC1 : exists iv, In iv (aci AIF) /\ fst iv <= 141376 /\ 152288 <= snd iv.
  Proof. exists (0x22840, 0x25300). split; [apply AI_of_DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia]. Qed.
  Lemma inst_TABC2 : exists iv, In iv (aci AIF) /\ fst iv <= 149216 /\ 149568 <= snd iv.
  Proof. exists (0x246e0, 0x24860). split; [apply AI_of_DRV_CI; unfold drv_img_ranges; cbn; tauto| cbn; lia]. Qed.
  Lemma inst_CI_LO : forall iv, In iv (aci AIF) -> 32768 <= fst iv.
  Proof. intros iv Hin. pose proof aci_ok as OK. rewrite Forall_forall in OK. destruct (OK iv Hin) as (LO & _). lia. Qed.
End OfFree.
End CANSEC1.
