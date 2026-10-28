(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BothAllocCons BReach BazyRestrict BazyLedger BazySR BazyNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocBudget BllocRep BllocRepFacts BllocRepX BsDepotInv BsDepotHash BsUnwind BW_DepotFrame BW_MallocBase BW_Put1 BW_Enqueue2 BG_MallocModel BG_Malloc2 BG_Frame BG_FreeModel BG_FreeModel2 BG_Free2 BG_RepQ BG_FreeMid BG_FreeTail BecLazy BG_WriteSet BG_RecycleDefs BG_RecycleModel3 BG_ComplFrame BG_FreeT2 BG_FreeT2W BG_RecycleChunk.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma alb_intro : forall s ch, In ch (chunk_list (a_st s)) -> ch_state ch = CAllocated -> In (ch_user_beg ch, ch_used ch) (alb s).
Proof.
  intros s ch IN AL. unfold alb. apply in_map_iff. exists ch. split; [reflexivity|]. apply filter_In. split; [exact IN|].
  unfold is_alloc. rewrite AL. reflexivity.
Qed.

Section FreeTail2X.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk).

  Let st := a_st s.
  Let TH := a_thr s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0xba24c (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  Let LB' := lb_remove U LB.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DFS : disj (a_fsb s) AFS_SIZE (d_nb d) (16 * 65536) /\ disj (a_fsb s) AFS_SIZE (d_sb d) (8 * 32768).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 3200 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPv : bv_unsigned tp = ATP.

  Theorem free_tail2 : forall sm msF2 mo2,
    free_mids ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB d lo CH ch sm msF2 mo2 ->
    kMaxCacheSize < qc_bytes (as_tq (a_st sm)) -> kQuarantineMaxSize < qc_bytes (as_gq (a_st sm)) + qc_bytes (as_tq (a_st sm)) ->
    as_cache_inited (a_st sm) = true -> NUM (a_st sm) ->
    (forall msF' mo', free_gpostX ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB d lo CH ch msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF2 mo2).
  Proof.
    intros sm msF2 mo2 MID GT GT2 INIT NM K.
    destruct MID as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & jk & rest & m2 & Ethr & Ectx & Efsb & Ezr & Etop & Ebot & Esb & Epa & Esec & Egq & HAL & TNE & TQB & GQB & OK2 & VIS2 & HQ & AWV & FX & AMX & NVS & DEP & DPL2 & DCOV & MI2 & ST2 & PFR & ESO & TRB & LR & NR & TFB & F4 & AMF & WM & ACM & AVX & (stX & ev0 & ev2 & EM & SBS & SC0)).
    pose proof HQ as (RQ & ND & LBs).
    pose proof (AREPQ_WFQ _ _ _ _ RQ) as WQ2. pose proof (WFQ_consts _ _ _ WQ2) as (CQmax & CQmin & CQc). pose proof (WFQ_lens _ _ _ WQ2) as [L32 _].
    assert (DLO : d_nb d' + 16 * 65536 <= lo /\ d_sb d' + 8 * 32768 <= lo).
    { pose proof DPL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & G11 & G12 & G13). unfold d'. rewrite d_nb_put, d_sb_put. clear - G11 G13 LO. lia. }
    eapply (free_tail2_w ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Q s LB d lo CH ch LO HI SPT SPA TPv DLO (step_chunk_real gp tp F fc Q d' lo) sm msF2 mo2
              t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' jk rest m2 Ethr Etop Ebot TNE TQB GQB OK2 VIS2 HQ AWV FX AMX DEP DPL2 DCOV MI2 ST2 PFR ESO TRB LR NR TFB F4 GT GT2 INIT NM).
    intros msF' mo' PO. apply K.
    destruct PO as (sF & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m5
                    & Et5 & Ec5 & Ef5 & Ez5 & Etp5 & Ebt5 & Eal5 & Esb5 & Epa5 & SUB5 & INIT5 & AU5 & OK5 & VIS5 & RQ5 & AWV5 & FX5 & AMX5
                    & NVS5 & AVM5 & DCOV5 & DEP5 & DPL5 & MI5 & ST5 & ACM5 & AVS5 & _ & ALK5 & AGA5 & MOD5).

    pose proof SBS as SBS0. unfold same_but_shadow in SBS0.
    destruct SBS0 as (_ & _ & Erg & _ & _ & _ & _ & Ech & Etq & Egq' & _ & _ & _ & Eqm & Eqmin & Eqc).
    destruct (MOD5 stX SBS) as (stR & evR & QR & SR).
    assert (L32X : length (as_regions (transfer_m stX)) = 32%nat) by (unfold transfer_m; cbn [as_regions set_gq set_tq]; rewrite Erg; exact L32).
    destruct (quarantine_recycle_final (transfer_m stX) (as_qmin stX) stR evR L32X QR) as (CS & TQR & GQR).
    pose proof SR as SR0. unfold same_but_shadow in SR0.
    destruct SR0 as (_ & _ & _ & _ & _ & _ & _ & EchF & EtqF & EgqF & _).
    pose proof (WFQ_consts _ _ _ (AREPQ_WFQ _ _ _ _ RQ5)) as (FQmax & FQmin & FQc).
    assert (QB : qbounds (a_st sF)).
    { unfold qbounds. rewrite <- EtqF, <- EgqF, TQR, FQc, FQmax. unfold transfer_m. cbn [as_tq set_gq set_tq qcache0 qc_bytes].
      split; [unfold kMaxCacheSize; clear; lia|]. rewrite Eqmin, CQmin in GQR. clear - GQR. unfold kQuarantineMinSize, kQuarantineMaxSize in *. lia. }

    assert (CSF : forall x, In x (chunk_list (a_st sF)) -> In x (chunk_list (a_st sm))).
    { intros x Hx. rewrite <- (chunk_list_ext stX (a_st sm) Ech). rewrite <- (chunk_list_ext stR (a_st sF) EchF) in Hx.
      apply CS in Hx. rewrite (chunk_list_ext (transfer_m stX) stX eq_refl) in Hx. exact Hx. }
    assert (LBF : forall b, In b LB' <-> In b (alb sF)).
    { intros [A n]. split.
      - intros Hb. apply (proj1 (LBs (A, n))) in Hb. destruct (alb_In sm A n Hb) as (x & IN & AL & <- & <-).
        exact (alb_intro sF x (ALK5 x IN AL) AL).
      - intros Hb. apply (proj2 (LBs (A, n))). destruct (alb_In sF A n Hb) as (x & IN & AL & <- & <-).
        exact (alb_intro sm x (CSF x IN) AL). }

    assert (OKs : ast_ok s) by exact (proj1 (proj1 HR)).
    assert (HLB1 : forall b, In b LB' -> In b (alb sm)) by (intros b Hb; exact (proj1 (LBs b) Hb)).
    assert (SUB1 : forall sc, In sc (as_sec (a_st sm)) -> In sc (as_sec (a_st s))) by (intros sc Hsc; rewrite <- Esec; exact Hsc).
    assert (ACM5d : acompl sm sF d lo (bv_unsigned sp) m2 m5) by (exact (proj1 (acompl_dput sm sF d (depot_hash T) nT lo (bv_unsigned sp) m2 m5) ACM5)).
    unfold free_gpostX.
    exists sF, u0, u1, u2, v0, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m5.
    split; [rewrite Et5; exact Ethr|]. split; [rewrite Ec5; exact Ectx|]. split; [rewrite Ef5; exact Efsb|].
    split; [rewrite Ez5; exact Ezr|]. split; [rewrite Etp5; exact Etop|]. split; [rewrite Ebt5; exact Ebot|].
    split; [intros sc Hsc; exact (SUB1 sc (SUB5 sc Hsc))|].
    split; [rewrite Eal5; exact HAL|].
    split; [exact OK5|]. split; [exact VIS5|].
    split; [split; [exact (AREP_of_AREPQ sF m5 RQ5 QB)| split; [exact ND| exact LBF]]|].
    split; [exact AWV5|]. split; [exact FX5|]. split; [exact AMX5|].
    split; [exact (nonvm_same_trans _ _ _ NVS NVS5)|].
    split; [exact DEP5|]. split; [exact DPL5|]. split; [exact DCOV5|]. split; [exact MI5|]. split; [exact ST5|].
    split.
    { apply (amframe_trans s LB' (bv_unsigned sp) m m2 m5 AMF).
      apply (amframe_of_compl s sm sF LB' d lo (bv_unsigned sp) m2 m5 OKs HLB1 (conj Ethr (conj Esb Epa)) Esec SUB5 DPL DFS LO ltac:(clear - HI; lia) ACM5d AGA5). }
    split; [exact (avis_trans s sm sF m m2 m5 SUB1 SUB5 (avis_of_wmono s sm m m2 WM) AVS5)|].
    split; [exact (acompl_trans s sm sF d lo (bv_unsigned sp) m m2 m5 (conj Ethr (conj Esb Epa)) SUB1 ACM ACM5d)|].
    split; [exact (avmx_trans s sm sF mo mo2 mo' SUB1 SUB5 AVX AVM5)|].
    rewrite EM, (free_tail_recycle U size stX ev0 ev2) by (rewrite ?Etq, ?Egq', ?Eqc, ?Eqm, ?CQc, ?CQmax; first [exact GT| exact GT2]).
    rewrite QR. eexists stR, _. split; [reflexivity| exact SR].
  Qed.
End FreeTail2X.
End HCW.
