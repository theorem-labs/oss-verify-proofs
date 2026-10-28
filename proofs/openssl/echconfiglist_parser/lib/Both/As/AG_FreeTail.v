(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsDepotPut AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_IAInit AW_FreePre
     AW_Put1 AW_Enqueue1 AW_Enqueue2 AW_Put2 AW_Drain AW_Put3 AS_Free1 AS_Free2 AS_Free3 AS_Free4 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_RefillModel AG_Refill1 AG_Refill2 AG_Frame AG_MallocCold AG_MallocTop
     AG_FreeModel AG_FreeModel2 AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_Free9 AG_RepQ AG_RepQFacts AG_FreeMid SecLazy
     AG_WriteSet AG_RecycleDefs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition FREE_COST : Z := 0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tq_cells_of_arepq : forall s XC XB m, AREPQ s XC XB m ->
  rw_cells asegs m (a_thr s + OT_TQ)
    [C8 (wz (zlen (qc_list (as_tq (a_st s))))); C8 (wz (hd 0 (map qb_addr (qc_list (as_tq (a_st s))))));
     C8 (wz (last (map qb_addr (qc_list (as_tq (a_st s)))) 0)); C8 (wz (qc_bytes (as_tq (a_st s))))].
Proof. intros s XC XB m (_ & _ & _ & _ & T & _). destruct T as (_ & _ & _ & _ & _ & _ & TQ & _). exact TQ. Qed.

Section FreeTails.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk).

  Let st := a_st s.
  Let TH := a_thr s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0x1bf2bc (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2944 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis QSZ : size <= kQuarantineMaxSize.

  (* [comment removed for export] *)
  Definition free_mids (sm : ast) (msF2 : machine_state) (mo2 : Model) : Prop :=
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (jk : list byte) (rest : list word) (m2 : mem),
       a_thr sm = a_thr s /\ a_ctx sm = a_ctx s /\ a_fsb sm = a_fsb s /\ a_Zr sm = a_Zr s /\ a_top sm = a_top s /\ a_bot sm = a_bot s
    /\ a_sb sm = a_sb s /\ a_pa sm = a_pa s                                                         (* [comment removed for export] *)
    /\ as_sec (a_st sm) = as_sec st /\ as_gq (a_st sm) = as_gq st /\ a_AL s - FREE_COST <= a_AL sm
    /\ qc_list (as_tq (a_st sm)) <> [] /\ 0 <= qc_bytes (as_tq (a_st sm)) <= kMaxCacheSize + kQuarantineMaxSize + kBatchSize
    /\ 0 <= qc_bytes (as_gq (a_st sm)) <= kQuarantineMaxSize
    /\ lzok asegs (a_L sm) (a_S sm) (a_Zr sm) (mkCfg msF2 mo2)
    /\ restrict (a_L sm) (a_S sm) msF2
       = MS (enq_regs sp gp tp s7 s8 s9 s10 s11 U size TH kMaxCacheSize t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F (Z_to_bv 64 0x19b46c) fc None m2 (seg_rom asegs)
    /\ ARHEAPQ sm [] [] (lb_remove U LB) m2 /\ awin_vis sm m2 /\ flagsx_rep m2 /\ AMODELX sm mo2 /\ nonvm_same mo mo2   (* [comment removed for export] *)
    /\ DEPOT asegs d' m2 /\ depot_placed sm d' /\ depot_cov d' mo2
    /\ mem_inv asegs m2 /\ stk asegs m2 lo (bv_unsigned sp + -2208)
    /\ rw_cells asegs m2 (bv_unsigned sp + -2208) (put_frame sp s6 U TH)
    /\ rw_cells asegs m2 (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))]
    /\ u64arr asegs m2 (bv_unsigned sp + -2128 + 16) (map wz T ++ rest) /\ length rest = (255 - length T)%nat /\ (1 <= length T <= 30)%nat
    /\ rw_cells asegs m2 (bv_unsigned sp + -72) [C8 sp]
    /\ rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ amframe s (lb_remove U LB) (bv_unsigned sp) m m2 /\ wmono asegs m m2
    /\ acompl s sm d lo (bv_unsigned sp) m m2 /\ avmx s sm mo mo2                                   (* [comment removed for export] *)
    /\ (exists stX ev0 ev2, am_free_full st U = free_tail_m U size stX ev0 ev2 /\ same_but_shadow stX (a_st sm) /\ syscalls_of ev0 = []).

  (* [comment removed for export] *)
  Definition free_gpostX (msF' : machine_state) (mo' : Model) : Prop :=
    exists (s' : ast) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       a_thr s' = a_thr s /\ a_ctx s' = a_ctx s /\ a_fsb s' = a_fsb s /\ a_Zr s' = a_Zr s /\ a_top s' = a_top s /\ a_bot s' = a_bot s
    /\ (forall sc, In sc (as_sec (a_st s')) -> In sc (as_sec (a_st s)))                             (* [comment removed for export] *)
    /\ a_AL s - FREE_COST <= a_AL s'
    /\ lzok asegs (a_L s') (a_S s') (a_Zr s') (mkCfg msF' mo')
    /\ restrict (a_L s') (a_S s') msF'
       = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ ARHEAP s' (lb_remove U LB) m' /\ awin_vis s' m' /\ flagsx_rep m' /\ AMODELX s' mo' /\ nonvm_same mo mo'
    /\ DEPOT asegs d' m' /\ depot_placed s' d' /\ depot_cov d' mo'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ amframe s (lb_remove U LB) (bv_unsigned sp) m m' /\ avis s s' m m'                          (* [comment removed for export] *)
    /\ acompl s s' d lo (bv_unsigned sp) m m' /\ avmx s s' mo mo'                                   (* [comment removed for export] *)
    /\ (exists st'' ev, am_free_full st U = Some (st'', ev) /\ same_but_shadow st'' (a_st s')).

  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

  (* [comment removed for export] *)
  Theorem free_tail0 : forall sm msF2 mo2,
    free_mids sm msF2 mo2 -> qc_bytes (as_tq (a_st sm)) <= kMaxCacheSize ->
    (forall msF' mo', free_gpostX msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF2 mo2).
  Proof.
    intros sm msF2 mo2 MID LE K.
    destruct MID as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & jk & rest & m2 & Ethr & Ectx & Efsb & Ezr & Etop & Ebot & Esb & Epa & Esec & Egq & HAL & TNE & TQB & GQB & OK2 & VIS2 & HQ & AWV & FX & AMX & NVS & DEP & DPL & DCOV & MI2 & ST2 & PFR & ESO & TRB & LR & NR & TFB & F4 & AMF & WM & ACM & AVX & (stX & ev0 & ev2 & EM & SBS & SC0)).
    pose proof HQ as (RQ & ND & LBs).
    pose proof (tq_cells_of_arepq sm [] [] m2 RQ) as TQ. rewrite Ethr in TQ.
    pose proof (WFQ_consts _ _ _ (AREPQ_WFQ _ _ _ _ RQ)) as (CQmax & CQmin & CQc).
    pose proof (AREPQ_placed _ _ _ _ RQ) as PL2. pose proof PL2 as (_ & _ & _ & _ & _ & _ & T1 & T2 & T3 & _). rewrite Ethr in T2, T3.
    eapply (evt_sreach_lazy_at asegs (a_L sm) (a_S sm) (a_Zr sm) _ msF2 _ mo2 Q OK2 VIS2).
    assert (HI' : lo + 2496 <= bv_unsigned sp) by (clear - HI; lia).
    { eapply (@put_tail _ sp ra s0 s1 s2 s3 s4 s5 gp tp s6 s7 s8 s9 s10 s11 F fc lo T rest jk LO HI' LR NR).
      6: exact TQ.
      - constructor. unfold kPageSize in T2, T3. split; [exact T2| exact T3].   (* [comment removed for export] *)
      - unfold kMaxCacheSize. clear. lia.
      - clear - TQB LE. lia.
      - exact ST2.
      - exact PFR.
      - exact ESO.
      - exact TRB.
      - exact TFB.
      - exact F4. }
    cbv beta. intros msF' mo' OK' SBM _ PO.
    destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & VIS' & ST').
    apply K. unfold free_gpostX. exists sm, t0'', t1'', t2'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m2.
    split; [exact Ethr|]. split; [exact Ectx|]. split; [exact Efsb|]. split; [exact Ezr|]. split; [exact Etop|]. split; [exact Ebot|].
    split; [intros sc Hsc; rewrite <- Esec; exact Hsc|]. split; [exact HAL|].
    split; [exact OK'|]. split; [exact VIS'|].
    split. { apply (ARHEAP_of_Q sm _ m2 HQ). split; [rewrite CQc; exact LE| rewrite CQmax; exact (proj2 GQB)]. }
    split; [exact AWV|]. split; [exact FX|]. split; [exact (AMODELX_mat sm mo2 mo' AMX SBM)|].
    split; [exact (nonvm_same_trans _ _ _ NVS (nonvm_same_mat mo2 mo' SBM))|].
    split; [exact DEP|]. split; [exact DPL|].
    split; [unfold depot_cov in DCOV |- *; intros x Hx; rewrite (same_but_materialized_vmmaps mo2 mo' SBM); exact (DCOV x Hx)|].
    split; [exact MI2|]. split; [exact ST'|]. split; [exact AMF|]. split; [exact (avis_of_wmono s sm m m2 WM)|].
    split; [exact ACM|]. split; [exact (avmx_mat_r s sm mo mo2 mo' AVX SBM)|].
    pose proof SBS as SBS0. unfold same_but_shadow in SBS0.
    destruct SBS0 as (_ & _ & _ & _ & _ & _ & _ & _ & Etq & _ & _ & _ & _ & _ & _ & Eqc).
    rewrite (free_tail_nodrain U size stX ev0 ev2) in EM by (rewrite Etq, Eqc, CQc; exact LE).
    eexists stX, _. split; [exact EM| exact SBS].
  Qed.
End FreeTails.
End HCW.
