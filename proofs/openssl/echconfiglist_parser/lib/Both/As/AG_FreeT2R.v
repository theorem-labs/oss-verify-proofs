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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2 AllocRepX CidBits CidBits2
     AsDepotInv AsDepotHash AsDepotPut AsUnwind AW_DepotFrame AW_MallocBase AW_AllocBase AW_IAInit AW_FreePre
     AW_Put1 AW_Enqueue1 AW_Enqueue2 AW_Put2 AW_Drain AW_Put3 AS_Free1 AS_Free2 AS_Free3 AS_Free4 AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_RefillModel AG_Refill1 AG_Refill2 AG_Frame AG_MallocCold AG_MallocTop
     AG_FreeModel AG_FreeModel2 AG_WFFree AG_Free1 AG_FreeFacts AG_Free2 AG_Free3 AG_Free4 AG_Free9 AG_RepQ AG_RepQFacts AG_RepQFacts2
     AG_FreeMid AG_FreeTail SecLazy
     AW_MergeBatches AW_Recycle AW_DoRecycle AW_Put4 AG_FreeT1 AG_WriteSet SecLazy2 AG_RecycleDefs AG_RecycleModel2 AllocBudget AS_DoRecycle AG_CacheDealloc3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).
Local Ltac olia := dle_wrap ltac:(Zify.zify; xlia zchecker).

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_PutR1 AW_EnqueueR1 AW_PutR2 AW_PutR3 AW_PutR4 AG_FreeT2.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section FreeTail2R.
  Variables (sp gp tp cs0 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (Q : config -> Prop).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (ch : chunk).
  Variables (T : list Z) (RFr : mem -> Prop).

  Let st := a_st s.
  Let TH := a_thr s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.
  Let LB' := lb_remove U LB.

  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 3280 <= bv_unsigned sp.
  Hypothesis RFrA : forall m0 m1, RFr m0 -> agree_on (fun a => bv_unsigned sp + -2208 <= a) m0 m1 -> RFr m1.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPv : bv_unsigned tp = ATP.
  Hypothesis DLO : d_nb d' + 16 * 65536 <= lo /\ d_sb d' + 8 * 131072 <= lo.

  (* [comment removed for export] *)
  Definition rec_state (sm : ast) (l2 : list qbatch) (b2 : Z) : ast :=
    mkAst (set_gq (transfer_m (a_st sm)) (mkQC l2 b2)) (a_thr sm) (a_ctx sm) (a_fsb sm) (a_L sm) (a_S sm) (a_Zr sm) (a_AL sm) (a_top sm) (a_bot sm).

  (* [comment removed for export] *)
  Hypothesis REC_PRE : forall (sm : ast) (m2 m1 : mem),
    let stm := a_st sm in let lt := qc_list (as_tq stm) in let lg := qc_list (as_gq stm) in
    ARHEAPQ sm [] [] LB' m2 -> lt <> [] ->
    munch (drain_W (bv_unsigned sp + -2288) (a_thr sm + OT_TQ) (last (map qb_addr lg) 0) (zlen lg)) m2 m1 -> wmono asegs m2 m1 ->
    (zlen lg <> 0 -> rw_cells asegs m1 (last (map qb_addr lg) 0)
                       [C8 (wz (hd 0 (map qb_addr lt))); C8 (wz (qb_size (last lg (mkQB 0 0 0 [])))); C8 (wz (qb_count (last lg (mkQB 0 0 0 []))))]) ->
       batches_rep m1 (lg ++ lt) /\ Forall bok (lg ++ lt) /\ List.NoDup (map qb_addr (lg ++ lt))
    /\ (forall a b, In a (map qb_addr (lg ++ lt)) -> In b (map qb_addr (lg ++ lt)) -> a <> b -> a + kBatchSize <= b \/ b + kBatchSize <= a)
    /\ qc_bytes (as_gq stm) + qc_bytes (as_tq stm) = bsum (lg ++ lt).

  (* [comment removed for export] *)
  Hypothesis REC_ENTRY : forall (sm : ast) (m2 m1 m4 : mem) (mo4 : Model) (l2F exF rpF : list qbatch) (b2F : Z),
    let stm := a_st sm in let lt := qc_list (as_tq stm) in let lg := qc_list (as_gq stm) in let l := lg ++ lt in
    let Tb := exF ++ rev rpF in let s4 := rec_state sm l2F b2F in
    ARHEAPQ sm [] [] LB' m2 -> lt <> [] -> as_cache_inited stm = true -> NUM stm ->
    0 <= qc_bytes (as_tq stm) <= kMaxCacheSize + kQuarantineMaxSize + kBatchSize -> 0 <= qc_bytes (as_gq stm) <= kQuarantineMaxSize ->
    awin_vis sm m2 -> flagsx_rep m2 -> AMODELX sm mo4 -> DEPOT asegs d' m2 -> depot_placed sm d' ->
    rsplit (mkQC l (qc_bytes (as_gq stm) + qc_bytes (as_tq stm))) kQuarantineMinSize = Some (mkQC l2F b2F, exF, rpF) ->
    munch (drain_W (bv_unsigned sp + -2288) (a_thr sm + OT_TQ) (last (map qb_addr lg) 0) (zlen lg)) m2 m1 -> wmono asegs m2 m1 ->
    (zlen lg <> 0 -> rw_cells asegs m1 (last (map qb_addr lg) 0)
                       [C8 (wz (hd 0 (map qb_addr lt))); C8 (wz (qb_size (last lg (mkQB 0 0 0 [])))); C8 (wz (qb_count (last lg (mkQB 0 0 0 []))))]) ->
    rw_cells asegs m1 (a_thr sm + OT_TQ) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    munch (rec_W (bv_unsigned sp + -2288) l) m1 m4 -> wmono asegs m1 m4 -> mem_inv asegs m4 ->
    rw_cells asegs m4 (AINST + OI_QMUTEX) [C8 (wz 0)] ->
    rw_cells asegs m4 (AINST + OI_GQ) [C8 (wz (zlen l2F)); C8 (wz (hd 0 (map qb_addr l2F))); C8 (wz (last (map qb_addr l2F) 0)); C8 (wz b2F)] ->
    batches_rep m4 l2F -> batches_rep m4 Tb -> Forall bok l2F -> Forall bok Tb ->
    (forall b, In b (l2F ++ Tb) -> In (qb_addr b) (map qb_addr l)) -> List.NoDup (map qb_addr (l2F ++ Tb)) -> b2F = bsum l2F ->
       AREPQ s4 (flat_map qb_chunks Tb) (map qb_addr Tb) m4 /\ NUM (a_st s4) /\ awin_vis s4 m4 /\ flagsx_rep m4 /\ AMODELX s4 mo4
    /\ DEPOT asegs d' m4 /\ depot_placed s4 d'
    /\ bsum Tb < 2^62 /\ Forall (fun b => class_of_addr (a_st s4) (qb_addr b) = kBatchClass) Tb
    /\ b2F <= kQuarantineMinSize /\ (forall a, alive (a_st s4) a -> a < aceil)
    /\ acompl sm sm d' lo (bv_unsigned sp) m2 m4 /\ agree_on (alive stm) m2 m4.

  (* [comment removed for export] *)
  Hypothesis STEP_CHUNK : forall (spD : word) (ra1 t0 t1 t2 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 t3 t4 t5 t6 s10x s11x : word)
      (m0 : mem) (msF : machine_state) (mo : Model) (sx : ast) (XC XB : list Z) (chx : chunk),
      AREPQ sx (ch_chunk_beg chx :: XC) XB m0 -> In chx (chunk_list (a_st sx)) -> ch_state chx = CQuarantine ->
      as_cache_inited (a_st sx) = true -> awin_vis sx m0 /\ flagsx_rep m0 -> AMODELX sx mo ->
      DEPOT asegs d' m0 -> depot_placed sx d' -> depot_cov d' mo -> mem_inv asegs m0 ->
      aceil <= lo -> lo + 800 <= bv_unsigned spD -> bv_unsigned spD + 16 <= 2^47 -> bv_unsigned spD mod 16 = 0 ->
      stk asegs m0 lo (bv_unsigned spD) -> bv_unsigned tp = ATP -> pusage (a_st sx) + 303104 <= B_PRIM ->
      bv_unsigned spD <= bv_unsigned spD + 8 /\ bv_unsigned spD + 8 + 8 <= 2^63 ->
      rw_cells asegs m0 (bv_unsigned spD + 8) [C8 (wz (a_cache sx))] ->
      lzok asegs (a_L sx) (a_S sx) (a_Zr sx) (mkCfg msF mo) ->
      restrict (a_L sx) (a_S sx) msF
        = MS (mkR ra1 spD gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned spD + 112)) (wz AINST) (wz (bv_unsigned spD + 8)) (wz (ch_chunk_beg chx)) a2 a3 a4 a5 a6 a7
                  x2 x3 x4 x5 x6 x7 x8 x9 s10x s11x t3 t4 t5 t6) F (Z_to_bv 64 0x199214) fc None m0 (seg_rom asegs) ->
      (forall msF' mo',
         rstep_post ra1 spD gp tp (Z_to_bv 64 (bv_unsigned spD + 112)) (wz AINST) x2 x3 x4 x5 x6 x7 x8 x9 s10x s11x F fc sx d' lo m0 mo XC XB XB
           (fun st' => forall stA, same_but_shadow stA (a_st sx) ->
                         exists stA' ev, cb_recycle stA (ch_chunk_beg chx) = Some (stA', ev) /\ same_but_shadow stA' st') msF' mo' ->
         sreach asegs Q (mkCfg msF' mo')) ->
      sreach asegs Q (mkCfg msF mo).

  (* [comment removed for export] *)
  Definition MREC (sm : ast) (stX : astate) : Prop :=
    forall stA, same_but_shadow stA (a_st sm) ->
      exists stR evR, quarantine_recycle (transfer_m stA) (as_qmin stA) = Some (stR, evR) /\ same_but_shadow stR stX.

  (* [comment removed for export] *)
  Lemma step_batch_real : forall (spD : word) (ra1 t0 t1 t2 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 t3 t4 t5 t6 s10x s11x : word)
      (m0 : mem) (msF : machine_state) (mo : Model) (sx : ast) (XC XB : list Z) (p : Z),
      AREPQ sx XC (p :: XB) m0 -> class_of_addr (a_st sx) p = kBatchClass ->
      as_cache_inited (a_st sx) = true -> awin_vis sx m0 /\ flagsx_rep m0 -> AMODELX sx mo ->
      DEPOT asegs d' m0 -> depot_placed sx d' -> depot_cov d' mo -> mem_inv asegs m0 ->
      aceil <= lo -> lo + 688 <= bv_unsigned spD -> bv_unsigned spD + 16 <= 2^47 -> bv_unsigned spD mod 16 = 0 ->
      stk asegs m0 lo (bv_unsigned spD) -> bv_unsigned tp = ATP ->
      junk m0 p (class_size kBatchClass) -> poisoned m0 p (Z.to_nat (class_size kBatchClass / 8)) kAsanHeapLeftRedzoneMagic ->
      pusage (a_st sx) + 303104 <= B_PRIM ->
      lzok asegs (a_L sx) (a_S sx) (a_Zr sx) (mkCfg msF mo) ->
      restrict (a_L sx) (a_S sx) msF
        = MS (mkR ra1 spD gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned spD + 112)) (wz AINST) (wz (a_cache sx)) (wz AINST) (wz kBatchClass) (wz p) a4 a5 a6 a7
                  x2 x3 x4 x5 x6 x7 x8 x9 s10x s11x t3 t4 t5 t6) F (Z_to_bv 64 0x199618) fc None m0 (seg_rom asegs) ->
      (forall msF' mo',
         rstep_post ra1 spD gp tp (Z_to_bv 64 (bv_unsigned spD + 112)) (wz AINST) x2 x3 x4 x5 x6 x7 x8 x9 s10x s11x F fc sx d' lo m0 mo XC XB XB
           (fun st' => forall stA, same_but_shadow stA (a_st sx) ->
                         exists stA' ev, cache_dealloc stA kBatchClass p = Some (stA', ev) /\ same_but_shadow stA' st') msF' mo' ->
         sreach asegs Q (mkCfg msF' mo')) ->
      sreach asegs Q (mkCfg msF mo).
  Proof.
    intros until p. intros RQ CLS INIT AX AMX DEP DPL DCOV MI LO' HI' SPT' SPA' ST TP SLOTJ SLOTP PROOM OK VISE K.
    eapply (cache_dealloc_arepq ra1 spD gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned spD + 112)) (wz AINST) a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 s10x s11x t3 t4 t5 t6
              F fc m0 msF mo Q sx XC XB kBatchClass p d' lo RQ CLS ltac:(unfold kBatchClass; clear; olia) INIT AX AMX DEP DPL DCOV MI LO' HI' SPT' SPA' ST TP SLOTJ SLOTP PROOM OK VISE).
    intros msF' mo' P. apply K. exact P.
  Qed.

  (* [comment removed for export] *)
  Definition rstep_postR (s0x : ast) (dd : depot) (m0 : mem) (mo0 : Model) (MODEL : astate -> Prop) (msF' : machine_state) (mo' : Model) : Prop :=
    exists (s' : ast) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       a_thr s' = a_thr s0x /\ a_ctx s' = a_ctx s0x /\ a_fsb s' = a_fsb s0x /\ a_Zr s' = a_Zr s0x /\ a_top s' = a_top s0x /\ a_bot s' = a_bot s0x
    /\ a_AL s' = a_AL s0x /\ a_sb s' = a_sb s0x /\ a_pa s' = a_pa s0x
    /\ (forall sc, In sc (as_sec (a_st s')) -> In sc (as_sec (a_st s0x)))
    /\ as_cache_inited (a_st s') = true
    /\ (forall c0, 0 <= c0 -> rg_allocated_user (get_region (a_st s') c0) = rg_allocated_user (get_region (a_st s0x) c0))
    /\ lzok asegs (a_L s') (a_S s') (a_Zr s') (mkCfg msF' mo')
    /\ restrict (a_L s') (a_S s') msF'
       = MS (mkR (wz 0x197a10) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0' t1' t2' cs0 (wz U) a0' a1' a2' a3' a4' a5' a6' a7' cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x197a10) fc None m' (seg_rom asegs)
    /\ AREPQ s' [] [] m' /\ awin_vis s' m' /\ flagsx_rep m' /\ AMODELX s' mo'
    /\ nonvm_same mo0 mo' /\ avmx s0x s' mo0 mo' /\ depot_cov dd mo'
    /\ DEPOT asegs dd m' /\ depot_placed s' dd /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -2208) /\ RFr m'
    /\ acompl s0x s' dd lo (bv_unsigned sp) m0 m' /\ avis s0x s' m0 m' /\ agree_on (pendz (a_st s0x) []) m0 m'
    /\ alive_kept (a_st s0x) (a_st s') /\ agree_on (alive (a_st s0x)) m0 m'
    /\ MODEL (a_st s').

  Theorem free_tail2_rawR : forall (sm : ast) (msF2 : machine_state) (mo2 : Model)
      (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : mem),
    a_thr sm = a_thr s -> a_top sm = a_top s -> a_bot sm = a_bot s ->
    qc_list (as_tq (a_st sm)) <> [] -> 0 <= qc_bytes (as_tq (a_st sm)) <= kMaxCacheSize + kQuarantineMaxSize + kBatchSize ->
    0 <= qc_bytes (as_gq (a_st sm)) <= kQuarantineMaxSize ->
    lzok asegs (a_L sm) (a_S sm) (a_Zr sm) (mkCfg msF2 mo2) ->
    restrict (a_L sm) (a_S sm) msF2
       = MS (enq_regsR sp gp tp s7 s8 s9 s10 s11 U size TH kMaxCacheSize t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F (Z_to_bv 64 0x19b46c) fc None m2 (seg_rom asegs) ->
    ARHEAPQ sm [] [] LB' m2 -> awin_vis sm m2 -> flagsx_rep m2 -> AMODELX sm mo2 ->
    DEPOT asegs d' m2 -> depot_placed sm d' -> depot_cov d' mo2 ->
    mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -2288) ->
    rw_cells asegs m2 (bv_unsigned sp + -2288) (put_frameR sp cs0 cs2 cs3 cs4 cs5 s6 U TH) ->
    RFr m2 ->
    (* [comment removed for export] *)
    kMaxCacheSize < qc_bytes (as_tq (a_st sm)) -> kQuarantineMaxSize < qc_bytes (as_gq (a_st sm)) + qc_bytes (as_tq (a_st sm)) ->
    as_cache_inited (a_st sm) = true -> NUM (a_st sm) ->
    (forall msF' mo', rstep_postR sm d' m2 mo2 (MREC sm) msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF2 mo2).
  Proof.
    intros sm msF2 mo2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2.
    intros Ethr Etop Ebot TNE TQB GQB OK2 VIS2 HQ AWV FX AMX DEP DPL DCOV MI2 ST2 PFR RF2 GT GT2 INIT NM K.
    pose proof HQ as (RQ & ND & LBs).
    pose proof (AREPQ_placed _ _ _ _ RQ) as PL2. pose proof (AREPQ_WFQ _ _ _ _ RQ) as WQ2. pose proof (conj PL2 WQ2 : placed_ok sm /\ WFQ (a_st sm) [] []) as OKQ2.
    pose proof (WFQ_consts _ _ _ WQ2) as (CQmax & CQmin & CQc).
    pose proof (AREPQ_mem _ _ _ _ RQ) as (INST & _ & _ & _ & _ & _ & _ & BT & BG).
    pose proof INST as (_ & _ & _ & _ & _ & _ & _ & QC & _ & QM & GQ & _). rewrite CQmax, CQmin, CQc in QC.
    pose proof (tq_cells_of_arepq sm [] [] m2 RQ) as TQ. rewrite Ethr in TQ.
    pose proof PL2 as (_ & SB2 & SB3 & _ & _ & _ & T1 & T2 & T3 & _). rewrite Ethr in T1, T2, T3.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR. pose proof aceil_range as ACR.
    set (lt := qc_list (as_tq (a_st sm))) in *. set (lg := qc_list (as_gq (a_st sm))) in *.
    set (glb := last lg (mkQB 0 0 0 [])).
    set (bt := qc_bytes (as_tq (a_st sm))) in *. set (bg := qc_bytes (as_gq (a_st sm))) in *.
    assert (BA : forall b, In b (lt ++ lg) -> AHI_LO <= qb_addr b /\ qb_addr b + 8192 <= aceil /\ qb_addr b mod 8 = 0).
    { intros b Hb. pose proof (batch_in_spaceQ sm [] [] OKQ2 b Hb) as (P1 & P2 & P3). clear - P1 P2 P3 SB2 SB3. unfold kBatchSize, kSpaceSize, kPageSize in *. repeat split; try exact P3; lia. }
    assert (NGB : 0 <= zlen lg /\ kBatchSize * zlen lg <= bg).
    { split; [unfold zlen; clear; lia|]. apply (qc_len_bytes (a_st sm) [] [] (as_gq (a_st sm)) WQ2 (WFQ_gq _ _ _ WQ2)). intros b Hb. apply in_app_iff. right. exact Hb. }
    assert (NTB : 1 <= zlen lt /\ kBatchSize * zlen lt <= bt).
    { split; [subst lt; destruct (qc_list (as_tq (a_st sm))); [exfalso; exact (TNE eq_refl)| rewrite zlen_cons; unfold zlen; clear; lia]|].
      apply (qc_len_bytes (a_st sm) [] [] (as_tq (a_st sm)) WQ2 (WFQ_tq _ _ _ WQ2)). intros b Hb. apply in_app_iff. left. exact Hb. }
    assert (ADB : forall x, (x = 0 \/ exists b, In b (lt ++ lg) /\ x = qb_addr b) -> 0 <= x < 2^64 /\ x mod 8 = 0).
    { intros x [->|(b & Hb & ->)]; [clear; repeat split; reflexivity || lia|]. pose proof (BA b Hb) as (P1 & P2 & P3). clear - P1 P2 P3 ACR. unfold AHI_LO in *. split; [lia| exact P3]. }
    assert (FGB : 0 <= hd 0 (map qb_addr lg) < 2^64 /\ hd 0 (map qb_addr lg) mod 8 = 0).
    { apply ADB. destruct (hd_addr_cases lg) as [E|(b & Hb & E)]; [left; exact E| right; exists b; split; [apply in_app_iff; right; exact Hb| exact E]]. }
    assert (LGB : 0 <= last (map qb_addr lg) 0 < 2^64 /\ last (map qb_addr lg) 0 mod 8 = 0).
    { apply ADB. destruct (last_addr_cases lg) as [E|(b & Hb & E)]; [left; exact E| right; exists b; split; [apply in_app_iff; right; exact Hb| exact E]]. }
    assert (FTB : 0 <= hd 0 (map qb_addr lt) < 2^64 /\ hd 0 (map qb_addr lt) mod 8 = 0).
    { apply ADB. destruct (hd_addr_cases lt) as [E|(b & Hb & E)]; [left; exact E| right; exists b; split; [apply in_app_iff; left; exact Hb| exact E]]. }
    assert (LTB : 0 <= last (map qb_addr lt) 0 < 2^64 /\ last (map qb_addr lt) 0 mod 8 = 0).
    { apply ADB. destruct (last_addr_cases lt) as [E|(b & Hb & E)]; [left; exact E| right; exists b; split; [apply in_app_iff; left; exact Hb| exact E]]. }
    assert (GLF : zlen lg <> 0 -> lg = removelast lg ++ [glb] /\ last (map qb_addr lg) 0 = qb_addr glb /\ In glb (qc_list (as_tq (a_st sm)) ++ qc_list (as_gq (a_st sm)))
                                 /\ batch_rep m2 glb 0 /\ carved (a_st sm) kBatchClass (qb_addr glb)).
    { intros NZ. assert (NE : lg <> []) by (intros E; apply NZ; rewrite E; reflexivity).
      assert (EL : lg = removelast lg ++ [glb]) by (subst glb; apply app_removelast_last; exact NE).
      assert (IN : In glb (qc_list (as_tq (a_st sm)) ++ qc_list (as_gq (a_st sm)))) by (apply in_app_iff; right; fold lg; rewrite EL; apply in_app_iff; right; left; reflexivity).
      split; [exact EL|]. split; [rewrite EL at 1; rewrite map_app; cbn [map]; rewrite last_app_nonnil by discriminate; reflexivity|].
      split; [exact IN|]. split; [rewrite EL in BG; exact (batches_rep_last m2 _ _ BG)|]. exact (proj1 (batch_carvedQ sm [] [] OKQ2 glb IN)). }
    assert (HI' : lo + 2576 <= bv_unsigned sp) by (clear - HI; lia).
    assert (THR : hidden (akobj (a_thr s) 4096 /\ a_thr s + 4096 <= aceil /\ a_thr s mod 16 = 0)).
    { constructor. unfold kPageSize in T1, T2, T3. clear - T1 T2 T3. split; [exact T2|]. split; [exact T3|]. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L sm) (a_S sm) (a_Zr sm) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (@put_drain_recR _ sp cs0 cs2 cs3 cs4 cs5 gp tp s6 s7 s8 s9 s10 s11 F fc lo LO HI' SPT
                t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 U size (a_thr s) kMaxCacheSize
                (zlen lg) (hd 0 (map qb_addr lg)) (last (map qb_addr lg) 0) bg (qb_size glb) (qb_count glb)
                (zlen lt) (hd 0 (map qb_addr lt)) (last (map qb_addr lt) 0) bt kQuarantineMaxSize kQuarantineMinSize MI2 THR).
      - unfold kMaxCacheSize. clear. lia.
      - exact GT.
      - clear - NGB FGB LGB GQB. unfold kBatchSize, kQuarantineMaxSize in *. lia.
      - clear - NTB FTB LTB TQB. unfold kBatchSize, kQuarantineMaxSize, kMaxCacheSize in *. lia.
      - clear - GQB TQB. unfold kBatchSize, kQuarantineMaxSize, kMaxCacheSize in *. lia.
      - unfold kQuarantineMaxSize, kQuarantineMinSize. clear. lia.
      - intros NZ. destruct (GLF NZ) as (EL & ELG & IN & BR & CV). rewrite ELG. pose proof (BA glb ltac:(apply in_app_iff; right; fold lg; rewrite EL; apply in_app_iff; right; left; reflexivity)) as (P1 & P2 & P3).
        pose proof (carved_vs_threadQ sm [] [] OKQ2 _ _ CV) as CT. change (class_size kBatchClass) with 8192 in CT. rewrite Ethr in CT.
        clear - P1 P2 P3 CT. unfold kPageSize, OT_TQ in *. repeat split; try exact P3; lia.
      - exact ST2.
      - exact PFR.
      - exact QM.
      - exact GQ.
      - intros NZ. destruct (GLF NZ) as (EL & ELG & IN & BR & CV). rewrite ELG. exact (proj1 BR).
      - exact TQ.
      - exact QC.
      - exact GT2. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ PO3.
    destruct PO3 as (t0'' & t1'' & a4'' & a5'' & a6'' & a7'' & m1 & VIS3 & DM & PFR1).
    pose proof DM as (MU1 & WM1 & MI1 & ST1 & QM1 & GQ1 & GL1 & TQ1 & QC1).
    rewrite unsigned_lit in MU1 by (clear - HI LO SPR ACR; lia). rewrite unsigned_lit in ST1 by (clear - HI LO SPR ACR; lia).
    rewrite <- Ethr in MU1, TQ1.
    (* [comment removed for export] *)
    destruct (REC_PRE sm m2 m1 HQ TNE MU1 WM1 GL1) as (BR1 & OKL1 & NDL1 & PW1 & QB1). fold lt lg bg bt in BR1, OKL1, NDL1, PW1, QB1.
    destruct (rsplit_total (lg ++ lt) (bg + bt) kQuarantineMinSize OKL1 QB1 ltac:(unfold kQuarantineMinSize; clear; lia)) as (l2F & b2F & exF & rpF & RS).
    (* [comment removed for export] *)
    assert (GQ1' : rw_cells asegs m1 (AINST + OI_GQ) [C8 (wz (zlen (lg ++ lt))); C8 (wz (hd 0 (map qb_addr (lg ++ lt)))); C8 (wz (last (map qb_addr (lg ++ lt)) 0)); C8 (wz (bg + bt))]).
    { rewrite zlen_app', hd_app_if, (last_app_ne lg lt TNE). exact GQ1. }
    eapply (evt_sreach_lazy_at asegs (a_L sm) (a_S sm) (a_Zr sm) _ msF3 _ mo3 Q OK3 VIS3).
    { eapply (recycle_head (wz 0x19b3a4) (Z_to_bv 64 (bv_unsigned sp + -2288)) gp tp t0'' t1'' t2' (wz (AINST + OI_Q)) (wz (a_thr s + OT_TQ))
                (wz (a_thr s + OT_CACHE)) (Z_to_bv 64 (bv_unsigned sp + -2136)) a4'' a5'' a6'' a7''
                (wz size) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz (a_thr s + OT_CACHE)) (wz (U + -16)) (wz kMaxCacheSize) s7 s8 s9 s10 s11 t3' t4' t5' t6'
                F fc m1 lo kQuarantineMinSize (bg + bt) (lg ++ lt) l2F exF rpF b2F MI1).
      - rewrite unsigned_lit by (clear - HI LO SPR ACR; lia). exact ST1.
      - exact LO.
      - rewrite unsigned_lit by (clear - HI LO SPR ACR; lia). clear - HI; lia.
      - rewrite unsigned_lit by (clear - HI LO SPR ACR; lia). clear - SPT; lia.
      - constructor. rewrite unsigned_lit by (clear - HI LO SPR ACR; lia). clear - SPA. Z.div_mod_to_equations. lia.
      - unfold kQuarantineMinSize. clear. lia.
      - clear - GQB TQB. unfold kQuarantineMaxSize, kMaxCacheSize, kBatchSize in *. lia.
      - exact QB1.
      - exact OKL1.
      - exact NDL1.
      - exact PW1.
      - exact RS.
      - exact QM1.
      - exact GQ1'.
      - exact BR1. }
    cbv beta. intros msF4 mo4 OK4 SBM4 _ PO4.
    destruct PO4 as (u0 & u1 & u2 & x0 & x1 & ua4 & ua5 & ua6 & ua7 & x2 & x3 & x4 & u3 & u4 & u5 & u6 & m4
                     & VIS4 & MU4 & WM4 & MI4 & ST4 & TMP4 & QM4 & GQ4 & BR24 & BRT4 & OK24 & OKT4 & SUB4 & ND4 & B24).
    rewrite unsigned_lit in VIS4, MU4, ST4, TMP4 by (clear - HI LO SPR ACR; lia).
    (* [comment removed for export] *)
    pose proof (AMODELX_mat sm mo2 mo3 AMX SBM3) as AMX3. pose proof (AMODELX_mat sm mo3 mo4 AMX3 SBM4) as AMX4.
    pose proof (depot_cov_mat d' mo2 mo3 DCOV SBM3) as DCOV3. pose proof (depot_cov_mat d' mo3 mo4 DCOV3 SBM4) as DCOV4.
    destruct (REC_ENTRY sm m2 m1 m4 mo4 l2F exF rpF b2F HQ TNE INIT NM TQB GQB AWV FX AMX4 DEP DPL RS MU1 WM1 GL1 TQ1 MU4 WM4 MI4 QM4 GQ4 BR24 BRT4 OK24 OKT4 SUB4 ND4 B24)
      as (RQ4 & NM4 & AWV4 & FX4 & AMX4' & DEP4 & DPL4 & BST & CLT & B2LE & ALB4 & ACM24 & AGA24).
    set (s4x := rec_state sm l2F b2F) in *. set (Tb := exF ++ rev rpF) in *.
    set (spD := Z_to_bv 64 (bv_unsigned sp + -2480)).
    assert (ESPD : bv_unsigned spD = bv_unsigned sp + -2480) by (subst spD; apply unsigned_lit; clear - HI LO SPR ACR; lia).
    (* [comment removed for export] *)
    eapply (do_recycle_arepq spD gp tp F fc x0 x1 x2 x3 x4 (wz (U + -16)) (wz kMaxCacheSize) s7 s8 s9 s10 s11 (Z_to_bv 64 (bv_unsigned sp + -2136))
              lo d' (lg ++ lt) Q s4x m4 mo4 Tb).
    - exact LO.
    - rewrite ESPD. clear - HI; lia.
    - rewrite ESPD. clear - SPT; lia.
    - rewrite ESPD. clear - SPA. Z.div_mod_to_equations. lia.
    - exact TPv.
    - exact OKL1.
    - exact PW1.
    - exact DLO.
    - exact ALB4.
    - (* [comment removed for export] *) intros. eapply STEP_CHUNK; eassumption.
    - (* [comment removed for export] *) intros. eapply step_batch_real; eassumption.
    - (* [comment removed for export] *) split; [exact RQ4|]. split; [exact INIT|]. split; [exact NM4|]. split; [exact AWV4|]. split; [exact FX4|]. split; [exact AMX4'|].
      split; [exact DEP4|]. split; [exact DPL4|]. split; [exact DCOV4| exact MI4].
    - rewrite ESPD. replace (bv_unsigned sp + -2480 + 112) with (bv_unsigned sp + -2288 + -80) by (clear; olia). exact ST4.
    - apply Permutation_refl.
    - apply Permutation_refl.
    - (* [comment removed for export] *) split; [exact OKT4|]. split; [rewrite map_app in ND4; exact (NoDup_app_remove_l _ _ ND4)|].
      split; [intros x Hx; apply SUB4; apply in_app_iff; right; exact Hx|]. split; [exact BST| exact CLT].
    - rewrite ESPD. replace (bv_unsigned sp + -2480 + 112) with (bv_unsigned sp + -2288 + -80) by (clear; olia).
      apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in TMP4. exact (proj1 TMP4).
    - exact BRT4.
    - exact OK4.
    - rewrite VIS4, ESPD. replace (bv_unsigned sp + -2480 + 112) with (bv_unsigned sp + -2288 + -80) by (clear; olia). subst s4x. unfold rec_state, a_cache. cbn [a_L a_S a_thr]. rewrite Ethr. reflexivity.
    - cbv beta. intros msF5 mo5 PO5.
    destruct PO5 as (sF & v0 & v1 & v2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & v3 & v4 & v5 & v6 & m5 & RL5 & CU5 & OK5 & VIS5 & ST5 & TMP5 & MOD5).
    rewrite ESPD in VIS5, ST5, TMP5. unfold AS_DoRecycle.REL in RL5. rewrite ESPD in RL5.
    replace (bv_unsigned sp + -2480 + 112) with (bv_unsigned sp + -2288 + -80) in VIS5, ST5, TMP5 by (clear; olia).
    replace (bv_unsigned sp + -2480 + 144) with (bv_unsigned sp + -2336) in RL5 by (clear; olia).
    destruct RL5 as (Et5 & Ec5 & Ef5 & Ez5 & Etp5 & Ebt5 & Eal5 & Esb5 & Epa5 & SUB5 & AU5 & NVS5 & AVM5 & ACM5 & AVS5 & AGS5 & ALK5 & AGA5).
    destruct CU5 as (RQ5 & INIT5 & NM5 & AWV5 & FX5 & AMX5 & DEP5 & DPL5 & DCOV5 & MI5).
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in TMP4. destruct TMP4 as [_ SAV4]. cbn [cells_size csize Nat.add] in SAV4.
    replace (bv_unsigned sp + -2288 + -80 + Z.of_nat 32) with (bv_unsigned sp + -2336) in SAV4 by (clear; olia).
    assert (SAV5 : rw_cells asegs m5 (bv_unsigned sp + -2336)
              [C8 (wz (a_thr s + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2136)); C8 (wz size); C8 (wz (a_thr s + OT_TQ)); C8 (wz (AINST + OI_Q)); C8 (wz 1684388)]).
    { eapply (AS_DoRecycle.rw_cells_transport_pt2 _ m4 m5 AGS5); [exact SAV4|]. intros a Ha. clear - Ha; olia. }
    assert (FR5 : rw_cells asegs m5 (bv_unsigned sp + -2288 + -80)
              [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz (a_thr s + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2136)); C8 (wz size); C8 (wz (a_thr s + OT_TQ)); C8 (wz (AINST + OI_Q)); C8 (wz 1684388)]).
    { apply (proj2 (rw_cells_app asegs _ _ [_; _; _; _] _)). split; [exact TMP5|]. cbn [cells_size csize Nat.add].
      replace (bv_unsigned sp + -2288 + -80 + Z.of_nat 32) with (bv_unsigned sp + -2336) by (clear; olia). exact SAV5. }
    (* [comment removed for export] *)
    assert (EQR : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2288)) = bv_unsigned sp + -2288) by (apply unsigned_lit; clear - HI LO SPR ACR; lia).
    rewrite <- EQR in VIS5, ST5, FR5.
    eapply (evt_sreach_lazy_at asegs (a_L sF) (a_S sF) (a_Zr sF) _ msF5 _ mo5 Q OK5 VIS5).
    { eapply (recycle_tail (wz 0x19b3a4) (Z_to_bv 64 (bv_unsigned sp + -2288)) gp tp (wz (AINST + OI_Q)) (wz (a_thr s + OT_TQ)) (wz size) (Z_to_bv 64 (bv_unsigned sp + -2136))
                (wz (a_thr s + OT_CACHE)) (wz (U + -16)) (wz kMaxCacheSize) s7 s8 s9 s10 s11 F fc lo); [rewrite EQR; clear - HI; lia| exact MI5| exact ST5| exact FR5]. }
    cbv beta. intros msF6 mo6 OK6 SBM6 _ PO6. destruct PO6 as [VIS6 ST6].
    rewrite EQR in ST6.
    change (ret_pc (wz 0x19b3a4)) with (ret_pc (Z_to_bv 64 0x19b3a4)) in VIS6. rewrite (ret_pc_even 0x19b3a4) in VIS6 by (clear; olia).
    (* [comment removed for export] *)
    pose proof (munch_agree _ _ _ MU4) as AG14.
    assert (OUT4 : forall a, bv_unsigned sp + -2288 <= a -> outside (rec_W (bv_unsigned sp + -2288) (lg ++ lt)) a).
    { intros a Ha. unfold rec_W. cbn [outside]. unfold AINST, OI_QMUTEX, OI_GQ.
      split; [clear - Ha; olia|]. split; [clear - Ha HI LO ACR; olia|]. split; [clear - Ha HI LO ACR; olia|].
      apply (outside_bext_hi _ a OKL1). clear - Ha HI LO; olia. }
    assert (AGS15 : agree_on (fun a => bv_unsigned sp + -2288 <= a) m1 m5).
    { eapply (AS_DoRecycle.agree_on_trans (fun a => bv_unsigned sp + -2288 <= a) m1 m4 m5); [| eapply AS_DoRecycle.agree_on_weaken; [| exact AGS5]; intros a Ha; cbv beta in *; clear - Ha; olia].
      intros a Ha Hr. cbv beta in Ha. exact (AG14 a (OUT4 a Ha) Hr). }
    assert (PFR5 : rw_cells asegs m5 (bv_unsigned sp + -2288) (put_frameR sp cs0 cs2 cs3 cs4 cs5 s6 U (a_thr s))).
    { eapply (AS_DoRecycle.rw_cells_transport_pt2 _ m1 m5 AGS15); [exact PFR1|]. intros a Ha. clear - Ha; olia. }
    assert (OUT1 : forall a, bv_unsigned sp + -2208 <= a -> outside (drain_W (bv_unsigned sp + -2288) (a_thr sm + OT_TQ) (last (map qb_addr lg) 0) (zlen lg)) a).
    { intros a Ha. unfold drain_W. apply AS_Free2.outside_app. split.
      - cbn [outside]. unfold AINST, OI_QMUTEX, OI_GQ, OT_TQ. rewrite Ethr. unfold kPageSize in T3.
        split; [clear - Ha; olia|]. split; [clear - Ha HI LO ACR; olia|]. split; [clear - Ha HI LO ACR; olia|]. split; [clear - Ha HI LO T3; olia| exact I].
      - destruct (Z.eqb_spec (zlen lg) 0) as [Ez|NZ]; [exact I|]. destruct (GLF NZ) as (EL & ELG & IN & BR & CV). rewrite ELG.
        pose proof (BA glb ltac:(apply in_app_iff; right; fold lg; rewrite EL; apply in_app_iff; right; left; reflexivity)) as (P1 & P2 & P3).
        cbn [outside]. split; [clear - Ha P2 HI LO; olia| exact I]. }
    assert (AGS21 : agree_on (fun a => bv_unsigned sp + -2208 <= a) m2 m1).
    { intros a Ha Hr. cbv beta in Ha. exact (munch_agree _ _ _ MU1 a (OUT1 a Ha) Hr). }
    assert (RF5 : RFr m5).
    { apply (RFrA m1 m5); [apply (RFrA m2 m1 RF2 AGS21)|].
      eapply AS_DoRecycle.agree_on_weaken; [| exact AGS15]. intros a Ha. cbv beta in *. clear - Ha; olia. }
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L sF) (a_S sF) (a_Zr sF) _ msF6 _ mo6 Q OK6 VIS6).
    { eapply (put_after_recycleR sp cs0 cs2 cs3 cs4 cs5 gp tp s6 s7 s8 s9 s10 s11 F fc lo HI'); [exact MI5| exact ST6| exact PFR5]. }
    cbv beta. intros msF7 mo7 OK7 SBM7 _ PO7. destruct PO7 as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & VIS7 & ST7).
    (* [comment removed for export] *)
    apply K. unfold rstep_postR.
    exists sF, y0, y1, y2, z0, z1, z2, z3, z4, z5, z6, z7, y3, y4, y5, y6, m5.
    subst s4x. unfold rec_state in *. cbn [a_thr a_ctx a_fsb a_Zr a_top a_bot a_AL a_L a_S a_st] in *.
    assert (ESB : a_sb (mkAst (set_gq (transfer_m (a_st sm)) (mkQC l2F b2F)) (a_thr sm) (a_ctx sm) (a_fsb sm) (a_L sm) (a_S sm) (a_Zr sm) (a_AL sm) (a_top sm) (a_bot sm)) = a_sb sm) by reflexivity.
    assert (EPA : a_pa (mkAst (set_gq (transfer_m (a_st sm)) (mkQC l2F b2F)) (a_thr sm) (a_ctx sm) (a_fsb sm) (a_L sm) (a_S sm) (a_Zr sm) (a_AL sm) (a_top sm) (a_bot sm)) = a_pa sm) by reflexivity.
    rewrite ESB in Esb5. rewrite EPA in Epa5.
    split; [exact Et5|]. split; [exact Ec5|]. split; [exact Ef5|]. split; [exact Ez5|]. split; [exact Etp5|]. split; [exact Ebt5|].
    split; [exact Eal5|]. split; [exact Esb5|]. split; [exact Epa5|].
    split; [intros sc Hsc; exact (SUB5 sc Hsc)|].
    split; [exact INIT5|].
    split; [intros c0 Hc0; rewrite (AU5 c0 Hc0); reflexivity|].
    split; [exact OK7|]. split; [exact VIS7|].
    split; [exact RQ5|]. split; [exact AWV5|]. split; [exact FX5|].
    split; [exact (AMODELX_mat sF mo6 mo7 (AMODELX_mat sF mo5 mo6 AMX5 SBM6) SBM7)|].
    split.
    { eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM3|]. eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM4|].
      eapply nonvm_same_trans; [exact NVS5|]. eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM6| apply nonvm_same_mat; exact SBM7]. }
    split.
    { eapply avmx_mat_l; [exact SBM3|]. eapply avmx_mat_l; [exact SBM4|]. eapply avmx_mat_r; [| exact SBM7]. eapply avmx_mat_r; [| exact SBM6]. exact AVM5. }
    split; [exact (depot_cov_mat d' mo6 mo7 (depot_cov_mat d' mo5 mo6 DCOV5 SBM6) SBM7)|].
    split; [exact DEP5|]. split; [exact DPL5|]. split; [exact MI5|]. split; [exact ST7|]. split; [exact RF5|].
    split.
    { apply (acompl_trans sm sm sF d' lo (bv_unsigned sp) m2 m4 m5 (conj eq_refl (conj eq_refl eq_refl)) (fun sc H => H) ACM24).
      apply (AS_DoRecycle.acompl_SP_mono sm sF d' lo (bv_unsigned sp + -2336) (bv_unsigned sp) m4 m5); [clear; olia| exact ACM5]. }
    split.
    { apply (avis_trans sm sm sF m2 m4 m5 (fun sc H => H) SUB5); [apply avis_of_wmono; eapply wmono_trans; [exact WM1| exact WM4]| exact AVS5]. }
    split; [intros a (x & IN & _); destruct IN|].
    split; [exact ALK5|].
    split; [eapply AS_DoRecycle.agree_on_trans; [exact AGA24| exact AGA5]|].
    (* [comment removed for export] *)
    intros stA SA. rewrite quarantine_recycle_rsplit.
    pose proof SA as SA'. destruct SA' as (_ & _ & _ & _ & _ & _ & _ & _ & Etq & Egq & _ & _ & _ & _ & Eqmin & _).
    unfold transfer_m at 1. cbn [as_gq set_gq set_tq]. rewrite Etq, Egq, Eqmin, CQmin. fold lg lt bg bt. rewrite RS.
    destruct (MOD5 (set_gq (transfer_m stA) (mkQC l2F b2F)) [] (sbs_set_gq_transfer _ _ _ SA)) as (stR & raccR & DR & SR).
    fold Tb. rewrite DR. exists stR, (rev raccR). split; [reflexivity| exact SR].
  Qed.
End FreeTail2R.
End HCW.
