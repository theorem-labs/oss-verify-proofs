(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AW_DepotFrame AW_Drain AW_MergeBatches AW_Recycle AllocWalkKit
     AG_MallocModel AG_WFHit AG_Malloc AG_Malloc2 AG_FreeModel AG_FreeModel2 AG_RepQ AG_RepQFacts AG_RepQFacts2 AG_FreeMid AG_FreeT1
     AG_RecycleModel AG_WriteSet AG_RecycleDefs SecLazy AllocTacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AG_RecEntry.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PackagesR.
  Context {HCEIL : HeapCeil}.
  Variables (sp : word) (lo : Z) (d' : depot) (LB' : list (Z * Z)).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 3280 <= bv_unsigned sp.

  Theorem rec_pre_okR : forall (sm : ast) (m2 m1 : mem),
    let stm := a_st sm in let lt := qc_list (as_tq stm) in let lg := qc_list (as_gq stm) in
    ARHEAPQ sm [] [] LB' m2 -> lt <> [] ->
    munch (drain_W (bv_unsigned sp + -2288) (a_thr sm + OT_TQ) (last (map qb_addr lg) 0) (zlen lg)) m2 m1 -> wmono asegs m2 m1 ->
    (zlen lg <> 0 -> rw_cells asegs m1 (last (map qb_addr lg) 0)
                       [C8 (wz (hd 0 (map qb_addr lt))); C8 (wz (qb_size (last lg (mkQB 0 0 0 [])))); C8 (wz (qb_count (last lg (mkQB 0 0 0 []))))]) ->
       batches_rep m1 (lg ++ lt) /\ Forall bok (lg ++ lt) /\ List.NoDup (map qb_addr (lg ++ lt))
    /\ (forall a b, In a (map qb_addr (lg ++ lt)) -> In b (map qb_addr (lg ++ lt)) -> a <> b -> a + kBatchSize <= b \/ b + kBatchSize <= a)
    /\ qc_bytes (as_gq stm) + qc_bytes (as_tq stm) = bsum (lg ++ lt).
  Proof.
    intros sm m2 m1. cbv zeta. intros HQ TNE MU1 WM1 GL1. pose proof HQ as (RQ & _).
    assert (SPV : aceil + 48 <= bv_unsigned sp + -2288) by (clear - LO HI; lia).
    split; [exact (batches_after_transfer sm m2 m1 (bv_unsigned sp + -2288) RQ SPV MU1 WM1 GL1)|].
    exact (rec_pre_pure sm [] [] m2 RQ).
  Qed.

  Theorem rec_entry_okR : forall (sm : ast) (m2 m1 m4 : mem) (mo4 : Model) (l2F exF rpF : list qbatch) (b2F : Z),
    let stm := a_st sm in let lt := qc_list (as_tq stm) in let lg := qc_list (as_gq stm) in let l := lg ++ lt in
    let Tb := exF ++ rev rpF in let s4 := recentry_s sm l2F b2F in
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
  Proof.
    intros sm m2 m1 m4 mo4 l2F exF rpF b2F. cbv zeta.
    intros HQ TNE INIT NM TQB GQB AWV FX AMX DEP DPL RS MU1 WM1 GL1 TQ1 MU4 WM4 MI4 QM4 GQ4 BR24 BRT4 OK24 OKT4 SUB4 ND4 B24.
    pose proof HQ as (RQ & _).
    set (spv := bv_unsigned sp + -2288) in *.
    set (lt := qc_list (as_tq (a_st sm))) in *. set (lg := qc_list (as_gq (a_st sm))) in *.
    assert (SPV : aceil + 96 <= spv) by (subst spv; clear - LO HI; lia).
    pose proof (munch_app_re _ _ _ _ _ MU1 MU4) as MU. pose proof (munch_agree _ _ _ MU) as AG. pose proof (wmono_trans _ _ _ _ WM1 WM4) as WM.
    (* [comment removed for export] *)
    assert (TQ4 : rw_cells asegs m4 (a_thr sm + OT_TQ) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]).
    { eapply (rw_cells_transport_pt (outside (rec_W spv (lg ++ lt))) m1 m4 (munch_agree _ _ _ MU4) WM4); [exact TQ1|].
      cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length]. intros a Ha.
      apply (ZRW_thr sm m2 spv RQ SPV a). pose proof (AREPQ_placed _ _ _ _ RQ) as (_ & _ & _ & _ & _ & _ & T1 & _). clear - Ha T1. unfold OT_TQ, kPageSize in *. lia. }
    pose proof (rec_pre_pure sm [] [] m2 RQ) as (OKL & NDL & PW & QB). fold lt lg in OKL, NDL, PW, QB.
    pose proof (rsplit_bsum _ _ _ _ _ _ _ RS QB) as [BT1 BT2].
    split; [exact (arepq_rec_entry sm m2 m4 spv l2F exF rpF b2F kQuarantineMinSize RQ SPV AG WM QM4 GQ4 TQ4 BR24 RS)|].
    split; [exact (NUM_rec_entry sm l2F b2F NM)|].
    split; [exact (awin_rec_entry sm m2 m4 l2F b2F WM AWV)|].
    split; [exact (flagsx_rec_entry sm m2 m4 spv RQ SPV AG WM FX)|].
    split; [exact (amodelx_rec_entry sm l2F b2F mo4 AMX)|].
    split; [exact (DEPOT_transport asegs d' m2 m4 _ DEP MU WM (depot_avoid_rec_entry sm m2 spv RQ SPV d' DPL))|].
    split; [exact (depot_placed_rec_entry sm l2F b2F d' DPL)|].
    split. { pose proof (bsum_len l2F OK24) as BL. pose proof (zlen_nonneg l2F) as ZL. clear - BT1 BT2 BL ZL TQB GQB.
             unfold kBatchSize, kMaxCacheSize, kQuarantineMaxSize in *. lia. }
    split; [exact (rec_entry_T sm m2 l2F exF rpF b2F RQ (fun x Hx => SUB4 x ltac:(apply in_app_iff; right; exact Hx)))|].
    split; [exact (proj1 (proj2 (proj2 (proj2 (rec_entry_pop sm m2 l2F exF rpF b2F kQuarantineMinSize RQ RS)))))|].
    split; [exact (alive_below sm m2 l2F b2F RQ)|].
    split; [| exact (alive_agree sm m2 m4 spv RQ SPV AG)].
    apply (acompl_of_munch sm sm d' lo (bv_unsigned sp) _ m2 m4 MU). apply (W_awrit sm m2 spv RQ SPV d' lo (bv_unsigned sp)); subst spv; clear - LO HI; lia.
  Qed.
End PackagesR.
