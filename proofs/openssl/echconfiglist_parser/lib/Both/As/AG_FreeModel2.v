(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocWf AllocKit AG_MallocModel AG_WFHit AS_Refill1 AG_RefillModel AG_ColdModel AG_FreeModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition free_tail_m (U size : Z) (stX : astate) (ev0 ev2 : list effect) : option (astate * list effect) :=
  match (if as_qcache stX <? qc_bytes (as_tq stX)
         then match quarantine_drain stX with
              | None => None
              | Some (st3, ev3) => Some (st3, [EPoison U (round_up size 8) kAsanHeapFreeMagic] ++ ev2 ++ ev3)
              end
         else Some (stX, [EPoison U (round_up size 8) kAsanHeapFreeMagic] ++ ev2)) with
  | None => None
  | Some (st4, ev4) => Some (st4, ev0 ++ [EStore64 U 0xFFFFFFFF00000000; EStore64 U 0] ++ ev4)
  end.

(* [comment removed for export] *)
Definition transfer_m (stX : astate) : astate :=
  set_gq (set_tq stX qcache0) (mkQC (qc_list (as_gq stX) ++ qc_list (as_tq stX)) (qc_bytes (as_gq stX) + qc_bytes (as_tq stX))).

Lemma free_tail_nodrain : forall U size stX ev0 ev2, qc_bytes (as_tq stX) <= as_qcache stX ->
  free_tail_m U size stX ev0 ev2 = Some (stX, ev0 ++ [EStore64 U 0xFFFFFFFF00000000; EStore64 U 0] ++ [EPoison U (round_up size 8) kAsanHeapFreeMagic] ++ ev2).
Proof. intros U size stX ev0 ev2 LE. unfold free_tail_m. replace (as_qcache stX <? qc_bytes (as_tq stX)) with false by (symmetry; apply Z.ltb_ge; exact LE). reflexivity. Qed.

Lemma free_tail_transfer : forall U size stX ev0 ev2, as_qcache stX < qc_bytes (as_tq stX) ->
  qc_bytes (as_gq stX) + qc_bytes (as_tq stX) <= as_qmax stX ->
  free_tail_m U size stX ev0 ev2 = Some (transfer_m stX, ev0 ++ [EStore64 U 0xFFFFFFFF00000000; EStore64 U 0] ++ [EPoison U (round_up size 8) kAsanHeapFreeMagic] ++ ev2 ++ []).
Proof.
  intros U size stX ev0 ev2 GT LE. unfold free_tail_m. replace (as_qcache stX <? qc_bytes (as_tq stX)) with true by (symmetry; apply Z.ltb_lt; exact GT).
  unfold quarantine_drain. cbn [qc_bytes]. replace (as_qmax stX <? qc_bytes (as_gq stX) + qc_bytes (as_tq stX)) with false by (symmetry; apply Z.ltb_ge; exact LE).
  reflexivity.
Qed.

Lemma free_tail_recycle : forall U size stX ev0 ev2, as_qcache stX < qc_bytes (as_tq stX) ->
  as_qmax stX < qc_bytes (as_gq stX) + qc_bytes (as_tq stX) ->
  free_tail_m U size stX ev0 ev2
  = match quarantine_recycle (transfer_m stX) (as_qmin stX) with
    | None => None
    | Some (st3, ev3) => Some (st3, ev0 ++ [EStore64 U 0xFFFFFFFF00000000; EStore64 U 0] ++ [EPoison U (round_up size 8) kAsanHeapFreeMagic] ++ ev2 ++ ev3)
    end.
Proof.
  intros U size stX ev0 ev2 GT GT2. unfold free_tail_m. replace (as_qcache stX <? qc_bytes (as_tq stX)) with true by (symmetry; apply Z.ltb_lt; exact GT).
  unfold quarantine_drain. cbn [qc_bytes]. replace (as_qmax stX <? qc_bytes (as_gq stX) + qc_bytes (as_tq stX)) with true by (symmetry; apply Z.ltb_lt; exact GT2).
  fold (transfer_m stX). change (as_qmin (set_gq (set_tq stX qcache0) _)) with (as_qmin stX).
  destruct (quarantine_recycle (transfer_m stX) (as_qmin stX)) as [[st3 ev3]|]; reflexivity.
Qed.

Section FreeModel2.
  Variables (st : astate) (ch : chunk).
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let st0 := set_internal_init st.

  Hypothesis FIND : find_chunk (as_chunks st) U = Some ch.
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis SZ : 1 <= size.
  Hypothesis QMAX : size <= as_qmax st /\ as_qcache st <> 0.
  Hypothesis AL8 : Z.land U 7 = 0.
  Hypothesis IM1 : addr_is_in_mem U = true.
  Hypothesis IM2 : addr_is_in_mem (U + round_up size 8 - 8) = true.

  Lemma am_free_app_gen : need_new (as_tq st) = false ->
    exists stX ev0, am_free_full st U = free_tail_m U size stX ev0 [] /\ same_but_shadow stX (free_app_state st0 ch) /\ syscalls_of ev0 = [].
  Proof.
    intros NN. destruct (am_free_unfold st ch FIND ALLOC QMAX AL8 IM1 IM2) as (ev0 & stp & _ & SP & SC0 & E). change (ch_user_beg ch) with U in E. change (ch_used ch) with size in E. change (set_internal_init st) with st0 in SP. rewrite E.
    pose proof (sbs_fields _ _ SP) as (Ftq & Fqc & _).
    assert (TQ0 : as_tq stp = as_tq st) by (rewrite Ftq; subst st0; reflexivity).
    assert (QC0 : as_qcache stp = as_qcache st) by (rewrite Fqc; subst st0; reflexivity).
    unfold quarantine_enqueue. rewrite TQ0. unfold need_new in NN.
    destruct (qc_list (as_tq st)) as [|b0 l0] eqn:EL; [discriminate|]. rewrite NN.
    cbn [as_tq set_tq qc_bytes as_qcache].
    lazymatch goal with |- context [quarantine_drain ?X] => exists X, ev0 end. split; [| split; [| exact SC0]].
    - unfold free_tail_m. cbn [as_tq set_tq qc_bytes as_qcache app]. reflexivity.
    - unfold free_app_state, tq_app. change (ch_chunk_beg (qch ch)) with (ch_chunk_beg ch). fold size.
      replace (as_tq st0) with (as_tq st) by (subst st0; reflexivity). rewrite EL. apply sbs_set_tq. exact SP.
  Qed.

  Lemma am_free_newhit_gen : forall cp rest,
    need_new (as_tq st) = true -> pc_chunks (get_pc st kBatchClass) = cp :: rest -> pc_count (get_pc st kBatchClass) <> 0 ->
    0 < compact_to_addr st kBatchClass cp ->
    exists stX ev0, am_free_full st U = free_tail_m U size stX ev0 [] /\ same_but_shadow stX (free_new_state st0 ch cp rest) /\ syscalls_of ev0 = [].
  Proof.
    intros cp rest NN PCS CNT BPOS. destruct (am_free_unfold st ch FIND ALLOC QMAX AL8 IM1 IM2) as (ev0 & stp & _ & SP & SC0 & E). change (ch_user_beg ch) with U in E. change (ch_used ch) with size in E. change (set_internal_init st) with st0 in SP. rewrite E.
    pose proof (sbs_fields _ _ SP) as (Ftq & Fqc & _ & Fca & Fsb & _).
    assert (TQ0 : as_tq stp = as_tq st) by (rewrite Ftq; subst st0; reflexivity).
    assert (QC0 : as_qcache stp = as_qcache st) by (rewrite Fqc; subst st0; reflexivity).
    assert (PC0 : get_pc stp kBatchClass = get_pc st kBatchClass) by (unfold get_pc; rewrite Fca; subst st0; reflexivity).
    assert (CA0 : forall stx p, as_space_beg stx = as_space_beg st -> compact_to_addr stx kBatchClass p = compact_to_addr st kBatchClass p)
      by (intros stx p Hs; unfold compact_to_addr, region_beg; rewrite Hs; reflexivity).
    unfold quarantine_enqueue. rewrite TQ0. unfold need_new in NN.
    unfold cache_alloc. replace ((kBatchClass =? 0) || (kNumClasses <=? kBatchClass)) with false by reflexivity. rewrite PC0.
    replace (pc_count (get_pc st kBatchClass) =? 0) with false by (symmetry; apply Z.eqb_neq; exact CNT).
    rewrite PCS. rewrite (CA0 (set_pc stp kBatchClass _)) by (cbn; rewrite Fsb; subst st0; reflexivity).
    replace (compact_to_addr st kBatchClass cp =? 0) with false by (symmetry; apply Z.eqb_neq; clear - BPOS; lia).
    assert (NB : forall X : option (astate * list effect),
              (let need_new := match qc_list (as_tq st) with [] => true | _ :: _ => kBatchCount <=? qb_count (last (qc_list (as_tq st)) (mkQB 0 0 0 [])) end in
               if need_new then X
               else let l := qc_list (as_tq st) in let k := length l in let lb := last l (mkQB 0 0 0 []) in
                    let lb' := mkQB (qb_addr lb) (qb_size lb + size) (qb_count lb + 1) (qb_chunks lb ++ [ch_chunk_beg (qch ch)]) in
                    let t1 := mkQC (firstn (k - 1) l ++ [lb']) (qc_bytes (as_tq st) + size) in Some (set_tq stp t1, [])) = X).
    { intros X. destruct (qc_list (as_tq st)); [reflexivity|]. rewrite NN. reflexivity. }
    rewrite NB. clear NB.
    cbn [as_tq set_tq set_pc qc_bytes as_qcache qc_list]. rewrite TQ0.
    lazymatch goal with |- context [quarantine_drain ?X] => exists X, ev0 end. split; [| split; [| exact SC0]].
    - unfold free_tail_m. cbn [as_tq set_tq set_pc qc_bytes as_qcache app]. reflexivity.
    - unfold free_new_state, tq_new. change (ch_chunk_beg (qch ch)) with (ch_chunk_beg ch). fold size.
      replace (as_tq st0) with (as_tq st) by (subst st0; reflexivity).
      replace (get_pc st0 kBatchClass) with (get_pc st kBatchClass) by (subst st0; reflexivity).
      rewrite (CA0 st0) by (subst st0; reflexivity).
      apply sbs_set_tq. apply sbs_set_pc. exact SP.
  Qed.

  Lemma am_free_refill_gen : forall cp rest,
    WF st -> need_new (as_tq st) = true -> pc_count (get_pc st kBatchClass) = 0 ->
    rg_mapped_user (get_region st kBatchClass) + 2 * kUserMapSize <= kFreeArrayOffset ->
    kHighMemBeg <= as_space_beg st /\ as_space_beg st + kSpaceSize <= kHighMemEnd + 1 /\ as_space_beg st mod 4096 = 0 ->
    let r := get_region st kBatchClass in
    firstn (Z.to_nat (rf_n kBatchClass)) (rf_fl1 kBatchClass (rg_num_freed r) (rg_allocated_user r) (rg_mapped_user r) (rg_free_array r)) = cp :: rest ->
    0 < compact_to_addr st kBatchClass cp ->
    exists stX ev0 ev2, am_free_full st U = free_tail_m U size stX ev0 ev2 /\ same_but_shadow stX (free_new_state (refilled st0 kBatchClass) ch cp rest) /\ syscalls_of ev0 = [].
  Proof.
    intros cp rest W NN EMPTY ROOM HM r TAKEN BPOS. destruct (am_free_unfold st ch FIND ALLOC QMAX AL8 IM1 IM2) as (ev0 & stp & _ & SP & SC0 & E). change (ch_user_beg ch) with U in E. change (ch_used ch) with size in E. change (set_internal_init st) with st0 in SP. rewrite E.
    pose proof (sbs_fields _ _ SP) as (Ftq & Fqc & _ & Fca & Fsb & Frg & Fci & Fch).
    assert (TQ0 : as_tq stp = as_tq st) by (rewrite Ftq; subst st0; reflexivity).
    assert (QC0 : as_qcache stp = as_qcache st) by (rewrite Fqc; subst st0; reflexivity).
    assert (PC0 : get_pc stp kBatchClass = get_pc st kBatchClass) by (unfold get_pc; rewrite Fca; subst st0; reflexivity).
    assert (CA0 : forall stx p, as_space_beg stx = as_space_beg st -> compact_to_addr stx kBatchClass p = compact_to_addr st kBatchClass p)
      by (intros stx p Hs; unfold compact_to_addr, region_beg; rewrite Hs; reflexivity).
    assert (W0 : WF st0) by (subst st0; eapply WF_ext; [ .. | exact W]; reflexivity).
    assert (HC : 1 <= kBatchClass <= 30) by (unfold kBatchClass; lia).
    destruct (gfa_cold st0 kBatchClass W0 HC EMPTY ROOM HM) as (stg & evg & EG & SG).
    unfold quarantine_enqueue. rewrite TQ0. unfold need_new in NN.
    unfold cache_alloc. replace ((kBatchClass =? 0) || (kNumClasses <=? kBatchClass)) with false by reflexivity. rewrite PC0, EMPTY. cbn [Z.eqb].
    assert (AG3 : agree3 (ensure_cache_inited st0) (ensure_cache_inited stp)).
    { rewrite !ensure_cache_inited_eq. unfold agree3. cbn. rewrite Fsb, Frg. unfold same_but_shadow in SP. subst st0; cbn in SP |- *.
      repeat split; try reflexivity. symmetry. tauto. }
    pose proof (gfa_transfer (ensure_cache_inited st0) (ensure_cache_inited stp) kBatchClass (max_count kBatchClass / 2) AG3) as GT.
    change (rf_n kBatchClass) with (max_count kBatchClass / 2) in EG, TAKEN. rewrite EG in GT. destruct GT as (b' & EB & SB'). rewrite EB.
    cbn [pc_chunks pc_count]. change (get_region st0 kBatchClass) with r. rewrite TAKEN.
    assert (NB : forall X Y : option (astate * list effect),
              (if match qc_list (as_tq st) with [] => true | _ :: _ => kBatchCount <=? qb_count (last (qc_list (as_tq st)) (mkQB 0 0 0 [])) end then X else Y) = X).
    { intros X Y. destruct (qc_list (as_tq st)); [reflexivity|]. rewrite NN. reflexivity. }
    rewrite NB. clear NB.
    pose proof (sbs_fields _ _ SB') as (Gtq & Gqc & _ & Gca & Gsb & _).
    assert (SB0 : as_space_beg b' = as_space_beg st).
    { rewrite Gsb. cbn. rewrite ensure_cache_inited_eq. cbn. rewrite Fsb. subst st0; reflexivity. }
    rewrite (CA0 (set_pc b' kBatchClass _)) by (cbn; exact SB0).
    replace (compact_to_addr st kBatchClass cp =? 0) with false by (symmetry; apply Z.eqb_neq; clear - BPOS; lia).
    cbn [as_tq set_tq set_pc qc_bytes as_qcache qc_list].
    assert (TQb : as_tq b' = as_tq st) by (rewrite Gtq; cbn; rewrite ensure_cache_inited_eq; cbn; exact TQ0).
    assert (QCb : as_qcache b' = as_qcache st) by (rewrite Gqc; cbn; rewrite ensure_cache_inited_eq; cbn; exact QC0).
    rewrite TQb.
    lazymatch goal with |- context [quarantine_drain ?X] => exists X, ev0 end. eexists. split; [| split; [| exact SC0]].
    { unfold free_tail_m. cbn [as_tq set_tq set_pc qc_bytes as_qcache app]. reflexivity. }
    (* [comment removed for export] *)
    unfold free_new_state, tq_new. change (ch_chunk_beg (qch ch)) with (ch_chunk_beg ch). fold size.
    rewrite (rfd_pc_c st0 kBatchClass W0 HC ROOM). cbn [pc_count refill_pc].
    pose proof (rfd_same st0 kBatchClass) as (Rsb & _ & _ & _ & _ & Rtq & _ & _ & _ & _ & _ & _ & _ & _ & Rca & _).
    rewrite Rtq, Rca. replace (as_tq st0) with (as_tq st) by (subst st0; reflexivity). rewrite (CA0 st0) by (subst st0; reflexivity).
    change (rf_n kBatchClass) with (max_count kBatchClass / 2).
    apply sbs_set_tq.
    (* [comment removed for export] *)
    clear - SP SB' SG W0 HC.
    unfold same_but_shadow, gset in SB', SG |- *. rewrite ensure_cache_inited_eq in SB'. unfold gfa_state in SG.
    unfold set_pc, upd_chunk, set_chunks, refilled. cbn -[refill_region refill_pc refill_newmaps rf_n rf_fl1 get_region compact_to_addr max_count].
    unfold same_but_shadow in SP. subst st0. unfold set_internal_init, upd_chunk, set_chunks in SP, SB', SG |- *.
    cbn -[refill_region refill_pc refill_newmaps rf_n rf_fl1 get_region compact_to_addr max_count] in SP, SB', SG |- *.
    rewrite upd_nth_upd_nth.
    destruct SP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16).
    destruct SB' as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16).
    destruct SG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
    repeat split; congruence.
  Qed.
End FreeModel2.
