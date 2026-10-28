(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FMapPositive.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil AsanAllocModel. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocWf AllocKit AG_MallocModel AG_WFHit AS_Refill1 AG_RefillModel AG_ColdModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FreeNum.
  Variable st : astate.
  Hypothesis W : WF st.
  Hypothesis PI : PINV st.
  Hypothesis NAL : nalloc st <= LIVEB.
  Hypothesis EMPTY : pc_count (get_pc st kBatchClass) = 0.
  Hypothesis ROOM : rg_mapped_user (get_region st kBatchClass) + 2 * kUserMapSize <= kFreeArrayOffset.
  Hypothesis HM : kHighMemBeg <= as_space_beg st /\ as_space_beg st + kSpaceSize <= kHighMemEnd + 1 /\ as_space_beg st mod 4096 = 0.

  Lemma NUM_refilled : NUM (refilled st kBatchClass).
  Proof.
    assert (HC : 1 <= kBatchClass <= 30) by (unfold kBatchClass; lia).
    assert (Hc : 1 <= kBatchClass < kNumClasses) by (unfold kBatchClass, kNumClasses; lia).
    destruct PI as [CO NM].
    destruct (gfa_cold st kBatchClass W HC EMPTY ROOM HM) as (stg & evg & EG & SG).
    pose proof (rf_facts st kBatchClass W HC ROOM) as (Q1 & Q2 & _).
    set (r := get_region st kBatchClass) in *.
    set (fl1 := rf_fl1 kBatchClass (rg_num_freed r) (rg_allocated_user r) (rg_mapped_user r) (rg_free_array r)) in *.
    assert (N1 : 1 <= rf_n kBatchClass) by (vm_compute; discriminate).
    assert (NE : exists cp rest, firstn (Z.to_nat (rf_n kBatchClass)) fl1 = cp :: rest).
    { destruct (firstn (Z.to_nat (rf_n kBatchClass)) fl1) as [|cp rest] eqn:E; [exfalso| exists cp, rest; reflexivity].
      apply (f_equal (@length Z)) in E. rewrite length_firstn in E. cbn [length] in E. unfold zlen in Q2. clear - E Q1 Q2 N1. lia. }
    destruct NE as (cp & rest & TAKEN).
    assert (CA : exists st' a, cache_alloc st kBatchClass = Some (st', a, evg) /\ as_regions st' = as_regions stg).
    { unfold cache_alloc. replace ((kBatchClass =? 0) || (kNumClasses <=? kBatchClass)) with false by reflexivity. rewrite EMPTY. cbn [Z.eqb].
      change (max_count kBatchClass / 2) with (rf_n kBatchClass). rewrite EG. cbn [pc_chunks pc_count]. rewrite TAKEN.
      eexists _, _. split; [reflexivity| reflexivity]. }
    destruct CA as (st' & a & CA & RG).
    pose proof (WF_region st kBatchClass W ltac:(unfold kNumClasses in *; lia)) as RO.
    assert (TAIL : rg_mapped_user (get_region st kBatchClass) - rg_allocated_user (get_region st kBatchClass) < class_size kBatchClass + kUserMapSize).
    { assert (CSZ : class_size kBatchClass <> 0) by (change (class_size kBatchClass) with 8192; lia).
      pose proof (ro_tail_small _ _ RO CSZ) as T. destruct (rg_allocated_user (get_region st kBatchClass) =? 0); unfold kUserMapSize in *; lia. }
    destruct (cache_alloc_ncarved st noX kBatchClass st' a evg (WF_cons_pre st kBatchClass W Hc) (ro_numfreed _ _ RO) TAIL ltac:(lia) CO CA) as (OTH & NC & _).
    (* [comment removed for export] *)
    assert (RGR : as_regions st' = as_regions (refilled st kBatchClass)).
    { rewrite RG. destruct SG as (_ & _ & E & _). rewrite E. reflexivity. }
    assert (NCE : forall c0, ncarved (refilled st kBatchClass) c0 = ncarved st' c0) by (intros c0; unfold ncarved, get_region; rewrite RGR; reflexivity).
    intros c0 Hc0. rewrite NCE. destruct (Z.eq_dec c0 kBatchClass) as [->|NEc].
    - destruct NC as [E|B]; [rewrite E; exact (NM _ Hc)|].
      pose proof (own_chunk_bound st kBatchClass W Hc) as OC. pose proof (own_batch_bound st kBatchClass W) as OB.
      unfold CAP, CHB, NBB. replace (zlen (noX kBatchClass)) with 0 in B by reflexivity.
      assert (D0 : 0 <= QTOT / kBatchSize) by (apply Z.div_pos; unfold QTOT, kBatchSize, kQuarantineMaxSize, kMaxCacheSize; lia).
      rewrite Z.eqb_refl in OB |- *. lia.
    - unfold ncarved. rewrite (OTH c0 ltac:(lia) NEc). exact (NM c0 Hc0).
  Qed.
End FreeNum.

(* [comment removed for export] *)
Lemma NUM_regions : forall a b, as_regions a = as_regions b -> NUM b -> NUM a.
Proof. intros a b E N c Hc. unfold ncarved, get_region. rewrite E. exact (N c Hc). Qed.

(* [comment removed for export] *)
Lemma inited_of_count : forall st c, cache_ok st c -> pc_count (get_pc st c) <> 0 -> as_cache_inited st = true.
Proof. intros st c CO NZ. pose proof (co_bound _ _ CO) as B. destruct (as_cache_inited st); [reflexivity| exfalso; exact (NZ B)]. Qed.
(* [comment removed for export] *)
Lemma inited_of_tq : forall st, INITQ st -> qc_list (as_tq st) <> [] -> as_cache_inited st = true.
Proof. intros st [I|[T _]] NE; [exact I| exfalso; exact (NE T)]. Qed.
