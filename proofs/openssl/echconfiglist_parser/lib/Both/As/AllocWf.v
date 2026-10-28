(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record region_ok (st : astate) (c : Z) : Prop := mkRegionOk {
  ro_alloc_nonneg : 0 <= rg_allocated_user (get_region st c);
  ro_alloc_le     : rg_allocated_user (get_region st c) <= rg_mapped_user (get_region st c);
  ro_mapped_mod   : rg_mapped_user (get_region st c) mod kUserMapSize = 0;
  ro_mapped_bound : rg_mapped_user (get_region st c) + kUserMapSize <= kFreeArrayOffset;
  ro_alloc_mod    : class_size c <> 0 -> rg_allocated_user (get_region st c) mod class_size c = 0;
  ro_tail_small   : class_size c <> 0 -> rg_mapped_user (get_region st c) - rg_allocated_user (get_region st c) < class_size c
                                          + (if rg_allocated_user (get_region st c) =? 0 then kUserMapSize else 0);
  ro_empty        : class_size c = 0 -> rg_mapped_user (get_region st c) = 0;
  ro_numfreed     : rg_num_freed (get_region st c) = zlen (rg_free_array (get_region st c));
  ro_fa_le        : 4 * rg_num_freed (get_region st c) <= rg_mapped_free_array (get_region st c);
  ro_fa_mod       : rg_mapped_free_array (get_region st c) mod kFreeArrayMapSize = 0;
  ro_fa_bound     : rg_mapped_free_array (get_region st c) <= kFreeArraySize;
  ro_fa_elems     : forall cp, In cp (rg_free_array (get_region st c)) ->
                      0 <= cp /\ Z.shiftl cp kCompactPtrScale < rg_allocated_user (get_region st c)
                      /\ class_size c <> 0 /\ Z.shiftl cp kCompactPtrScale mod class_size c = 0
}.

(* [comment removed for export] *)
Record cache_ok (st : astate) (c : Z) : Prop := mkCacheOk {
  co_count     : pc_count (get_pc st c) = zlen (pc_chunks (get_pc st c));
  co_bound     : if as_cache_inited st then pc_count (get_pc st c) <= max_count c else pc_count (get_pc st c) = 0;
  co_elems     : forall cp, In cp (pc_chunks (get_pc st c)) ->
                   0 <= cp /\ Z.shiftl cp kCompactPtrScale < rg_allocated_user (get_region st c)
                   /\ class_size c <> 0 /\ Z.shiftl cp kCompactPtrScale mod class_size c = 0
}.

(* [comment removed for export] *)
Definition chunk_ok (st : astate) (ch : chunk) : Prop :=
  let r := compute_req (ch_used ch) in
  1 <= ch_used ch /\ ch_used ch = rq_size r /\ ch_rz ch = rq_rz r /\ ch_user_beg ch = ch_alloc_beg ch + ch_rz ch
  /\ if ch_primary ch then
       let c := ch_class ch in
       rq_primary r = true /\ c = class_id (rq_needed r) /\ c = class_of_addr st (ch_alloc_beg ch)
       /\ in_primary st (ch_alloc_beg ch) = true
       /\ (ch_alloc_beg ch - region_beg st c) mod class_size c = 0
       /\ 0 <= ch_alloc_beg ch - region_beg st c
       /\ ch_alloc_beg ch - region_beg st c + class_size c <= rg_allocated_user (get_region st c)
       /\ rq_needed r <= class_size c
     else
       rq_primary r = false /\ in_primary st (ch_alloc_beg ch) = false
       /\ exists i h, nth_error (as_sec st) i = Some h /\ sc_map_beg h = ch_alloc_beg ch - kPageSize
          /\ sc_size h = rq_needed r /\ sc_map_size h = round_up (sc_size h) kPageSize + kPageSize.

(* [comment removed for export] *)
Definition batch_ok (st : astate) (b : qbatch) : Prop :=
  qb_count b = zlen (qb_chunks b) /\ 1 <= qb_count b <= kBatchCount
  /\ in_primary st (qb_addr b) = true /\ class_of_addr st (qb_addr b) = kBatchClass
  /\ (qb_addr b - region_beg st kBatchClass) mod class_size kBatchClass = 0
  /\ 0 <= qb_addr b - region_beg st kBatchClass
  /\ qb_addr b - region_beg st kBatchClass + class_size kBatchClass <= rg_allocated_user (get_region st kBatchClass)
  /\ qb_size b = kBatchSize + fold_right (fun m acc => match find_chunk (as_chunks st) (m + kChunkHeaderSize) with Some ch => ch_used ch | None => 0 end + acc) 0 (qb_chunks b)
  /\ forall m, In m (qb_chunks b) -> exists ch, find_chunk (as_chunks st) (m + kChunkHeaderSize) = Some ch /\ ch_state ch = CQuarantine.

Definition qcache_ok (st : astate) (q : qcache) : Prop :=
  (forall b, In b (qc_list q) -> batch_ok st b) /\ qc_bytes q = fold_right (fun b acc => qb_size b + acc) 0 (qc_list q).

(* [comment removed for export] *)
Definition carved_addr_list (st : astate) : list Z :=
  flat_map (fun c => map (compact_to_addr st c) (rg_free_array (get_region st c))
                     ++ map (compact_to_addr st c) (pc_chunks (get_pc st c))) (map Z.of_nat (seq 0 32))
  ++ map ch_alloc_beg (filter ch_primary (chunk_list st))
  ++ map qb_addr (qc_list (as_tq st) ++ qc_list (as_gq st)).

Definition WF (st : astate) : Prop :=
     (forall c, 0 <= c < kNumClasses -> region_ok st c /\ cache_ok st c)
  /\ NoDup (carved_addr_list st)
  /\ (forall ch, In ch (chunk_list st) -> chunk_ok st ch)
  /\ (forall ch ch', In ch (chunk_list st) -> In ch' (chunk_list st) -> ch_user_beg ch = ch_user_beg ch' -> ch = ch')
  /\ zlen (filter (fun ch => negb (ch_primary ch)) (chunk_list st)) = zlen (as_sec st)
  /\ NoDup (map sc_map_beg (as_sec st))
  /\ zlen (as_sec st) <= as_n_reserved st /\ (as_n_reserved st = 0 \/ as_n_reserved st = kChunksBlockCount)
  /\ qcache_ok st (as_tq st) /\ qcache_ok st (as_gq st)
  /\ qc_bytes (as_tq st) <= as_qcache st /\ qc_bytes (as_gq st) <= as_qmax st
  /\ NoDup (flat_map qb_chunks (qc_list (as_tq st) ++ qc_list (as_gq st)))
  /\ (forall ch, In ch (chunk_list st) -> ch_state ch = CQuarantine ->
        exists b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) /\ In (ch_chunk_beg ch) (qb_chunks b))
  /\ rg_mapped_user (get_region st 0) = 0 /\ rg_mapped_user (get_region st 31) = 0
  /\ pc_count (get_pc st 0) = 0 /\ pc_count (get_pc st 31) = 0
  /\ length (as_regions st) = 32%nat /\ length (as_cache st) = 32%nat
  /\ as_qmax st = kQuarantineMaxSize /\ as_qmin st = kQuarantineMinSize /\ as_qcache st = kMaxCacheSize
  (* [comment removed for export] *)
  /\ (forall k x, PositiveMap.find k (as_chunks st) = Some x -> k = ckey (ch_user_beg x) /\ 0 < ch_user_beg x).

(* [comment removed for export] *)
Lemma WF_region : forall st c, WF st -> 0 <= c < kNumClasses -> region_ok st c.
Proof. intros st c W Hc. destruct W as [H _]. apply (H c Hc). Qed.
Lemma WF_cache : forall st c, WF st -> 0 <= c < kNumClasses -> cache_ok st c.
Proof. intros st c W Hc. destruct W as [H _]. apply (H c Hc). Qed.
Lemma WF_chunk : forall st ch, WF st -> In ch (chunk_list st) -> chunk_ok st ch.
Proof. intros st ch W Hin. destruct W as (_ & _ & H & _). apply H, Hin. Qed.
Lemma WF_tq : forall st, WF st -> qcache_ok st (as_tq st).
Proof. intros st W. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma WF_gq : forall st, WF st -> qcache_ok st (as_gq st).
Proof. intros st W. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma WF_batch : forall st b, WF st -> In b (qc_list (as_tq st) ++ qc_list (as_gq st)) -> batch_ok st b.
Proof.
  intros st b W Hin. apply in_app_iff in Hin as [Hin|Hin]; [apply (proj1 (WF_tq st W)) | apply (proj1 (WF_gq st W))]; exact Hin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac eval_class_consts :=
  repeat match goal with
  | |- context [class_size ?k] => let v := eval vm_compute in (class_size k) in change (class_size k) with v
  | |- context [max_count ?k] => let v := eval vm_compute in (max_count k) in change (max_count k) with v
  end.
Ltac class_cases c :=
  let rec go k := lazymatch k with
    | 32%Z => lia
    | _ => let k' := eval compute in (k + 1)%Z in
           destruct (Z.eq_dec c k) as [-> | ?]; [eval_class_consts | go k']
    end in go 0%Z.
(* [comment removed for export] *)

Lemma class_size_table_facts : forall c, 0 <= c < 32 ->
  0 <= class_size c <= 65536 /\ class_size c mod 32 = 0 /\ (1 <= c -> 32 <= class_size c)
  /\ 0 <= max_count c <= 16 /\ (1 <= c -> 2 <= max_count c) /\ max_count c mod 2 = 0.
Proof. intros c Hc. class_cases c; repeat split; intros; try reflexivity; lia. Qed.

Lemma rz_size_facts : forall n, 16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0
  /\ (rz_size n = 16 \/ rz_size n = 32 \/ rz_size n = 64 \/ rz_size n = 128 \/ rz_size n = 256 \/ rz_size n = 512 \/ rz_size n = 1024 \/ rz_size n = 2048).
Proof.
  intros n. unfold rz_size, rz_log, kMinRedzoneLog, kMaxRedzoneLog.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; repeat split; try reflexivity; lia.
Qed.
