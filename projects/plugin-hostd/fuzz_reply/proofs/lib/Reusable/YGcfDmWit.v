(* CARRIED from commit 13dada94373d48ba230c171e98126b88ba98118e,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfDmWit.v, sha256 c33c4141450ba0efd13a2ae9cf2e049755845c8838bc43063f82dbfccd1067b5 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change made here is the module
   prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.
   Plus, in wit_wf, the bullet for WfP_cf's last field wfc_qsize (the cf layer's model-pp, YG01cf.v:173): every
   quarantined witness item is a 1-byte request, req_size 1 <= kQuarantineMax. Proof lines only; no statement changes.
   One writer for fuzz_reply and fuzz_preset (a Theorem Labs lane / Main, 2026-10-30): fuzz_preset takes this blob by path. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30 (free_cf's size test, Quarantine::Put): comment only: item 3 (FREEG's enqueue disjunct and its recycle disjunct; 3(a) now derivable) and its line references. *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), a NON-VACUITY WITNESS for the
   merge arm of h-verbs-5's drain contract (DMspec.v: drain_pre_cf, drain_body_cf, merge_split_cf). It shows a
   state that satisfies Wf_cf and every MODEL premise of drain_pre_cf, with more than 16,384 quarantine batches,
   on which maybe_drain_cf (YG00cf.v:306-320) takes the drain arm, then the recycle branch, then MergeBatches.
   No address, no event count.

   PREMISE MAP. The drain's call site is free_cf's tail (YG00cf.v:350-351): the drain runs on the state X after the
   free's enqueue of the freed chunk k. The free's ENTRY state S carries acall_pre_cf (YG0dcf.v:45-68).
   1. ARX inst ly X W mem md, here ARcf at X (YG0ncf.v:610-612). NO lemma on this base supplies it.
      acall_pre_cf gives ARcf at the entry state S only (YG0dcf.v:233). The AR laws (YG0dcf.v:617-726) keep the
      state fixed (they change memory, world, layout or Hp), so none of them gives ARcf at the new state X.
      The Deallocate walk must re-establish it after the enqueue, as cgif's free walk does at its S'
      (YFfl.v, for example ALedger_S' at :931). Its MODEL part is on this base: Wf_cf at X is
      YG03cf.v:2090-2093 (enqueue_okx_cf, then W5p : WfP_cf U 0 1 0 s5), weakened by WfP_cf_weaken
      (YG01cf.v:300-317); ARcf carries Wf_cf as its field amc_wf (YG0ncf.v:214).
   2. kQuarantineCacheMax < qc_bytes (st_qthread X): the drain's own branch condition. maybe_drain_cf tests
      `qc_bytes (st_qthread s) <=? kQuarantineCacheMax` (YG00cf.v:308; split by name in YG03dcf.v:194-202) and
      the drain arm is the false branch; DMspec.v's maybe_drain_cf_drain is the bridge. No lemma is needed.
   3. qloose X (YG01.v:339-340). Its source is acall_pre_cf's qmeter_cf (YG0dcf.v:239), that is
      qtight S /\ mroom_cf S (YG0ncf.v:447; qtight YG01.v:337-338). X is reached through the enqueue only on free_cf's
      enqueue side (ck_n k <= kQuarantineMax; a larger chunk is recycled at once and the queues do not change, FREEG's
      third disjunct). Between S and X the free changes the queue only by the flip of k to CQuarantined and its enqueue
      (FREEG's enqueue disjunct, YGcfRoom.v; qc_push, YG00.v:438-445). So all three clauses are derivable:
      (b) qc_bytes (st_qglobal X) <= 2 ^ 30: the global queue does not change (YGcfRoom.v:939) and qtight gives
          <= kQuarantineMax = 2 ^ 28.
      (c) quar_n X <= queued_n X + 2 ^ 30: both sides grow by ck_n k (unq_flip_cf YG03cf.v:854, unq_push_cf
          :857, used at :2094-2095) and qtight gives quar_n S <= queued_n S.
      (a) qc_bytes (st_qthread X) <= 2 ^ 29: qc_push adds ck_n k, plus kBatchBytes when it opens a batch, so the
          bound is kQuarantineCacheMax + kBatchBytes + ck_n k, and on the enqueue side ck_n k <= kQuarantineMax:
          2 ^ 20 + 2 ^ 13 + 2 ^ 28 <= 2 ^ 29, as cgif derives the clause (YFfl.v:925-930) from MALLOC_MAX = 2 ^ 28.
          The request bound is di_shape_cf's premise req_size n <= kQuarantineMax (YGcfDIface.v). (Before free_cf
          took the size test, the clause failed for a request in [535,814,145, 535,822,335] at the old
          cf_malloc_max = 2 ^ 29 - 2 ^ 20: such a request is now recycled at once.)
   4. Z.of_nat (length (all_batches X)) <= L24MAX_cf: batches_bound_cf (YGcfBatch.v:26-38) applied to Wf_cf
      at X (item 1). Supplied.

   THE WITNESS (dmw_state below). The quarantine holds T = 114 thread batches and G = 29,070 global batches,
   29,184 in all, every one FULL: 1,021 quarantined chunks of a 1-byte request each, so b_bytes = 9,213. The
   chunks are class 1 (32 B) records, 29,796,864 of them (953,499,648 B of the class, mapped 953,679,872); the
   batch objects are class kBatchClass records (b_self), 29,184 x 8,192 = 239,075,328 B. Compl0 holds with no
   free-array entry and no per-class cache chunk. The thread cache holds 1,050,282 B (just above 2 ^ 20) and the
   global queue 267,821,910 B (within kQuarantineMax, dmw_state_global_tight), so transfer_g carries
   268,872,192 B > 2 ^ 28 over L = 29,184 batches, with 8,192 * L = 239,075,328 < 268,872,192 < 2 * 8,192 * L:
   Recycle's test passes and MergeBatches runs. Every Wf_cf field is proved for any T, G under one room
   condition (wit_room); the numbers enter only in section 7, one lemma per conjunct (dmw_wf, dmw_thread_over,
   dmw_QB, dmw_batches, dmw_merge). DMspec.v's QB at the cf instance is QB_cf, the thread-byte bound that
   replaces qloose; dmw_qloose shows the witness meets qloose too, and dmw_qv_bytes bounds the whole queue for
   DIface's qv_view. Nothing large is computed: the counts are Z.to_nat numerals, related to Z by Z2Nat.id. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith PeanoNat List Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YGcfNames YG01cf YGcfBatch.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* transfer_g, VERBATIM from YFeu.v:157-158 (the definition DMspec.v uses: cgif's YFeu.v:156-157): the global
   list, then the thread list. YFeu.v is NOT imported: it needs YF0x.v, an UNRELOCATED cgif twin (commit
   8053f85d818) that does not compile against preset's binary (YF0x.v:35, "Unable to unify None"). The two
   definitions are the same term, so they agree by reflexivity wherever both are in scope. *)
Definition transfer_g (X : astate) : qcache :=
  mkQC (qc_list (st_qglobal X) ++ qc_list (st_qthread X)) (qc_bytes (st_qglobal X) + qc_bytes (st_qthread X)).

Section DMW.
Context {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 1. The state, for T thread batches and G global batches.                      *)
Definition wS : nat := Z.to_nat kBatchSlots.

Lemma wS_Z : Z.of_nat wS = kBatchSlots.
Proof. unfold wS. apply Z2Nat.id. unfold kBatchSlots. lia. Qed.

(* Item j: a quarantined chunk of a 1-byte request, the j-th class 1 record. *)
Definition wit_item (j : nat) : chunk :=
  mkChunk (PPrim (region_off 1 + 32 * Z.of_nat j)) 1 CQuarantined.

(* Batch i: the i-th class kBatchClass record, holding items wS * i .. wS * i + wS - 1. *)
Definition wit_batch (i : nat) : batch :=
  mkBatch (region_off kBatchClass + kBatchBytes * Z.of_nat i) (map wit_item (seq (wS * i)%nat wS)).

Definition wit_batches (a n : nat) : list batch := map wit_batch (seq a n).

Definition wit_qc (l : list batch) : qcache := mkQC l (sum_bytes l).

(* The record count of class c. *)
Definition wit_K (T G : nat) (c : Z) : nat :=
  if c =? 1 then (wS * (T + G))%nat else if c =? kBatchClass then (T + G)%nat else 0%nat.

Definition wit_alloc (T G : nat) (c : Z) : Z := class_size c * Z.of_nat (wit_K T G c).

Definition wit_reg (T G : nat) (c : Z) : region :=
  mkRegion (round_up (wit_alloc T G c) kUserMapSize) (wit_alloc T G c) 0 [] [].

Definition wit_nev : Z := 2 ^ 32.

Definition wit_state (T G : nat) : astate :=
  mkA (map (fun i => wit_reg T G (Z.of_nat i)) (seq 0 32)) true
    (map (fun i => mkPC (max_cached (Z.of_nat i)) []) (seq 0 32))
    (map wit_item (seq 0 (wS * (T + G))))
    [] [] 0 (wit_qc (wit_batches 0 T)) (wit_qc (wit_batches T G))
    (mkFS (repeat 0 11) []) [] true wit_nev.

(* The one room condition: class 1's records fit under kFreeArrayOffset with a map's slack. *)
Definition wit_room (T G : nat) : Prop :=
  32 * kBatchSlots * Z.of_nat (T + G) + kUserMapSize <= kFreeArrayOffset.

(* ---------------------------------------------------------------------------- *)
(* 2. List facts.                                                                *)
Lemma nth_map_seq {X : Type} (f : nat -> X) (d : X) (n i : nat) :
  (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof.
  intros H. rewrite nth_indep with (d' := f O) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Lemma NoDup_map_inj {A B : Type} (f : A -> B) :
  (forall x y, f x = f y -> x = y) -> forall l, NoDup l -> NoDup (map f l).
Proof.
  intros Hf l H. induction H as [|x l Hx H IH]; cbn [map].
  - constructor.
  - constructor; [|exact IH]. intros Hin. apply in_map_iff in Hin as (y & Hy & Hin).
    apply Hf in Hy. subst y. contradiction.
Qed.

(* YG00's removelast, the one wf_quar names. *)
Lemma Forall_removelast_wit {X : Type} (P : X -> Prop) : forall l, Forall P l -> Forall P (removelast l).
Proof.
  intros l H. induction H as [|x l Hx H IH]; [constructor|].
  destruct l as [|y l']; [constructor|]. cbn [removelast]. constructor; [exact Hx | exact IH].
Qed.

Lemma rup_props : forall a, 0 <= a ->
  (a <= round_up a kUserMapSize < a + kUserMapSize) /\ round_up a kUserMapSize mod kUserMapSize = 0.
Proof.
  intros a Ha. unfold round_up, kUserMapSize.
  pose proof (Z.div_mod (a + 262144 - 1) 262144 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (a + 262144 - 1) 262144 ltac:(lia)) as P.
  split; [lia|]. apply Z.mod_mul. lia.
Qed.

Lemma region_off_1 : region_off 1 = 2 ^ 32.
Proof. reflexivity. Qed.

Lemma prim_class_item : forall x, 0 <= x < 2 ^ 32 -> prim_class (region_off 1 + x) = 1.
Proof.
  intros x Hx. unfold prim_class. rewrite region_off_1, Z.shiftr_div_pow2 by lia.
  symmetry. apply (Z.div_unique _ _ _ x); [left; lia | lia].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The queue.                                                                 *)
Lemma all_batches_wit : forall T G, all_batches (wit_state T G) = wit_batches 0 (T + G).
Proof.
  intros T G. unfold all_batches, wit_state, wit_qc, wit_batches. cbn [st_qthread st_qglobal qc_list].
  rewrite seq_app, map_app. reflexivity.
Qed.

Lemma wit_all_len : forall T G, length (all_batches (wit_state T G)) = (T + G)%nat.
Proof. intros T G. rewrite all_batches_wit. unfold wit_batches. rewrite length_map, length_seq. reflexivity. Qed.

Lemma flat_items_wit : forall n a, flat_map b_items (wit_batches a n) = map wit_item (seq (wS * a) (wS * n)).
Proof.
  induction n as [|n IH]; intros a.
  - rewrite Nat.mul_0_r. reflexivity.
  - unfold wit_batches in *. cbn [seq map flat_map]. rewrite IH. cbn [wit_batch b_items].
    rewrite <- map_app. f_equal.
    rewrite (Nat.mul_succ_r wS n), (Nat.add_comm (wS * n) wS), seq_app, (Nat.mul_succ_r wS a). reflexivity.
Qed.

Lemma q_items_wit : forall T G, q_items (wit_state T G) = st_chunks (wit_state T G).
Proof. intros T G. unfold q_items. rewrite all_batches_wit, flat_items_wit, Nat.mul_0_r. reflexivity. Qed.

Lemma items_bytes : forall l, fold_right (fun k acc => ck_n k + acc) 0 (map wit_item l) = Z.of_nat (length l).
Proof.
  induction l as [|j l IH]; [reflexivity|]. cbn [map fold_right length]. rewrite IH, Nat2Z.inj_succ.
  change (ck_n (wit_item j)) with 1. lia.
Qed.

Lemma b_bytes_wit : forall i, b_bytes (wit_batch i) = kBatchBytes + kBatchSlots.
Proof. intros i. unfold b_bytes. cbn [wit_batch b_items]. rewrite items_bytes, length_seq, wS_Z. reflexivity. Qed.

Lemma sum_bytes_wit : forall n a, sum_bytes (wit_batches a n) = Z.of_nat n * (kBatchBytes + kBatchSlots).
Proof.
  induction n as [|n IH]; intros a; [reflexivity|].
  unfold wit_batches, sum_bytes in *. cbn [seq map fold_right]. rewrite IH, b_bytes_wit, Nat2Z.inj_succ.
  unfold kBatchBytes, kBatchSlots. lia.
Qed.

Lemma wit_batches_full : forall a n, Forall bfull (wit_batches a n).
Proof.
  intros a n. unfold wit_batches. apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (i & <- & _).
  unfold bfull. cbn [wit_batch b_items]. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma blocks_bytes_items : forall l,
  fold_right (fun k acc => if is_alloc k then ck_req k + acc else acc) 0 (map wit_item l) = 0.
Proof. induction l as [|j l IH]; [reflexivity|]. cbn [map fold_right]. exact IH. Qed.

Lemma quar_items_eq : forall l, quar_nl (map wit_item l) = items_n (map wit_item l).
Proof.
  induction l as [|j l IH]; [reflexivity|]. unfold quar_nl, items_n in *. cbn [map fold_right].
  rewrite IH. reflexivity.
Qed.

Lemma begs_nodup : forall l, NoDup l -> NoDup (map ck_beg (map wit_item l)).
Proof.
  intros l H. rewrite map_map. apply NoDup_map_inj; [|exact H].
  intros x y E. cbn [wit_item ck_beg] in E. injection E as E. apply Nat2Z.inj. lia.
Qed.

Lemma wit_qt_bytes : forall T G, qc_bytes (st_qthread (wit_state T G)) = Z.of_nat T * (kBatchBytes + kBatchSlots).
Proof. intros T G. exact (sum_bytes_wit T 0). Qed.

Lemma wit_qg_bytes : forall T G, qc_bytes (st_qglobal (wit_state T G)) = Z.of_nat G * (kBatchBytes + kBatchSlots).
Proof. intros T G. exact (sum_bytes_wit G T). Qed.

Lemma wit_qlens : forall T G,
  length (qc_list (st_qglobal (wit_state T G))) = G /\ length (qc_list (st_qthread (wit_state T G))) = T.
Proof.
  intros T G. unfold wit_state, wit_qc, wit_batches. cbn [st_qglobal st_qthread qc_list].
  rewrite !length_map, !length_seq. split; reflexivity.
Qed.

Lemma wit_quar_eq : forall T G, quar_n (wit_state T G) = queued_n (wit_state T G).
Proof.
  intros T G. unfold quar_n, queued_n. rewrite q_items_wit.
  change (st_chunks (wit_state T G)) with (map wit_item (seq 0 (wS * (T + G)))). apply quar_items_eq.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The classes.                                                               *)
Lemma wit_reg_at : forall T G c, 0 <= c <= 31 -> reg (wit_state T G) c = wit_reg T G c.
Proof.
  intros T G c Hc. unfold reg, znth, wit_state. cbn [st_regions].
  rewrite nth_map_seq by lia. cbv beta. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma wit_cache_at : forall T G c, 0 <= c <= 31 -> cache (wit_state T G) c = mkPC (max_cached c) [].
Proof.
  intros T G c Hc. unfold cache, znth, wit_state. cbn [st_cache].
  rewrite nth_map_seq by lia. cbv beta. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma wit_room_items : forall T G, wit_room T G ->
  32 * Z.of_nat (wS * (T + G)) + kUserMapSize <= kFreeArrayOffset.
Proof. intros T G H. unfold wit_room in H. rewrite Nat2Z.inj_mul, wS_Z. unfold kBatchSlots in *. lia. Qed.

Lemma alloc_bound : forall T G c, wit_room T G ->
  0 <= wit_alloc T G c /\ wit_alloc T G c + kUserMapSize <= kFreeArrayOffset.
Proof.
  intros T G c HR. pose proof (wit_room_items T G HR) as H1. unfold wit_room in HR.
  pose proof (Nat2Z.is_nonneg (T + G)) as N0. pose proof (Nat2Z.is_nonneg (wS * (T + G))) as N1.
  unfold wit_alloc, wit_K.
  destruct (Z.eqb_spec c 1) as [->|E1]; cbv beta iota.
  - change (class_size 1) with 32. lia.
  - destruct (Z.eqb_spec c kBatchClass) as [->|E2]; cbv beta iota.
    + change (class_size kBatchClass) with 8192. unfold kBatchSlots, kUserMapSize, kFreeArrayOffset in *. lia.
    + change (Z.of_nat 0) with 0. rewrite Z.mul_0_r. unfold kUserMapSize, kFreeArrayOffset. lia.
Qed.

Lemma chunk_offs_items : forall s l c,
  st_chunks s = map wit_item l -> Forall (fun j => 32 * Z.of_nat j < 2 ^ 32) l ->
  chunk_offs s c = if c =? 1 then map (fun j => 32 * Z.of_nat j) l else [].
Proof.
  intros s l c E HF. unfold chunk_offs. rewrite E. clear E.
  induction HF as [|j l Hj HF IH].
  - destruct (c =? 1); reflexivity.
  - cbn [map flat_map wit_item ck_beg].
    rewrite prim_class_item by (pose proof (Nat2Z.is_nonneg j); lia).
    rewrite IH, (Z.eqb_sym 1 c).
    destruct (Z.eqb_spec c 1) as [->|_]; [|reflexivity].
    cbn [app map]. f_equal. lia.
Qed.

Lemma batch_offs_wit : forall T G c, batch_offs (wit_state T G) c =
  if c =? kBatchClass then map (fun i => kBatchBytes * Z.of_nat i) (seq 0 (T + G)) else [].
Proof.
  intros T G c. unfold batch_offs. destruct (c =? kBatchClass); [|reflexivity].
  rewrite all_batches_wit. unfold wit_batches. rewrite map_map. apply map_ext. intros i.
  cbn [wit_batch b_self]. ring.
Qed.

(* Class c's records, in the order class_elems lists them, are the first wit_K c slots. *)
Lemma elems_wit : forall T G c, wit_room T G -> 1 <= c <= 31 ->
  chunk_offs (wit_state T G) c ++ batch_offs (wit_state T G) c =
  map (fun j => class_size c * Z.of_nat j) (seq 0 (wit_K T G c)).
Proof.
  intros T G c HR Hc. pose proof (wit_room_items T G HR) as H1.
  assert (HF : Forall (fun j => 32 * Z.of_nat j < 2 ^ 32) (seq 0 (wS * (T + G)))).
  { apply Forall_forall. intros j Hj. apply in_seq in Hj. cbv beta.
    assert (Z.of_nat j < Z.of_nat (wS * (T + G))) by (apply Nat2Z.inj_lt; lia).
    unfold kUserMapSize, kFreeArrayOffset in H1. lia. }
  rewrite (chunk_offs_items (wit_state T G) (seq 0 (wS * (T + G))) c eq_refl HF), batch_offs_wit.
  unfold wit_K.
  destruct (Z.eqb_spec c 1) as [E1|E1]; destruct (Z.eqb_spec c kBatchClass) as [E2|E2]; cbv beta iota.
  - exfalso. unfold kBatchClass in E2. lia.
  - subst c. rewrite app_nil_r. reflexivity.
  - subst c. reflexivity.
  - reflexivity.
Qed.

Lemma cls_ok_cf_wit : forall c (n : nat) ko bo,
  1 <= c <= 31 ->
  ko ++ bo = map (fun j => class_size c * Z.of_nat j) (seq 0 n) ->
  class_size c * Z.of_nat n + kUserMapSize <= kFreeArrayOffset ->
  cls_ok_cf c (mkRegion (round_up (class_size c * Z.of_nat n) kUserMapSize) (class_size c * Z.of_nat n) 0 [] [])
    (mkPC (max_cached c) []) true ko bo.
Proof.
  intros c n ko bo Hc E HB.
  pose proof (class_size_32 c Hc) as Hcs.
  pose proof (Nat2Z.is_nonneg n) as Hn.
  assert (Ha : 0 <= class_size c * Z.of_nat n) by nia.
  destruct (rup_props _ Ha) as [[R1 R2] R3].
  constructor; cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes pc_max pc_chunks].
  - (* wrc_alloc *) lia.
  - (* wrc_carved *) unfold kMaxSize. lia.
  - (* wrc_mapped_al *) exact R3.
  - (* wrc_alloc_al *) rewrite Z.mul_comm. apply Z.mod_mul. lia.
  - (* wrc_fa *) split; [lia | reflexivity].
  - (* wrc_fa_bound *) unfold kFreeArrayMax. lia.
  - (* wrc_fa_len *) cbn [fa_len]. lia.
  - (* wrc_runs *) constructor.
  - (* wrc_nodup *) unfold fa_elems. cbn [flat_map app]. rewrite E.
    apply NoDup_map_inj; [|apply seq_NoDup]. intros x y Hxy.
    apply Nat2Z.inj. apply (proj1 (Z.mul_cancel_l (Z.of_nat x) (Z.of_nat y) (class_size c) ltac:(lia))).
    exact Hxy.
  - (* wrc_elems *) unfold fa_elems. cbn [flat_map app]. rewrite E.
    apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (j & <- & Hj). apply in_seq in Hj.
    assert (Hjn : Z.of_nat j < Z.of_nat n) by lia. cbv beta.
    split; [nia | rewrite Z.mul_comm; apply Z.mod_mul; lia].
  - (* wrc_holes *) split; constructor.
  - (* wrc_cache *) split; [reflexivity|]. cbn [length]. unfold max_cached. lia.
  - (* wrc_mapped_bound *) lia.
Qed.

Lemma wit_class : forall T G c, wit_room T G -> 1 <= c <= 31 -> wf_class_cf (wit_state T G) c.
Proof.
  intros T G c HR Hc. unfold wf_class_cf.
  rewrite wit_reg_at, wit_cache_at by lia. unfold wit_reg, wit_alloc.
  change (st_cache_inited (wit_state T G)) with true.
  apply cls_ok_cf_wit; [exact Hc | exact (elems_wit T G c HR Hc) | exact (proj2 (alloc_bound T G c HR))].
Qed.

Lemma wit_compl0 : forall T G c, wit_room T G -> 1 <= c <= 31 -> cdef (wit_state T G) c = 0.
Proof.
  intros T G c HR Hc. unfold cdef, class_elems.
  rewrite wit_reg_at, wit_cache_at by lia. unfold wit_reg, fa_elems.
  cbn [rg_alloc_user rg_free pc_chunks flat_map app].
  rewrite (elems_wit T G c HR Hc), length_map, length_seq. unfold wit_alloc. lia.
Qed.

Lemma fold_mapped_le : forall (l : list region) B, 0 <= B -> Forall (fun r => 0 <= rg_mapped_user r <= B) l ->
  fold_right (fun r acc => rg_mapped_user r + acc) 0 l <= Z.of_nat (length l) * B.
Proof.
  intros l B HB H. induction H as [|r l Hr H IH]; cbn [fold_right length]; [lia|].
  rewrite Nat2Z.inj_succ. nia.
Qed.

Lemma prim_user_mapped_wit : forall T G, wit_room T G -> prim_user_mapped (wit_state T G) <= 32 * kFreeArrayOffset.
Proof.
  intros T G HR. unfold prim_user_mapped.
  change (st_regions (wit_state T G)) with (map (fun i => wit_reg T G (Z.of_nat i)) (seq 0 32)).
  assert (HB : 0 <= kFreeArrayOffset) by (unfold kFreeArrayOffset; lia).
  eapply Z.le_trans; [apply (fold_mapped_le _ kFreeArrayOffset HB)|].
  - apply Forall_forall. intros r Hr. apply in_map_iff in Hr as (i & <- & _).
    unfold wit_reg. cbn [rg_mapped_user].
    destruct (alloc_bound T G (Z.of_nat i) HR) as [A1 A2]. destruct (rup_props _ A1) as [[R1 R2] _]. lia.
  - rewrite length_map, length_seq. change (Z.of_nat 32) with 32. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. The record fields that are not per class.                                  *)
Lemma item_ok : forall s j, 32 * Z.of_nat j < 2 ^ 32 -> chunk_ok_cf s (wit_item j).
Proof.
  intros s j Hj. pose proof (Nat2Z.is_nonneg j) as Hj0. pose proof cf_malloc_max_pos as Hm.
  unfold chunk_ok_cf. cbn [wit_item ck_req ck_beg].
  rewrite prim_class_item by lia.
  split; [lia|]. split; [reflexivity|]. split; [reflexivity | lia].
Qed.

Lemma wit_quar : forall T G, wf_quar (wit_state T G).
Proof.
  intros T G. constructor.
  - (* wq_bytes_t *) reflexivity.
  - (* wq_bytes_g *) reflexivity.
  - (* wq_batches *) rewrite all_batches_wit. eapply Forall_impl; [|apply wit_batches_full].
    intros b Hb. cbv beta. unfold bfull in Hb. rewrite Hb. unfold kBatchSlots. lia.
  - (* wq_items *) rewrite q_items_wit. apply Forall_forall. intros k Hk. split; [exact Hk|].
    change (st_chunks (wit_state T G)) with (map wit_item (seq 0 (wS * (T + G)))) in Hk.
    apply in_map_iff in Hk as (j & <- & _). reflexivity.
  - (* wq_nodup *) rewrite q_items_wit.
    change (st_chunks (wit_state T G)) with (map wit_item (seq 0 (wS * (T + G)))).
    apply begs_nodup, seq_NoDup.
  - (* wq_tfull *) change (qc_list (st_qthread (wit_state T G))) with (wit_batches 0 T).
    apply Forall_removelast_wit, wit_batches_full.
  - (* wq_groups: one segment F, no group *) exists (wit_batches T G), []. split; [|split].
    + cbn [concat]. rewrite app_nil_r. reflexivity.
    + apply Forall_removelast_wit, wit_batches_full.
    + apply Forall_nil.
Qed.

Lemma wit_sec : forall T G, wf_sec_cf (wit_state T G).
Proof.
  intros T G. constructor.
  - (* wsc_nodup *) apply NoDup_nil.
  - (* wsc_arr_chunks *) intros r. split.
    + intros Hr. change (st_sec_arr (wit_state T G)) with (@nil nat) in Hr. destruct Hr.
    + intros (k & Hk & Hb).
      change (st_chunks (wit_state T G)) with (map wit_item (seq 0 (wS * (T + G)))) in Hk.
      apply in_map_iff in Hk as (j & <- & _). discriminate Hb.
  - (* wsc_arr_live *) intros r. split.
    + intros Hr. change (st_sec_arr (wit_state T G)) with (@nil nat) in Hr. destruct Hr.
    + intros (sm & H & _). change (st_secs (wit_state T G)) with (@nil secmap) in H. destruct r; discriminate H.
  - (* wsc_reserved *) change (st_sec_arr (wit_state T G)) with (@nil nat).
    change (st_sec_reserved (wit_state T G)) with 0. cbn [length]. unfold kPtrArrayEntriesPerCommit. lia.
  - (* wsc_reserved_al *) change (st_sec_reserved (wit_state T G)) with 0. split; [lia | reflexivity].
  - (* wsc_lens *) apply Forall_nil.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 6. Wf_cf, for any T and G under the room condition.                           *)
Lemma wit_wf : forall T G, wit_room T G -> Wf_cf (univ_of [] []) (wit_state T G).
Proof.
  intros T G HR. pose proof (wit_room_items T G HR) as H1.
  assert (HN : Z.of_nat (wS * (T + G)) <= 2 ^ 32) by (unfold kUserMapSize, kFreeArrayOffset in H1; lia).
  assert (HNB : Z.of_nat (T + G) <= Z.of_nat (wS * (T + G))).
  { rewrite Nat2Z.inj_mul, wS_Z. pose proof (Nat2Z.is_nonneg (T + G)). unfold kBatchSlots. lia. }
  unfold Wf_cf. constructor.
  - (* wfc_len_regions *) unfold wit_state. cbn [st_regions]. rewrite length_map, length_seq. reflexivity.
  - (* wfc_len_cache *) unfold wit_state. cbn [st_cache]. rewrite length_map, length_seq. reflexivity.
  - (* wfc_reg0 *) rewrite wit_reg_at by lia. reflexivity.
  - (* wfc_classes *) intros c Hc. exact (wit_class T G c HR Hc).
  - (* wfc_chunks *) change (st_chunks (wit_state T G)) with (map wit_item (seq 0 (wS * (T + G)))).
    apply Forall_forall. intros k Hk. apply in_map_iff in Hk as (j & <- & Hj). apply in_seq in Hj.
    apply item_ok. assert (Z.of_nat j < Z.of_nat (wS * (T + G))) by (apply Nat2Z.inj_lt; lia).
    unfold kUserMapSize, kFreeArrayOffset in H1. lia.
  - (* wfc_chunks_nodup *) change (st_chunks (wit_state T G)) with (map wit_item (seq 0 (wS * (T + G)))).
    apply begs_nodup, seq_NoDup.
  - (* wfc_chunks_ev *) change (st_chunks (wit_state T G)) with (map wit_item (seq 0 (wS * (T + G)))).
    change (st_nev (wit_state T G)) with wit_nev. rewrite length_map, length_seq. unfold wit_nev. lia.
  - (* wfc_prim_ev *) pose proof (prim_user_mapped_wit T G HR) as P. change (st_nev (wit_state T G)) with wit_nev.
    unfold wit_nev, kUserMapSize, kFreeArrayOffset in *. lia.
  - (* wfc_live *) unfold blocks_bytes.
    change (st_chunks (wit_state T G)) with (map wit_item (seq 0 (wS * (T + G)))).
    rewrite blocks_bytes_items. unfold LIVE_MAX. lia.
  - (* wfc_quarantine *) apply wit_quar.
  - (* wfc_batches_ev *) rewrite wit_all_len. change (st_nev (wit_state T G)) with wit_nev. unfold wit_nev. lia.
  - (* wfc_secondary *) apply wit_sec.
  - (* wfc_fakestack *) constructor.
    + change (fs_hint (st_fs (wit_state T G))) with (repeat 0 11). split; [reflexivity|].
      apply Forall_forall. intros h Hh. apply repeat_spec in Hh. cbv beta. lia.
    + apply NoDup_nil.
    + apply Forall_nil.
  - (* wfc_depot *) apply depot_fits_nil.
  - (* wfc_nev *) change (st_nev (wit_state T G)) with wit_nev. unfold wit_nev. lia.
  - (* wfc_slack *) lia.
  - (* wfc_qinited *) intros _. reflexivity.
  - (* wfc_secs_ev *) change (st_secs (wit_state T G)) with (@nil secmap).
    change (st_nev (wit_state T G)) with wit_nev. cbn [length]. unfold wit_nev. lia.
  - (* wfc_compl0 *) intros c Hc. exact (wit_compl0 T G c HR Hc).
  - (* wfc_sec_live *) change (st_sec_arr (wit_state T G)) with (@nil nat).
    pose proof cf_sec_live_nonneg. cbn [length]. lia.
  - (* wfc_qsize *) rewrite q_items_wit.
    change (st_chunks (wit_state T G)) with (map wit_item (seq 0 (wS * (T + G)))).
    apply Forall_forall. intros k Hk. apply in_map_iff in Hk as (j & <- & _).
    unfold ck_n, req_size, kQuarantineMax. cbn [wit_item ck_req]. destruct (1 =? 0); lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 7. The witness: T = 114, G = 29,070.                                          *)
Definition dmw_T : nat := Z.to_nat 114.
Definition dmw_G : nat := Z.to_nat 29070.
Definition dmw_state : astate := wit_state dmw_T dmw_G.

Lemma dmw_T_Z : Z.of_nat dmw_T = 114.
Proof. unfold dmw_T. apply Z2Nat.id. lia. Qed.

Lemma dmw_G_Z : Z.of_nat dmw_G = 29070.
Proof. unfold dmw_G. apply Z2Nat.id. lia. Qed.

Lemma dmw_NB : Z.of_nat (dmw_T + dmw_G) = 29184.
Proof. rewrite Nat2Z.inj_add, dmw_T_Z, dmw_G_Z. reflexivity. Qed.

Lemma dmw_room : wit_room dmw_T dmw_G.
Proof. unfold wit_room. rewrite dmw_NB. unfold kBatchSlots, kUserMapSize, kFreeArrayOffset. lia. Qed.

Lemma dmw_thread_bytes : qc_bytes (st_qthread dmw_state) = 1050282.
Proof. unfold dmw_state. rewrite wit_qt_bytes, dmw_T_Z. reflexivity. Qed.

Lemma dmw_global_bytes : qc_bytes (st_qglobal dmw_state) = 267821910.
Proof. unfold dmw_state. rewrite wit_qg_bytes, dmw_G_Z. reflexivity. Qed.

(* One lemma per conjunct of dm_merge_witness_cf, so a changed conjunct is a one-line swap. *)
Lemma dmw_wf : Wf_cf (univ_of [] []) dmw_state.
Proof. exact (wit_wf dmw_T dmw_G dmw_room). Qed.

Lemma dmw_thread_over : kQuarantineCacheMax < qc_bytes (st_qthread dmw_state).
Proof. rewrite dmw_thread_bytes. unfold kQuarantineCacheMax. lia. Qed.

Lemma dmw_qloose : qloose dmw_state.
Proof. unfold qloose. rewrite dmw_thread_bytes, dmw_global_bytes. unfold dmw_state. rewrite wit_quar_eq. lia. Qed.

(* The cf thread-byte bound, DMspec.v's QB at the cf instance (h-verbs-5, 2026-10-29 00:40Z): it replaces
   qloose, whose thread clause does not hold at every cf drain entry (premise map, item 3). cf_malloc_max is the
   cf request bound (CfParams, YGcfNames.v:174). *)
Definition QB_cf (X : astate) : Prop := qc_bytes (st_qthread X) <= kQuarantineCacheMax + cf_malloc_max + kBatchBytes.

Lemma dmw_thread_cf_bound : qc_bytes (st_qthread dmw_state) <= kQuarantineCacheMax + cf_malloc_max + kBatchBytes.
Proof.
  rewrite dmw_thread_bytes. pose proof cf_malloc_max_pos as Hm. unfold kQuarantineCacheMax, kBatchBytes. lia.
Qed.

Lemma dmw_QB : QB_cf dmw_state.
Proof. exact dmw_thread_cf_bound. Qed.

(* The whole queue's bytes, for DIface's qv_view. *)
Lemma dmw_qv_bytes : qc_bytes (st_qthread dmw_state) + qc_bytes (st_qglobal dmw_state) <= 2 ^ 31.
Proof. rewrite dmw_thread_bytes, dmw_global_bytes. lia. Qed.

Lemma dmw_batches : 16384 < Z.of_nat (length (all_batches dmw_state)) <= L24MAX_cf.
Proof. unfold dmw_state. rewrite wit_all_len, dmw_NB, L24MAX_cf_value. lia. Qed.

Lemma dmw_merge : let g := transfer_g dmw_state in kQuarantineMax < qc_bytes g /\
  kBatchBytes * Z.of_nat (length (qc_list g)) < qc_bytes g < 2 * (kBatchBytes * Z.of_nat (length (qc_list g))).
Proof.
  cbv zeta. unfold transfer_g. cbn [qc_list qc_bytes].
  rewrite dmw_thread_bytes, dmw_global_bytes, length_app.
  unfold dmw_state. destruct (wit_qlens dmw_T dmw_G) as [LG LT].
  rewrite LG, LT, Nat2Z.inj_add, dmw_T_Z, dmw_G_Z. unfold kQuarantineMax, kBatchBytes. lia.
Qed.

Lemma dm_merge_witness_cf : exists U X, Wf_cf U X /\ kQuarantineCacheMax < qc_bytes (st_qthread X) /\ QB_cf X /\
  16384 < Z.of_nat (length (all_batches X)) <= L24MAX_cf /\
  let g := transfer_g X in kQuarantineMax < qc_bytes g /\
  kBatchBytes * Z.of_nat (length (qc_list g)) < qc_bytes g < 2 * (kBatchBytes * Z.of_nat (length (qc_list g))).
Proof.
  exists (univ_of [] []), dmw_state.
  split; [exact dmw_wf|]. split; [exact dmw_thread_over|]. split; [exact dmw_QB|].
  split; [exact dmw_batches | exact dmw_merge].
Qed.

(* The witness is the shape of a real drain entry: its global queue is within the bound a drain leaves. *)
Lemma dmw_state_global_tight : qc_bytes (st_qglobal dmw_state) <= kQuarantineMax.
Proof. rewrite dmw_global_bytes. unfold kQuarantineMax. lia. Qed.

End DMW.
