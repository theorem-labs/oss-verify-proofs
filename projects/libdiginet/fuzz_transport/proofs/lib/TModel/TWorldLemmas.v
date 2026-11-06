From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Mem Cells Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld.
Import ListNotations.
Open Scope Z_scope.

(* TWorld's upd is the kit's upd_bytes (Lib/Mem.v:193) at a Z offset. *)
Lemma upd_upd_bytes : forall (bs v : list byte) k, upd bs k v = upd_bytes bs (Z.to_nat k) v.
Proof. reflexivity. Qed.

(* ---- copied from disco Prog/disco_table.v:11-63 ---- *)

Lemma nth_skipn : forall {X} n (l : list X) i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  intros X n. induction n as [|n IH]; intros l i; [reflexivity|].
  destruct l as [|x l]; [destruct i; reflexivity|]. cbn. apply IH.
Qed.

Lemma ble_range : forall bs, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  intros bs. rewrite bytes_le_to_Z_le_val.
  pose proof (le_val_range _ (bytes_ok_map bs)) as H. rewrite map_length in H.
  rewrite Z.pow_mul_r by lia. exact H.
Qed.

Lemma length_sub : forall bs k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) -> length (sub bs k n) = n.
Proof. intros bs k n Hk H. unfold sub. rewrite firstn_length, skipn_length. lia. Qed.

(* ---- copied from disco Prog/slot_observe.v:10-138 ---- *)

Lemma ne_firstn : forall {A} n (l : list A) i, nth_error (firstn n l) i = if (i <? n)%nat then nth_error l i else None.
Proof.
  intros A n. induction n as [|n IH]; intros l i; [destruct i; reflexivity|].
  destruct l as [|x l]; destruct i as [|i]; cbn [firstn nth_error];
    [reflexivity | destruct (S i <? S n)%nat; reflexivity | reflexivity | rewrite IH; reflexivity].
Qed.

Lemma ne_sub : forall (bs : list byte) k n i, 0 <= k ->
  nth_error (sub bs k n) i = if (i <? n)%nat then nth_error bs (Z.to_nat k + i) else None.
Proof. intros bs k n i Hk. unfold sub. rewrite ne_firstn. destruct (i <? n)%nat; [apply nth_skipn | reflexivity]. Qed.

Lemma ne_upd : forall (bs v : list byte) k i, 0 <= k -> (Z.to_nat k + length v <= length bs)%nat ->
  nth_error (upd bs k v) i =
  if ((Z.to_nat k <=? i) && (i <? Z.to_nat k + length v))%nat then nth_error v (i - Z.to_nat k) else nth_error bs i.
Proof.
  intros bs v k i Hk Hl. rewrite upd_upd_bytes. unfold upd_bytes. set (K := Z.to_nat k) in *.
  destruct (Nat.ltb_spec i K).
  - rewrite nth_error_app1 by (rewrite length_firstn; lia). rewrite ne_firstn.
    replace (i <? K)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    replace (K <=? i)%nat with false by (symmetry; apply Nat.leb_gt; lia). reflexivity.
  - rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn, Nat.min_l by lia.
    replace (K <=? i)%nat with true by (symmetry; apply Nat.leb_le; lia). cbn [andb].
    destruct (Nat.ltb_spec i (K + length v)).
    + rewrite nth_error_app1 by lia. reflexivity.
    + rewrite nth_error_app2 by lia. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma length_upd : forall (bs v : list byte) k, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  length (upd bs k v) = length bs.
Proof. intros bs v k Hk H. rewrite upd_upd_bytes. apply upd_bytes_length. lia. Qed.

Lemma len_ite : forall (c : bool) (bs v : list byte) k, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  length (if c then upd bs k v else bs) = length bs.
Proof. intros [|] bs v k Hk H; [apply length_upd; assumption | reflexivity]. Qed.

Lemma sub_upd_out : forall (bs v : list byte) k k' n, 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= k') -> k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  sub (upd bs k v) k' n = sub bs k' n.
Proof.
  intros bs v k k' n Hk Hk' Hd Hl. apply nth_error_ext. intros i. rewrite !ne_sub by lia.
  destruct (Nat.ltb_spec i n); [|reflexivity].
  rewrite ne_upd by lia.
  replace ((Z.to_nat k <=? Z.to_nat k' + i) && (Z.to_nat k' + i <? Z.to_nat k + length v))%nat with false;
    [reflexivity|].
  symmetry. apply andb_false_iff. destruct Hd; [left; apply Nat.leb_gt | right; apply Nat.ltb_ge]; lia.
Qed.

Lemma sub_upd_d : forall (bs v : list byte) k d n, 0 <= k -> 0 <= d -> d + Z.of_nat n <= Z.of_nat (length v) ->
  k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  sub (upd bs k v) (k + d) n = sub v d n.
Proof.
  intros bs v k d n Hk Hd Hn Hl. apply nth_error_ext. intros i. rewrite !ne_sub by lia.
  destruct (Nat.ltb_spec i n); [|reflexivity].
  rewrite ne_upd by lia.
  replace ((Z.to_nat k <=? Z.to_nat (k + d) + i) && (Z.to_nat (k + d) + i <? Z.to_nat k + length v))%nat with true.
  - f_equal. lia.
  - symmetry. apply andb_true_iff. split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia.
Qed.

Lemma sub_all : forall (v : list byte) n, length v = n -> sub v 0 n = v.
Proof. intros v n H. unfold sub. cbn [Z.to_nat skipn]. apply firstn_all2. lia. Qed.

Lemma sub_upd_eq : forall (bs v : list byte) k n, 0 <= k -> length v = n ->
  k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  sub (upd bs k v) k n = v.
Proof.
  intros bs v k n Hk Hn Hl. rewrite <- (Z.add_0_r k) at 2. rewrite sub_upd_d by lia. apply sub_all. exact Hn.
Qed.

Lemma sub_ite_out : forall (c : bool) (bs v : list byte) k k' n, 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= k') -> k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  sub (if c then upd bs k v else bs) k' n = sub bs k' n.
Proof. intros [|] bs v k k' n Hk Hk' Hd Hl; [apply sub_upd_out; assumption | reflexivity]. Qed.

Lemma sub_ite_eq : forall (c : bool) (bs v : list byte) k n, 0 <= k -> length v = n ->
  k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  sub (if c then upd bs k v else bs) k n = if c then v else sub bs k n.
Proof. intros [|] bs v k n Hk Hn Hl; [apply sub_upd_eq; assumption | reflexivity]. Qed.

Lemma len_ite3 : forall (c : bool) (bs v1 v2 v3 : list byte) k1 k2 k3, 0 <= k1 -> k2 = k1 + 1 -> k3 = k1 + 2 ->
  length v1 = 1%nat -> length v2 = 1%nat -> length v3 = 1%nat -> k1 + 3 <= Z.of_nat (length bs) ->
  length (if c then upd (upd (upd bs k1 v1) k2 v2) k3 v3 else bs) = length bs.
Proof.
  intros [|] bs v1 v2 v3 k1 k2 k3 Hk E2 E3 L1 L2 L3 Hl; [|reflexivity].
  assert (A1 : length (upd bs k1 v1) = length bs) by (apply length_upd; lia).
  assert (A2 : length (upd (upd bs k1 v1) k2 v2) = length bs) by (rewrite length_upd; lia).
  rewrite length_upd; lia.
Qed.

Lemma sub_ite3_out : forall (c : bool) (bs v1 v2 v3 : list byte) k1 k2 k3 k' n, 0 <= k1 -> k2 = k1 + 1 -> k3 = k1 + 2 ->
  length v1 = 1%nat -> length v2 = 1%nat -> length v3 = 1%nat -> k1 + 3 <= Z.of_nat (length bs) -> 0 <= k' ->
  (k' + Z.of_nat n <= k1 \/ k1 + 3 <= k') ->
  sub (if c then upd (upd (upd bs k1 v1) k2 v2) k3 v3 else bs) k' n = sub bs k' n.
Proof.
  intros [|] bs v1 v2 v3 k1 k2 k3 k' n Hk E2 E3 L1 L2 L3 Hl Hk' Hd; [|reflexivity].
  assert (A1 : length (upd bs k1 v1) = length bs) by (apply length_upd; lia).
  assert (A2 : length (upd (upd bs k1 v1) k2 v2) = length bs) by (rewrite length_upd; lia).
  rewrite sub_upd_out by lia. rewrite sub_upd_out by lia. rewrite sub_upd_out by lia. reflexivity.
Qed.

Lemma sub_ite3_1 : forall (c : bool) (bs v1 v2 v3 : list byte) k1 k2 k3, 0 <= k1 -> k2 = k1 + 1 -> k3 = k1 + 2 ->
  length v1 = 1%nat -> length v2 = 1%nat -> length v3 = 1%nat -> k1 + 3 <= Z.of_nat (length bs) ->
  sub (if c then upd (upd (upd bs k1 v1) k2 v2) k3 v3 else bs) k1 1 = if c then v1 else sub bs k1 1.
Proof.
  intros [|] bs v1 v2 v3 k1 k2 k3 Hk E2 E3 L1 L2 L3 Hl; [|reflexivity].
  assert (A1 : length (upd bs k1 v1) = length bs) by (apply length_upd; lia).
  assert (A2 : length (upd (upd bs k1 v1) k2 v2) = length bs) by (rewrite length_upd; lia).
  rewrite sub_upd_out by lia. rewrite sub_upd_out by lia. apply sub_upd_eq; lia.
Qed.

Lemma sub_ite3_2 : forall (c : bool) (bs v1 v2 v3 : list byte) k1 k2 k3, 0 <= k1 -> k2 = k1 + 1 -> k3 = k1 + 2 ->
  length v1 = 1%nat -> length v2 = 1%nat -> length v3 = 1%nat -> k1 + 3 <= Z.of_nat (length bs) ->
  sub (if c then upd (upd (upd bs k1 v1) k2 v2) k3 v3 else bs) k2 1 = if c then v2 else sub bs k2 1.
Proof.
  intros [|] bs v1 v2 v3 k1 k2 k3 Hk E2 E3 L1 L2 L3 Hl; [|reflexivity].
  assert (A1 : length (upd bs k1 v1) = length bs) by (apply length_upd; lia).
  assert (A2 : length (upd (upd bs k1 v1) k2 v2) = length bs) by (rewrite length_upd; lia).
  rewrite sub_upd_out by lia. apply sub_upd_eq; lia.
Qed.

Lemma sub_ite3_3 : forall (c : bool) (bs v1 v2 v3 : list byte) k1 k2 k3, 0 <= k1 -> k2 = k1 + 1 -> k3 = k1 + 2 ->
  length v1 = 1%nat -> length v2 = 1%nat -> length v3 = 1%nat -> k1 + 3 <= Z.of_nat (length bs) ->
  sub (if c then upd (upd (upd bs k1 v1) k2 v2) k3 v3 else bs) k3 1 = if c then v3 else sub bs k3 1.
Proof.
  intros [|] bs v1 v2 v3 k1 k2 k3 Hk E2 E3 L1 L2 L3 Hl; [|reflexivity].
  assert (A1 : length (upd bs k1 v1) = length bs) by (apply length_upd; lia).
  assert (A2 : length (upd (upd bs k1 v1) k2 v2) = length bs) by (rewrite length_upd; lia).
  apply sub_upd_eq; lia.
Qed.

(* ---- copied from disco Prog/disco_table.v:123-128 and Prog/reac_hunt_step.v:59-66 ---- *)

Lemma s32_range : forall bs k, -2^31 <= s32_at bs k < 2^31.
Proof.
  intros bs k. unfold s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31).
  change (bv_modulus 32) with (2^32).
  pose proof (Z.mod_pos_bound (u_at bs k 4 + 2^31) (2^32) ltac:(lia)). lia.
Qed.

Lemma sub_sub : forall (bs : list byte) a n b k, 0 <= a -> 0 <= b -> b + Z.of_nat k <= Z.of_nat n ->
  sub (sub bs a n) b k = sub bs (a + b) k.
Proof.
  intros bs a n b k Ha Hb Hk. unfold sub.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Z.to_nat (a + b)) with (Z.to_nat b + Z.to_nat a)%nat by lia.
  f_equal. lia.
Qed.

(* ---- new: lengths and ranges ---- *)

Lemma length_put : forall n v, length (put n v) = n.
Proof. intros. apply length_Z_to_le_bytes. Qed.

Lemma length_sub_le : forall bs k n, (length (sub bs k n) <= n)%nat.
Proof. intros. unfold sub. rewrite firstn_length. lia. Qed.

Lemma ble_small : forall bs n, (length bs <= n)%nat -> 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat n).
Proof.
  intros bs n Hn. pose proof (ble_range bs) as R. split; [lia|].
  eapply Z.lt_le_trans; [apply (proj2 R)|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma u_at_range : forall bs k n, 0 <= u_at bs k n < 2 ^ (8 * Z.of_nat n).
Proof. intros. unfold u_at. apply ble_small, length_sub_le. Qed.

Lemma length_upd_put : forall (bs : list byte) k n v, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  length (upd bs k (put n v)) = length bs.
Proof. intros. apply length_upd; [lia|]. rewrite length_put. lia. Qed.

(* ---- new: reads of an updated world ---- *)

Lemma bytes_le_to_Z_put : forall n v, bytes_le_to_Z (put n v) = v mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros n v. unfold put.
  assert (P : 0 < 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound v _ P) as R.
  rewrite <- (Z_to_le_bytes_mod n v (8 * Z.of_nat n)) by lia.
  rewrite bytes_le_to_Z_to_le_bytes by lia.
  apply Z.mod_mod. lia.
Qed.

Lemma u_at_put : forall n v, u_at (put n v) 0 n = v mod 2 ^ (8 * Z.of_nat n).
Proof. intros. unfold u_at. rewrite sub_all by apply length_put. apply bytes_le_to_Z_put. Qed.

Lemma u_at_upd_same : forall (bs v : list byte) k, 0 <= k -> k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  u_at (upd bs k v) k (length v) = bytes_le_to_Z v.
Proof. intros. unfold u_at. rewrite sub_upd_eq by (reflexivity || lia). reflexivity. Qed.

Lemma u_at_upd_put : forall (bs : list byte) k n v, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  u_at (upd bs k (put n v)) k n = v mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros bs k n v Hk Hl. unfold u_at.
  assert (L : length (put n v) = n) by apply length_put.
  rewrite (sub_upd_eq bs (put n v) k n Hk L) by (rewrite L; lia).
  apply bytes_le_to_Z_put.
Qed.

Lemma s32_at_upd_put : forall (bs : list byte) k v, 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  s32_at (upd bs k (put 4 v)) k = bv_swrap 32 v.
Proof.
  intros bs k v Hk Hl. unfold s32_at. rewrite u_at_upd_put by (cbn; lia).
  unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ (8 * Z.of_nat 4)).
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma u_at_upd_out : forall (bs v : list byte) k k' n, 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat n <= k \/ k + Z.of_nat (length v) <= k') -> k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  u_at (upd bs k v) k' n = u_at bs k' n.
Proof. intros. unfold u_at. rewrite sub_upd_out by assumption. reflexivity. Qed.

Lemma s32_at_upd_out : forall (bs v : list byte) k k', 0 <= k -> 0 <= k' ->
  (k' + 4 <= k \/ k + Z.of_nat (length v) <= k') -> k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  s32_at (upd bs k v) k' = s32_at bs k'.
Proof. intros. unfold s32_at. rewrite u_at_upd_out by (cbn; lia). reflexivity. Qed.

(* Writing back what is there changes nothing (memcpy of a piece onto itself, a store of the loaded value). *)
Lemma upd_sub_id : forall (bs : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length bs) ->
  upd bs k (sub bs k n) = bs.
Proof.
  intros bs k n Hk Hl. rewrite upd_upd_bytes. unfold upd_bytes.
  rewrite (length_sub bs k n Hk Hl). unfold sub. apply CB3_bytes. lia.
Qed.

(* A second write of the same span overwrites the first. *)
Lemma upd_upd_same : forall (bs v w : list byte) k, 0 <= k -> length v = length w ->
  k + Z.of_nat (length v) <= Z.of_nat (length bs) ->
  upd (upd bs k v) k w = upd bs k w.
Proof.
  intros bs v w k Hk Hvw Hl. apply nth_error_ext. intros i.
  assert (L1 : length (upd bs k v) = length bs) by (apply length_upd; lia).
  rewrite ne_upd by lia. rewrite (ne_upd bs w k i) by lia. rewrite ne_upd by lia.
  rewrite Hvw. destruct ((Z.to_nat k <=? i) && (i <? Z.to_nat k + length w))%nat; reflexivity.
Qed.

(* Writes to disjoint spans commute. *)
Lemma upd_upd_comm : forall (bs v w : list byte) k k', 0 <= k -> 0 <= k' ->
  (k' + Z.of_nat (length w) <= k \/ k + Z.of_nat (length v) <= k') ->
  k + Z.of_nat (length v) <= Z.of_nat (length bs) -> k' + Z.of_nat (length w) <= Z.of_nat (length bs) ->
  upd (upd bs k v) k' w = upd (upd bs k' w) k v.
Proof.
  intros bs v w k k' Hk Hk' Hd Hl Hl'. apply nth_error_ext. intros i.
  assert (L1 : length (upd bs k v) = length bs) by (apply length_upd; lia).
  assert (L2 : length (upd bs k' w) = length bs) by (apply length_upd; lia).
  rewrite (ne_upd (upd bs k v)) by lia. rewrite (ne_upd (upd bs k' w)) by lia.
  rewrite (ne_upd bs v) by lia. rewrite (ne_upd bs w) by lia.
  destruct (Nat.leb_spec (Z.to_nat k') i); destruct (Nat.ltb_spec i (Z.to_nat k' + length w));
  destruct (Nat.leb_spec (Z.to_nat k) i); destruct (Nat.ltb_spec i (Z.to_nat k + length v));
  cbn [andb]; try reflexivity; exfalso; lia.
Qed.

(* ---- new: put and the machine's little-endian store bytes (Lib/Mem.v:389-392) ---- *)

Lemma put_le8 : forall w : word, put 8 (bv_unsigned w) = le8 w.
Proof. reflexivity. Qed.
Lemma put_le4 : forall w : word, put 4 (bv_unsigned w) = le4 w.
Proof. reflexivity. Qed.
Lemma put_le2 : forall w : word, put 2 (bv_unsigned w) = le2 w.
Proof. reflexivity. Qed.
Lemma put_le1 : forall w : word, put 1 (bv_unsigned w) = le1 w.
Proof. reflexivity. Qed.

Lemma put_mod64 : forall n v, (n <= 8)%nat -> put n (v mod 2 ^ 64) = put n v.
Proof. intros n v Hn. unfold put. apply Z_to_le_bytes_mod. lia. Qed.

(* A register holding [Z_to_bv 64 v] stores the model's [put n v]. *)
Lemma le8_put : forall v, le8 (Z_to_bv 64 v) = put 8 v.
Proof. intros. rewrite <- put_le8, Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2 ^ 64). apply put_mod64. lia. Qed.
Lemma le4_put : forall v, le4 (Z_to_bv 64 v) = put 4 v.
Proof. intros. rewrite <- put_le4, Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2 ^ 64). apply put_mod64. lia. Qed.
Lemma le2_put : forall v, le2 (Z_to_bv 64 v) = put 2 v.
Proof. intros. rewrite <- put_le2, Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2 ^ 64). apply put_mod64. lia. Qed.
Lemma le1_put : forall v, le1 (Z_to_bv 64 v) = put 1 v.
Proof. intros. rewrite <- put_le1, Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2 ^ 64). apply put_mod64. lia. Qed.
