(* reac-pw/fuzz_link, PLAIN build: byte-list facts about struct reac_served_marks (516 bytes:
   int n, then 32 names of 16 bytes) that the remember / reac_served_mark walks use. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_str.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Bytes.
Local Open Scope Z_scope.

(* ---- generic list facts ---- *)

Lemma nth_firstn_gen : forall {A} (l : list A) n i,
  nth_error (firstn n l) i = if (i <? n)%nat then nth_error l i else None.
Proof.
  intros A l. induction l as [|x l IH]; intros [|n] [|i]; cbn; try reflexivity;
    try (rewrite IH; reflexivity);
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma nth_skipn_gen : forall {A} (l : list A) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  intros A l. induction l as [|x l IH]; intros n i; destruct n as [|n]; cbn; try reflexivity.
  - destruct i; reflexivity.
  - apply IH.
Qed.

Lemma slice_nth : forall (c : list byte) off len i, 0 <= off -> 0 <= len ->
  nth_error (slice c off len) i =
    if (i <? Z.to_nat len)%nat then nth_error c (Z.to_nat off + i) else None.
Proof. intros c off len i H0 H1. unfold slice. rewrite nth_firstn_gen, nth_skipn_gen. reflexivity. Qed.

Lemma slice_length : forall (c : list byte) off len, 0 <= off -> 0 <= len -> off + len <= Z.of_nat (length c) ->
  length (slice c off len) = Z.to_nat len.
Proof.
  intros c off len H0 H1 H2. unfold slice. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma bytes_at_slice : forall m a (c : list byte) off len, bytes_at rsegs m a c -> 0 <= off -> 0 <= len ->
  off + len <= Z.of_nat (length c) -> bytes_at rsegs m (a + off) (slice c off len).
Proof.
  intros m a c off len (Ha & Hl & H) H0 H1 H2. pose proof (slice_length c off len H0 H1 H2) as LS.
  split; [lia|]. split; [rewrite LS; lia|]. intros i Hi. rewrite LS in Hi. rewrite slice_nth by lia.
  replace (i <? Z.to_nat len)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite <- H by lia. f_equal. f_equal. lia.
Qed.

Lemma bytes_at_prefix : forall m a l1 l2, bytes_at rsegs m a (l1 ++ l2) -> bytes_at rsegs m a l1.
Proof. intros m a l1 l2 H. apply bytes_at_app in H. exact (proj1 H). Qed.

Lemma bytes_at_unique : forall m a l1 l2, bytes_at rsegs m a l1 -> bytes_at rsegs m a l2 ->
  length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None l1 i) Hi), (proj2 (nth_error_None l2 i) ltac:(lia)). reflexivity.
Qed.

(* a byte list with a NUL holds its C string, then the NUL *)
Lemma cstr_split : forall l, (nul_at l < length l)%nat ->
  exists rest, l = cstr l ++ [zb 0] ++ rest /\ ~ In (zb 0) (cstr l).
Proof.
  induction l as [|b l IH]; intros H; [cbn in H; lia|].
  unfold cstr in *. cbn [nul_at firstn] in *. unfold bz in *.
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E].
  - exists l. cbn [firstn app]. rewrite (byte_zero b E). split; [reflexivity | intros []].
  - cbn [length] in H. destruct (IH ltac:(lia)) as (rest & Hl & Hn). exists rest.
    cbn [firstn app]. split; [f_equal; exact Hl|].
    intros [Hb|Hin]; [apply E; rewrite Hb; reflexivity | exact (Hn Hin)].
Qed.

Lemma cstr_app_nul : forall s rest, ~ In (zb 0) s -> cstr (s ++ [zb 0] ++ rest) = s.
Proof.
  induction s as [|b s IH]; intros rest Hn; unfold cstr in *; cbn [app nul_at firstn].
  - reflexivity.
  - assert (Hb : bz b <> 0) by (intros E; apply Hn; left; apply byte_zero; exact E).
    replace (bz b =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb). cbn [firstn].
    f_equal. apply IH. intros H; apply Hn; right; exact H.
Qed.

Lemma nul_at_app_nul : forall s rest, ~ In (zb 0) s -> nul_at (s ++ [zb 0] ++ rest) = length s.
Proof.
  induction s as [|b s IH]; intros rest Hn; cbn [app nul_at length].
  - reflexivity.
  - assert (Hb : bz b <> 0) by (intros E; apply Hn; left; apply byte_zero; exact E).
    replace (bz b =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hb).
    f_equal. apply IH. intros H; apply Hn; right; exact H.
Qed.

(* ---- the 32-bit load of `n` ---- *)

Lemma bytes4_range : forall bs : list byte, length bs = 4%nat -> 0 <= bytes_le_to_Z bs < 2 ^ 32.
Proof.
  intros bs L. rewrite bytes_le_to_Z_le_val. pose proof (le_val_range _ (bytes_ok_map bs)) as R.
  rewrite length_map, L in R. exact R.
Qed.

Lemma lw_val : forall bs : list byte, length bs = 4%nat -> bytes_le_to_Z bs < 2 ^ 31 ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word bs)) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros bs L H. pose proof (bytes4_range bs L) as R.
  rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

(* ---- the marks block ---- *)

Lemma marks_n_range : forall gbs, marks_wf gbs -> 0 <= mk_n gbs <= 32.
Proof. intros gbs [H _]. unfold MARKS_MAX in H. exact H. Qed.

Lemma mk_n_slice : forall gbs, mk_n gbs = bytes_le_to_Z (firstn 4 (skipn 0 gbs)).
Proof. reflexivity. Qed.

Lemma slot_cstr : forall m a gbs i, bytes_at rsegs m a gbs -> Z.of_nat (length gbs) = 516 -> marks_wf gbs ->
  0 <= i < mk_n gbs ->
  bytes_at rsegs m (a + (4 + 16 * i)) (cstr (slice gbs (4 + 16 * i) 16) ++ [zb 0])
  /\ ~ In (zb 0) (cstr (slice gbs (4 + 16 * i) 16)).
Proof.
  intros m a gbs i B L [R T] Hi. unfold MARKS_MAX in R.
  specialize (T i Hi). unfold MK_NAME, MARK_LEN in T.
  pose proof (bytes_at_slice m a gbs (4 + 16 * i) 16 B ltac:(lia) ltac:(lia) ltac:(lia)) as BS.
  assert (LS : length (slice gbs (4 + 16 * i) 16) = 16%nat) by (rewrite slice_length by lia; reflexivity).
  destruct (cstr_split (slice gbs (4 + 16 * i) 16) ltac:(rewrite LS; lia)) as (rest & E & N).
  rewrite E in BS. rewrite app_assoc in BS. split; [exact (bytes_at_prefix _ _ _ _ BS) | exact N].
Qed.

Lemma mk_names_nth : forall gbs i, (i < Z.to_nat (mk_n gbs))%nat ->
  nth_error (mk_names gbs) i = Some (cstr (slice gbs (4 + 16 * Z.of_nat i) 16)).
Proof.
  intros gbs i Hi. unfold mk_names. rewrite nth_error_map, nth_error_seq.
  replace (i <? Z.to_nat (mk_n gbs))%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). reflexivity.
Qed.

Lemma mk_names_length : forall gbs, length (mk_names gbs) = Z.to_nat (mk_n gbs).
Proof. intros gbs. unfold mk_names. rewrite length_map, length_seq. reflexivity. Qed.

Lemma existsb_none : forall (l : list (list byte)) x,
  (forall j, (j < length l)%nat -> nth_error l j <> Some x) -> existsb (fun y => bl_eqb y x) l = false.
Proof.
  induction l as [|y l IH]; intros x H; [reflexivity|]. cbn [existsb].
  destruct (bl_eqb y x) eqn:E.
  - exfalso. apply bl_eqb_iff in E. subst y. apply (H 0%nat); [cbn; lia | reflexivity].
  - cbn [orb]. apply IH. intros j Hj. apply (H (S j)). cbn; lia.
Qed.

Lemma existsb_some : forall (l : list (list byte)) x j, nth_error l j = Some x ->
  existsb (fun y => bl_eqb y x) l = true.
Proof.
  induction l as [|y l IH]; intros x j H; [destruct j; discriminate|]. cbn [existsb].
  destruct j as [|j]; cbn in H.
  - injection H as ->. rewrite bl_eqb_refl. reflexivity.
  - rewrite (IH x j H). apply orb_true_r.
Qed.

(* ---- the block after remember's two stores: n + 1 at [0,4), then the name at slot n ---- *)

Lemma upd_bytes_nth_gen : forall (cs bs : list byte) k i, (k + length bs <= length cs)%nat ->
  nth_error (upd_bytes cs k bs) i =
    if (Nat.leb k i && Nat.ltb i (k + length bs))%bool then nth_error bs (i - k) else nth_error cs i.
Proof.
  intros cs bs k i H. destruct (Nat.lt_ge_cases i (length cs)) as [Hi|Hi].
  - apply upd_bytes_nth; assumption.
  - rewrite (proj2 (nth_error_None _ i)) by (rewrite upd_bytes_length by assumption; lia).
    rewrite (proj2 (nth_error_None cs i)) by lia.
    destruct (Nat.leb_spec k i), (Nat.ltb_spec i (k + length bs)); cbn; try reflexivity; lia.
Qed.

Lemma slice_upd_other : forall (cs bs : list byte) k off len, 0 <= off -> 0 <= len ->
  (k + length bs <= length cs)%nat ->
  (off + len <= Z.of_nat k \/ Z.of_nat (k + length bs) <= off) ->
  slice (upd_bytes cs k bs) off len = slice cs off len.
Proof.
  intros cs bs k off len H0 H1 H2 H3. apply nth_error_ext. intros i.
  rewrite !slice_nth by lia. destruct (Nat.ltb_spec i (Z.to_nat len)); [|reflexivity].
  rewrite upd_bytes_nth_gen by exact H2.
  destruct (Nat.leb_spec k (Z.to_nat off + i)), (Nat.ltb_spec (Z.to_nat off + i) (k + length bs));
    cbn; try reflexivity; lia.
Qed.

Lemma slice_upd_same : forall (cs bs : list byte) k len, (k + length bs <= length cs)%nat ->
  (length bs <= Z.to_nat len)%nat -> 0 <= len -> (k + Z.to_nat len <= length cs)%nat ->
  slice (upd_bytes cs k bs) (Z.of_nat k) len = bs ++ slice cs (Z.of_nat (k + length bs)) (len - Z.of_nat (length bs)).
Proof.
  intros cs bs k len H1 H2 H3 H4. apply nth_error_ext. intros i.
  rewrite slice_nth by lia. rewrite upd_bytes_nth_gen by exact H1.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite nth_error_app1 by exact Hi.
    replace (i <? Z.to_nat len)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite Nat2Z.id. destruct (Nat.leb_spec k (k + i)), (Nat.ltb_spec (k + i) (k + length bs)); try lia.
    cbn [andb]. f_equal. lia.
  - rewrite nth_error_app2 by exact Hi. rewrite slice_nth by lia. rewrite Nat2Z.id.
    destruct (Nat.ltb_spec i (Z.to_nat len)) as [Hl|Hl].
    + destruct (Nat.leb_spec k (k + i)), (Nat.ltb_spec (k + i) (k + length bs)); try lia. cbn [andb].
      replace (i - length bs <? Z.to_nat (len - Z.of_nat (length bs)))%nat with true
        by (symmetry; apply Nat.ltb_lt; lia).
      f_equal. lia.
    + replace (i - length bs <? Z.to_nat (len - Z.of_nat (length bs)))%nat with false
        by (symmetry; apply Nat.ltb_ge; lia). reflexivity.
Qed.
