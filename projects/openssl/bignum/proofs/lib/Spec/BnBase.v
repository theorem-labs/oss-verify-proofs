(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BW : Z := 18446744073709551616.
Definition HW : Z := 4294967296.

Arguments BW : simpl never.
Arguments HW : simpl never.

Lemma BW_pow : BW = 2 ^ 64. Proof. reflexivity. Qed.
Lemma HW_pow : HW = 2 ^ 32. Proof. reflexivity. Qed.
Lemma BW_HW : BW = HW * HW. Proof. reflexivity. Qed.
Lemma BW_pos : 0 < BW. Proof. reflexivity. Qed.
Lemma HW_pos : 0 < HW. Proof. reflexivity. Qed.

Definition Bp (n : nat) : Z := BW ^ Z.of_nat n.

Lemma Bp_0 : Bp 0 = 1. Proof. reflexivity. Qed.
Lemma Bp_S : forall n, Bp (S n) = BW * Bp n.
Proof. intros n. unfold Bp. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. Qed.
Lemma Bp_1 : Bp 1 = BW. Proof. reflexivity. Qed.
Lemma Bp_pos : forall n, 0 < Bp n.
Proof. intros n. unfold Bp. apply Z.pow_pos_nonneg; [reflexivity|lia]. Qed.
Lemma Bp_add : forall n m, Bp (n + m) = Bp n * Bp m.
Proof. intros n m. unfold Bp. rewrite Nat2Z.inj_add, Z.pow_add_r by lia. reflexivity. Qed.
Lemma Bp_ge1 : forall n, 1 <= Bp n.
Proof. intros n. pose proof (Bp_pos n). lia. Qed.
Lemma Bp_mono : forall n m, (n <= m)%nat -> Bp n <= Bp m.
Proof.
  intros n m H. replace m with (n + (m - n))%nat by lia. rewrite Bp_add.
  pose proof (Bp_pos n). pose proof (Bp_ge1 (m - n)). nia.
Qed.

Definition limb (x : Z) : Prop := 0 <= x < BW.
Definition hlimb (x : Z) : Prop := 0 <= x < HW.

Definition addw (a b : Z) : Z := (a + b) mod BW.
Definition subw (a b : Z) : Z := (a - b) mod BW.
Definition mulw (a b : Z) : Z := (a * b) mod BW.
Definition negw (a : Z) : Z := (0 - a) mod BW.
Definition shlw (a : Z) (k : Z) : Z := (a * 2 ^ k) mod BW.
Definition shrw (a : Z) (k : Z) : Z := a / 2 ^ k.
Definition ltw (a b : Z) : Z := if a <? b then 1 else 0.
Definition LBITS (a : Z) : Z := a mod HW.
Definition HBITS (a : Z) : Z := (a / HW) mod HW.
Definition L2HBITS (a : Z) : Z := (a * HW) mod BW.

Lemma limb_mod : forall x, limb (x mod BW).
Proof. intros x. unfold limb. apply Z.mod_pos_bound. exact BW_pos. Qed.
Lemma addw_limb : forall a b, limb (addw a b). Proof. intros; apply limb_mod. Qed.
Lemma subw_limb : forall a b, limb (subw a b). Proof. intros; apply limb_mod. Qed.
Lemma mulw_limb : forall a b, limb (mulw a b). Proof. intros; apply limb_mod. Qed.
Lemma negw_limb : forall a, limb (negw a). Proof. intros; apply limb_mod. Qed.
Lemma shlw_limb : forall a k, limb (shlw a k). Proof. intros; apply limb_mod. Qed.
Lemma limb_0 : limb 0. Proof. unfold limb, BW. lia. Qed.
Lemma limb_1 : limb 1. Proof. unfold limb, BW. lia. Qed.

Fixpoint lval (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: l' => x + BW * lval l'
  end.

Definition limbs (l : list Z) : Prop := Forall limb l.

Lemma limbs_nil : limbs []. Proof. constructor. Qed.
Lemma limbs_cons : forall x l, limb x -> limbs l -> limbs (x :: l).
Proof. intros. constructor; assumption. Qed.
Lemma limbs_cons_inv : forall x l, limbs (x :: l) -> limb x /\ limbs l.
Proof. intros x l H. inversion H; subst. split; assumption. Qed.
Lemma limbs_app : forall a b, limbs a -> limbs b -> limbs (a ++ b).
Proof. intros a b Ha Hb. apply Forall_app. split; assumption. Qed.
Lemma limbs_app_inv : forall a b, limbs (a ++ b) -> limbs a /\ limbs b.
Proof. intros a b H. apply Forall_app in H. exact H. Qed.
Lemma limbs_firstn : forall n l, limbs l -> limbs (firstn n l).
Proof.
  intros n l H. rewrite <- (firstn_skipn n l) in H. apply limbs_app_inv in H. apply H.
Qed.
Lemma limbs_skipn : forall n l, limbs l -> limbs (skipn n l).
Proof.
  intros n l H. rewrite <- (firstn_skipn n l) in H. apply limbs_app_inv in H. apply H.
Qed.
Lemma limbs_repeat : forall x n, limb x -> limbs (repeat x n).
Proof. intros x n H. unfold limbs. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. subst. exact H. Qed.
Lemma limbs_nth : forall l i, limbs l -> limb (nth i l 0).
Proof.
  intros l i H. destruct (Nat.lt_ge_cases i (length l)) as [Hi|Hi].
  - unfold limbs in H. rewrite Forall_forall in H. apply H. apply nth_In. exact Hi.
  - rewrite nth_overflow by exact Hi. exact limb_0.
Qed.

Lemma lval_app : forall a b, lval (a ++ b) = lval a + Bp (length a) * lval b.
Proof.
  induction a as [|x a IH]; intros b; cbn [lval app length].
  - rewrite Bp_0. lia.
  - rewrite IH, Bp_S. ring.
Qed.

Lemma lval_nonneg : forall l, limbs l -> 0 <= lval l.
Proof.
  induction l as [|x l IH]; intros H; cbn [lval]; [lia|].
  apply limbs_cons_inv in H. destruct H as [[Hx _] Hl]. specialize (IH Hl).
  pose proof BW_pos. nia.
Qed.

Lemma lval_bound : forall l, limbs l -> 0 <= lval l < Bp (length l).
Proof.
  induction l as [|x l IH]; intros H; cbn [lval length].
  - rewrite Bp_0. lia.
  - apply limbs_cons_inv in H. destruct H as [[Hx0 Hx1] Hl]. specialize (IH Hl).
    rewrite Bp_S. pose proof BW_pos. nia.
Qed.

Lemma lval_repeat0 : forall n, lval (repeat 0 n) = 0.
Proof. induction n as [|n IH]; cbn [repeat lval]; [reflexivity|]. rewrite IH. lia. Qed.

Lemma lval_single : forall x, lval [x] = x.
Proof. intros x. cbn [lval]. lia. Qed.

Lemma lval_split : forall n l, lval l = lval (firstn n l) + Bp (length (firstn n l)) * lval (skipn n l).
Proof. intros n l. rewrite <- lval_app, firstn_skipn. reflexivity. Qed.

Lemma lval_split_le : forall n l, (n <= length l)%nat ->
  lval l = lval (firstn n l) + Bp n * lval (skipn n l).
Proof. intros n l H. rewrite (lval_split n l) at 1. rewrite firstn_length_le by exact H. reflexivity. Qed.

Lemma lval_inj : forall a b, limbs a -> limbs b -> length a = length b -> lval a = lval b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] Ha Hb Hlen Hv; cbn [length] in Hlen; try discriminate; [reflexivity|].
  apply limbs_cons_inv in Ha. destruct Ha as [Hx Ha].
  apply limbs_cons_inv in Hb. destruct Hb as [Hy Hb].
  cbn [lval] in Hv. unfold limb in *.
  assert (x = y).
  { assert (E : x mod BW = y mod BW).
    { replace x with ((x + BW * lval a) - lval a * BW) by ring. rewrite Hv.
      replace (y + BW * lval b - lval a * BW) with (y + (lval b - lval a) * BW) by ring.
      rewrite Z.mod_add by (unfold BW; lia). reflexivity. }
    rewrite !Z.mod_small in E by lia. exact E. }
  subst y. f_equal. apply IH; try assumption; [lia|]. pose proof BW_pos. nia.
Qed.

Fixpoint to_limbs (n : nat) (v : Z) : list Z :=
  match n with
  | O => []
  | S n' => v mod BW :: to_limbs n' (v / BW)
  end.

Lemma to_limbs_length : forall n v, length (to_limbs n v) = n.
Proof. induction n as [|n IH]; intros v; cbn [to_limbs length]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma to_limbs_limbs : forall n v, limbs (to_limbs n v).
Proof. induction n as [|n IH]; intros v; cbn [to_limbs]; [constructor|]. constructor; [apply limb_mod|apply IH]. Qed.

Lemma lval_to_limbs : forall n v, lval (to_limbs n v) = v mod Bp n.
Proof.
  induction n as [|n IH]; intros v; cbn [to_limbs lval].
  - rewrite Bp_0, Z.mod_1_r. reflexivity.
  - rewrite IH, Bp_S. pose proof BW_pos. pose proof (Bp_pos n).
    rewrite Z.rem_mul_r by lia. ring.
Qed.

Lemma lval_to_limbs_small : forall n v, 0 <= v < Bp n -> lval (to_limbs n v) = v.
Proof. intros n v H. rewrite lval_to_limbs. apply Z.mod_small. exact H. Qed.

Lemma to_limbs_lval : forall l, limbs l -> to_limbs (length l) (lval l) = l.
Proof.
  intros l H. apply lval_inj; [apply to_limbs_limbs|exact H|apply to_limbs_length|].
  rewrite lval_to_limbs_small; [reflexivity|]. apply lval_bound. exact H.
Qed.

Lemma to_limbs_unique : forall l v, limbs l -> lval l = v -> to_limbs (length l) v = l.
Proof. intros l v H E. subst v. apply to_limbs_lval. exact H. Qed.

Definition slice (l : list Z) (off n : nat) : list Z := firstn n (skipn off l).
Definition splice (l : list Z) (off : nat) (seg : list Z) : list Z :=
  firstn off l ++ seg ++ skipn (off + length seg) l.

Definition upd (l : list Z) (i : nat) (v : Z) : list Z := splice l i [v].

Lemma slice_length : forall l off n, (off + n <= length l)%nat -> length (slice l off n) = n.
Proof. intros l off n H. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

Lemma slice_limbs : forall l off n, limbs l -> limbs (slice l off n).
Proof. intros. unfold slice. apply limbs_firstn, limbs_skipn. assumption. Qed.

Lemma splice_length : forall l off seg, (off + length seg <= length l)%nat ->
  length (splice l off seg) = length l.
Proof.
  intros l off seg H. unfold splice. rewrite !length_app, length_firstn, length_skipn. lia.
Qed.

Lemma splice_limbs : forall l off seg, limbs l -> limbs seg -> limbs (splice l off seg).
Proof.
  intros. unfold splice. apply limbs_app; [apply limbs_firstn; assumption|].
  apply limbs_app; [assumption|apply limbs_skipn; assumption].
Qed.

Lemma upd_length : forall l i v, (i < length l)%nat -> length (upd l i v) = length l.
Proof. intros. unfold upd. apply splice_length. cbn [length]. lia. Qed.

Lemma upd_limbs : forall l i v, limbs l -> limb v -> limbs (upd l i v).
Proof. intros. unfold upd. apply splice_limbs; [assumption|]. constructor; [assumption|constructor]. Qed.

Lemma slice_splice_same : forall l off seg, (off + length seg <= length l)%nat ->
  slice (splice l off seg) off (length seg) = seg.
Proof.
  intros l off seg H. unfold slice, splice.
  rewrite skipn_app, length_firstn, Nat.min_l by lia.
  rewrite skipn_all2 by (rewrite length_firstn; lia).
  replace (off - off)%nat with 0%nat by lia. cbn [skipn app].
  rewrite firstn_app, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
  apply firstn_all2. lia.
Qed.

Lemma firstn_splice_below : forall l off seg n, (n <= off)%nat -> (off <= length l)%nat ->
  firstn n (splice l off seg) = firstn n l.
Proof.
  intros l off seg n Hn Hoff. unfold splice. rewrite firstn_app, length_firstn, Nat.min_l by lia.
  replace (n - off)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
  rewrite firstn_firstn, Nat.min_l by lia. reflexivity.
Qed.

Lemma skipn_splice_above : forall l off seg n, (off + length seg <= n)%nat -> (off + length seg <= length l)%nat ->
  skipn n (splice l off seg) = skipn n l.
Proof.
  intros l off seg n Hn Hl. unfold splice.
  rewrite skipn_app, length_firstn, Nat.min_l by lia.
  rewrite skipn_all2 by (rewrite length_firstn; lia). cbn [app].
  rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
  rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma slice_splice_below : forall l off seg o n, (o + n <= off)%nat -> (off <= length l)%nat ->
  slice (splice l off seg) o n = slice l o n.
Proof.
  intros l off seg o n H Hoff. unfold slice. rewrite !firstn_skipn_comm.
  rewrite firstn_splice_below by lia. reflexivity.
Qed.

Lemma slice_splice_above : forall l off seg o n, (off + length seg <= o)%nat -> (off + length seg <= length l)%nat ->
  slice (splice l off seg) o n = slice l o n.
Proof. intros l off seg o n H Hl. unfold slice. rewrite skipn_splice_above by lia. reflexivity. Qed.

Lemma slice_0 : forall l n, slice l 0 n = firstn n l.
Proof. reflexivity. Qed.

Lemma slice_full : forall l, slice l 0 (length l) = l.
Proof. intros l. unfold slice. cbn [skipn]. apply firstn_all. Qed.

Lemma firstn_add : forall (l : list Z) n m, firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  induction l as [|x l IH]; intros n m.
  - rewrite !firstn_nil, skipn_nil, firstn_nil. reflexivity.
  - destruct n as [|n]; cbn [firstn skipn Nat.add app]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma slice_app_slice : forall l off n m, slice l off n ++ slice l (off + n) m = slice l off (n + m).
Proof.
  intros l off n m. unfold slice. rewrite firstn_add, skipn_skipn.
  replace (n + off)%nat with (off + n)%nat by lia. reflexivity.
Qed.

Lemma nth_slice : forall l off n i, (i < n)%nat -> nth i (slice l off n) 0 = nth (off + i) l 0.
Proof.
  intros l off n i H. unfold slice. rewrite nth_firstn.
  destruct (Nat.ltb_spec i n); [|lia]. rewrite nth_skipn. reflexivity.
Qed.

Lemma nth_splice_same : forall l off seg i, (off <= length l)%nat -> (i < length seg)%nat ->
  nth (off + i) (splice l off seg) 0 = nth i seg 0.
Proof.
  intros l off seg i Hoff Hi. unfold splice.
  rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn, Nat.min_l by lia.
  replace (off + i - off)%nat with i by lia. rewrite app_nth1 by lia. reflexivity.
Qed.

Lemma nth_splice_other : forall l off seg i, (off + length seg <= length l)%nat ->
  (i < off \/ off + length seg <= i)%nat -> nth i (splice l off seg) 0 = nth i l 0.
Proof.
  intros l off seg i Hl Hi. unfold splice. destruct Hi as [Hi|Hi].
  - rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
    destruct (Nat.ltb_spec i off); [reflexivity|lia].
  - rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn, Nat.min_l by lia.
    rewrite app_nth2 by lia. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma nth_upd_same : forall l i v, (i < length l)%nat -> nth i (upd l i v) 0 = v.
Proof.
  intros l i v H. unfold upd. replace i with (i + 0)%nat at 1 by lia.
  rewrite nth_splice_same; [reflexivity|lia|cbn; lia].
Qed.

Lemma nth_upd_other : forall l i j v, (i < length l)%nat -> i <> j -> nth j (upd l i v) 0 = nth j l 0.
Proof. intros l i j v H Hij. unfold upd. apply nth_splice_other; cbn [length]; lia. Qed.

Lemma lval_splice : forall l off seg, (off + length seg <= length l)%nat ->
  lval (splice l off seg) = lval l + Bp off * (lval seg - lval (slice l off (length seg))).
Proof.
  intros l off seg H. unfold splice, slice.
  rewrite (lval_split_le off l) by lia.
  rewrite (lval_split_le (length seg) (skipn off l)) by (rewrite length_skipn; lia).
  rewrite !lval_app, length_firstn, Nat.min_l by lia. rewrite skipn_skipn.
  replace (length seg + off)%nat with (off + length seg)%nat by lia. ring.
Qed.

Lemma nth_splice : forall l off seg i, (off + length seg <= length l)%nat ->
  nth i (splice l off seg) 0 = if ((off <=? i) && (i <? off + length seg))%nat then nth (i - off) seg 0 else nth i l 0.
Proof.
  intros l off seg i H. destruct (Nat.leb_spec off i) as [H1|H1]; cbn [andb].
  - destruct (Nat.ltb_spec i (off + length seg)) as [H2|H2].
    + replace i with (off + (i - off))%nat at 1 by lia. apply nth_splice_same; lia.
    + apply nth_splice_other; lia.
  - apply nth_splice_other; lia.
Qed.

Lemma list_eq_nth : forall (a b : list Z), length a = length b ->
  (forall i, (i < length a)%nat -> nth i a 0 = nth i b 0) -> a = b.
Proof. intros a b Hl H. apply (nth_ext a b 0 0 Hl). exact H. Qed.

Lemma splice_splice_same : forall l off s1 s2, (off + length s1 <= length l)%nat -> (length s2 <= length s1)%nat ->
  splice (splice l off s1) off s2 = splice l off (s2 ++ skipn (length s2) s1).
Proof.
  intros l off s1 s2 H1 H2.
  assert (Hlen : length (s2 ++ skipn (length s2) s1) = length s1) by (rewrite length_app, length_skipn; lia).
  apply list_eq_nth.
  - rewrite !splice_length; try lia. rewrite splice_length; lia.
  - intros i Hi. rewrite !nth_splice; try lia; [|rewrite splice_length; lia].
    rewrite Hlen.
    destruct (Nat.leb_spec off i) as [Ha|Ha]; cbn [andb]; [|reflexivity].
    destruct (Nat.ltb_spec i (off + length s2)) as [Hb|Hb].
    + destruct (Nat.ltb_spec i (off + length s1)); [|lia]. rewrite app_nth1 by lia. reflexivity.
    + destruct (Nat.ltb_spec i (off + length s1)) as [Hc|Hc]; [|reflexivity].
      rewrite app_nth2 by lia. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma upd_splice : forall l off s k x, (off + length s <= length l)%nat -> (k < length s)%nat ->
  upd (splice l off s) (off + k) x = splice l off (upd s k x).
Proof.
  intros l off s k x H1 H2. unfold upd at 1.
  assert (Hlu : length (upd s k x) = length s) by (apply upd_length; lia).
  apply list_eq_nth.
  - rewrite !splice_length; cbn [length]; try lia. rewrite splice_length; lia.
  - intros i Hi. rewrite !nth_splice; cbn [length]; try lia; [|rewrite splice_length; lia].
    rewrite Hlu.
    destruct (Nat.leb_spec (off + k) i) as [Ha|Ha]; cbn [andb].
    + destruct (Nat.ltb_spec i (off + k + 1)) as [Hb|Hb].
      * assert (i = off + k)%nat by lia. subst i. replace (off + k - (off + k))%nat with 0%nat by lia.
        destruct (Nat.leb_spec off (off + k)); [|lia]. destruct (Nat.ltb_spec (off + k) (off + length s)); [|lia].
        cbn [andb nth]. replace (off + k - off)%nat with k by lia. symmetry. apply nth_upd_same. lia.
      * destruct (Nat.leb_spec off i); [|lia]. cbn [andb].
        destruct (Nat.ltb_spec i (off + length s)); [|reflexivity].
        rewrite nth_upd_other by lia. reflexivity.
    + destruct (Nat.leb_spec off i) as [Hc|Hc]; cbn [andb]; [|reflexivity].
      destruct (Nat.ltb_spec i (off + length s)); [|reflexivity].
      rewrite nth_upd_other by lia. reflexivity.
Qed.

Lemma firstn_slice : forall l off n m, (m <= n)%nat -> firstn m (slice l off n) = slice l off m.
Proof. intros l off n m H. unfold slice. rewrite firstn_firstn, Nat.min_l by lia. reflexivity. Qed.

Lemma splice_slice_id : forall l off n, (off + n <= length l)%nat -> splice l off (slice l off n) = l.
Proof.
  intros l off n H. apply list_eq_nth.
  - apply splice_length. rewrite slice_length; lia.
  - intros i Hi. rewrite nth_splice by (rewrite slice_length; lia). rewrite slice_length by lia.
    destruct (Nat.leb_spec off i) as [Ha|Ha]; cbn [andb]; [|reflexivity].
    destruct (Nat.ltb_spec i (off + n)) as [Hb|Hb]; [|reflexivity].
    rewrite nth_slice by lia. f_equal. lia.
Qed.

Lemma nth_limb_val : forall l i, limbs l -> (i < length l)%nat ->
  lval l = lval (firstn i l) + Bp i * nth i l 0 + Bp (S i) * lval (skipn (S i) l).
Proof.
  intros l i Hl Hi. rewrite (lval_split_le i l) by lia.
  assert (E : skipn i l = nth i l 0 :: skipn (S i) l).
  { clear Hl. revert i Hi. induction l as [|x l IH]; intros i Hi; cbn [length] in Hi; [lia|].
    destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. lia. }
  rewrite E. cbn [lval]. rewrite Bp_S. ring.
Qed.

Lemma slice_splice_eq : forall l off seg m, length seg = m -> (off + m <= length l)%nat ->
  slice (splice l off seg) off m = seg.
Proof. intros l off seg m H1 H2. subst m. apply slice_splice_same. exact H2. Qed.

Lemma firstn_splice_0 : forall l seg m, length seg = m -> (m <= length l)%nat -> firstn m (splice l 0 seg) = seg.
Proof. intros l seg m H1 H2. change (firstn m (splice l 0 seg)) with (slice (splice l 0 seg) 0 m). apply slice_splice_eq; lia. Qed.
