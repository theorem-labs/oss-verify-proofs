(** * BtWin — window sums and per-value counts over [zarr] segments.

    OWNER: an earlier development run (zlib z-repro campaign, G1 build_tree keystone).

    The combine loop ([bt_loop]) and [gen_bitlen]'s first pass both need
    bookkeeping over a CONTIGUOUS WINDOW of the heap array: "how many parked
    positions hold value x", "sum of a weight over the parked window".  PqDown.v
    (ported) deliberately avoided multisets because its consumer needed only
    membership; the Kraft census below it DOES need counts — the union-typed
    [tr_dl] array makes parked-value distinctness load-bearing (a duplicated
    parking would let a [t_setlen] destroy a dad before [gb_pass1] reads it),
    and "every created node has exactly two parked children" is a count.

    One combinator serves both: [wsum] a [Z]-valued weight over [lo .. lo+n),
    [wcount] the instance at an equality indicator.  Everything else is the
    zset/window algebra, proved once here so the walks stay linear. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Fixpoint wsum (f : Z -> Z) (lo : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S k => f lo + wsum f (lo + 1) k
  end.

Definition ind (b : bool) : Z := if b then 1 else 0.

Lemma ind_0_1 : forall b, 0 <= ind b <= 1.
Proof. intro b; destruct b; cbn [ind]; lia. Qed.

Definition wcount (a : zarr) (lo : Z) (n : nat) (x : Z) : Z :=
  wsum (fun i => ind (Z.eqb (a i) x)) lo n.

(** ** [wsum] algebra *)

Lemma wsum_ext : forall f g lo n,
  (forall i, lo <= i < lo + Z.of_nat n -> f i = g i) ->
  wsum f lo n = wsum g lo n.
Proof.
  intros f g lo n; revert lo.
  induction n as [|k IH]; intros lo H; cbn [wsum]; [reflexivity|].
  rewrite (H lo) by lia. f_equal. apply IH. intros i Hi. apply H. lia.
Qed.

Lemma wsum_split_first : forall f lo n,
  wsum f lo (S n) = f lo + wsum f (lo + 1) n.
Proof. reflexivity. Qed.

Lemma wsum_split_last : forall f lo n,
  wsum f lo (S n) = wsum f lo n + f (lo + Z.of_nat n).
Proof.
  intros f lo n; revert lo.
  induction n as [|k IH]; intro lo.
  - cbn [wsum]. replace (lo + Z.of_nat 0) with lo by lia. lia.
  - rewrite (wsum_split_first f lo (S k)), (wsum_split_first f lo k),
            (IH (lo + 1)).
    replace (lo + 1 + Z.of_nat k) with (lo + Z.of_nat (S k)) by lia. lia.
Qed.

Lemma wsum_nonneg : forall f lo n,
  (forall i, lo <= i < lo + Z.of_nat n -> 0 <= f i) ->
  0 <= wsum f lo n.
Proof.
  intros f lo n; revert lo.
  induction n as [|k IH]; intros lo H; cbn [wsum]; [lia|].
  assert (0 <= f lo) by (apply H; lia).
  assert (0 <= wsum f (lo + 1) k) by (apply IH; intros; apply H; lia).
  lia.
Qed.

Lemma wsum_le : forall f g lo n,
  (forall i, lo <= i < lo + Z.of_nat n -> f i <= g i) ->
  wsum f lo n <= wsum g lo n.
Proof.
  intros f g lo n; revert lo.
  induction n as [|k IH]; intros lo H; cbn [wsum]; [lia|].
  assert (f lo <= g lo) by (apply H; lia).
  assert (wsum f (lo + 1) k <= wsum g (lo + 1) k)
    by (apply IH; intros; apply H; lia).
  lia.
Qed.

(** The one-point delta: changing the weight at a single in-window index. *)
Lemma wsum_point_delta : forall f g lo n j,
  lo <= j < lo + Z.of_nat n ->
  (forall i, lo <= i < lo + Z.of_nat n -> i <> j -> f i = g i) ->
  wsum g lo n = wsum f lo n - f j + g j.
Proof.
  intros f g lo n; revert lo.
  induction n as [|k IH]; intros lo j Hj H; cbn [wsum]; [lia|].
  destruct (Z.eq_dec j lo) as [->|Hne].
  - assert (wsum g (lo + 1) k = wsum f (lo + 1) k); [|lia].
    apply wsum_ext. intros i Hi. symmetry. apply H; lia.
  - rewrite (IH (lo + 1) j) by (try lia; intros; apply H; lia).
    rewrite (H lo) by lia. lia.
Qed.

(** ** [wcount] algebra *)

Lemma wcount_nonneg : forall a lo n x, 0 <= wcount a lo n x.
Proof.
  intros. apply wsum_nonneg. intros i _. apply ind_0_1.
Qed.

Lemma wcount_ub : forall a lo n x, wcount a lo n x <= Z.of_nat n.
Proof.
  intros a lo n x; revert lo.
  induction n as [|k IH]; intro lo; cbn [wcount wsum]; [lia|].
  fold (wcount a (lo + 1) k x).
  pose proof (IH (lo + 1)). pose proof (ind_0_1 (Z.eqb (a lo) x)). lia.
Qed.

Lemma wcount_ext_window : forall a b lo n x,
  (forall i, lo <= i < lo + Z.of_nat n -> a i = b i) ->
  wcount a lo n x = wcount b lo n x.
Proof.
  intros a b lo n x H. apply wsum_ext. intros i Hi. rewrite H by exact Hi.
  reflexivity.
Qed.

Lemma wcount_zset_in : forall a lo n i v x,
  lo <= i < lo + Z.of_nat n ->
  wcount (zset a i v) lo n x
  = wcount a lo n x - ind (Z.eqb (a i) x) + ind (Z.eqb v x).
Proof.
  intros a lo n i v x Hi.
  unfold wcount.
  rewrite (wsum_point_delta (fun j => ind (Z.eqb (a j) x))
             (fun j => ind (Z.eqb (zset a i v j) x)) lo n i Hi).
  - rewrite zset_same. reflexivity.
  - intros j _ Hne. rewrite zset_other by exact Hne. reflexivity.
Qed.

Lemma wcount_zset_out : forall a lo n i v x,
  ~ (lo <= i < lo + Z.of_nat n) ->
  wcount (zset a i v) lo n x = wcount a lo n x.
Proof.
  intros a lo n i v x Hi. apply wcount_ext_window.
  intros j Hj. rewrite zset_other by lia. reflexivity.
Qed.

(** Growing the window one slot at the low end (the parking direction:
    [b_hmax] decreases, the parked window [hmax .. HEAP_SIZE) gains its new
    low slot). *)
Lemma wcount_grow_low : forall a lo n x,
  wcount a (lo - 1) (S n) x = ind (Z.eqb (a (lo - 1)) x) + wcount a lo n x.
Proof.
  intros a lo n x. unfold wcount. cbn [wsum].
  replace (lo - 1 + 1) with lo by lia. reflexivity.
Qed.

Lemma wcount_grow_high : forall a lo n x,
  wcount a lo (S n) x = wcount a lo n x + ind (Z.eqb (a (lo + Z.of_nat n)) x).
Proof.
  intros a lo n x. unfold wcount. apply wsum_split_last.
Qed.

(** ** Membership vs counts *)

Lemma wcount_pos_inv : forall a lo n x,
  1 <= wcount a lo n x ->
  exists i, lo <= i < lo + Z.of_nat n /\ a i = x.
Proof.
  intros a lo n x; revert lo.
  induction n as [|k IH]; intros lo H; cbn [wcount wsum] in H; [lia|].
  destruct (Z.eqb (a lo) x) eqn:E.
  - apply Z.eqb_eq in E. exists lo. split; [lia | exact E].
  - cbn [ind] in H. fold (wcount a (lo + 1) k x) in H.
    destruct (IH (lo + 1)) as [i [Hi Hx]]; [lia|].
    exists i. split; [lia | exact Hx].
Qed.

Lemma wcount_of_member : forall a lo n x i,
  lo <= i < lo + Z.of_nat n -> a i = x ->
  1 <= wcount a lo n x.
Proof.
  intros a lo n x i; revert lo.
  induction n as [|k IH]; intros lo Hi Hx; [lia|].
  cbn [wcount wsum]. fold (wcount a (lo + 1) k x).
  pose proof (wcount_nonneg a (lo + 1) k x).
  destruct (Z.eq_dec i lo) as [->|Hne].
  - rewrite Hx, Z.eqb_refl. cbn [ind]. lia.
  - assert (1 <= wcount a (lo + 1) k x) by (apply (IH (lo + 1)); [lia | exact Hx]).
    pose proof (ind_0_1 (Z.eqb (a lo) x)). lia.
Qed.

(** Distinctness, in the form the union-typed [tr_dl] walk consumes: a window
    whose every value-count is at most 1 never shows one value at two
    positions. *)
Lemma wcount_le1_distinct : forall a lo n,
  (forall x, wcount a lo n x <= 1) ->
  forall p q, lo <= p < lo + Z.of_nat n -> lo <= q < lo + Z.of_nat n ->
  p <> q -> a p <> a q.
Proof.
  intros a lo n H p q; revert lo H.
  induction n as [|k IH]; intros lo H Hp Hq Hne Heq.
  - cbn [Z.of_nat] in Hp. lia.
  - rewrite Nat2Z.inj_succ in Hp, Hq.
    assert (Htail : forall x, wcount a (lo + 1) k x <= 1).
    { intro x. specialize (H x).
      cbn [wcount wsum] in H. fold (wcount a (lo + 1) k x) in H.
      pose proof (ind_0_1 (Z.eqb (a lo) x)). lia. }
    destruct (Z.eq_dec p lo) as [->|Hpne];
      [|destruct (Z.eq_dec q lo) as [->|Hqne]].
    + specialize (H (a lo)).
      cbn [wcount wsum] in H. rewrite Z.eqb_refl in H. cbn [ind] in H.
      fold (wcount a (lo + 1) k (a lo)) in H.
      assert (1 <= wcount a (lo + 1) k (a lo)); [|lia].
      apply (wcount_of_member a (lo + 1) k (a lo) q); [lia | congruence].
    + specialize (H (a lo)).
      cbn [wcount wsum] in H. rewrite Z.eqb_refl in H. cbn [ind] in H.
      fold (wcount a (lo + 1) k (a lo)) in H.
      assert (1 <= wcount a (lo + 1) k (a lo)); [|lia].
      apply (wcount_of_member a (lo + 1) k (a lo) p); [lia | congruence].
    + assert (Hp' : lo + 1 <= p < lo + 1 + Z.of_nat k) by lia.
      assert (Hq' : lo + 1 <= q < lo + 1 + Z.of_nat k) by lia.
      exact (IH (lo + 1) Htail Hp' Hq' Hne Heq).
Qed.



(** One in-window point bounds a nonnegative sum from below. *)
Lemma wsum_one_point : forall f lo n p,
  (forall i, lo <= i < lo + Z.of_nat n -> 0 <= f i) ->
  lo <= p < lo + Z.of_nat n ->
  f p <= wsum f lo n.
Proof.
  intros f lo n; revert lo.
  induction n as [|k IH]; intros lo p Hnn Hp.
  - cbn [Z.of_nat] in Hp. lia.
  - rewrite Nat2Z.inj_succ in Hp. rewrite (wsum_split_first f lo k).
    destruct (Z.eq_dec p lo) as [->|Hne].
    + assert (0 <= wsum f (lo + 1) k)
        by (apply wsum_nonneg; intros; apply Hnn; lia).
      lia.
    + assert (0 <= f lo) by (apply Hnn; lia).
      assert (f p <= wsum f (lo + 1) k)
        by (apply IH; [intros; apply Hnn; lia | lia]).
      lia.
Qed.

(** Two distinct in-window points bound the sum from below (used to refute
    "heap_len <= 1" when two live symbols exist). *)
Lemma wsum_two_points : forall f lo n p q,
  (forall i, lo <= i < lo + Z.of_nat n -> 0 <= f i) ->
  lo <= p < lo + Z.of_nat n -> lo <= q < lo + Z.of_nat n -> p <> q ->
  f p + f q <= wsum f lo n.
Proof.
  intros f lo n; revert lo.
  induction n as [|k IH]; intros lo p q Hnn Hp Hq Hne.
  - cbn [Z.of_nat] in Hp. lia.
  - rewrite Nat2Z.inj_succ in Hp, Hq.
    rewrite (wsum_split_first f lo k).
    assert (Htail : forall i, lo + 1 <= i < lo + 1 + Z.of_nat k -> 0 <= f i)
      by (intros; apply Hnn; lia).
    destruct (Z.eq_dec p lo) as [->|Hpne];
      [|destruct (Z.eq_dec q lo) as [->|Hqne]].
    + assert (f q <= wsum f (lo + 1) k)
        by (apply wsum_one_point; [exact Htail | lia]).
      lia.
    + assert (f p <= wsum f (lo + 1) k)
        by (apply wsum_one_point; [exact Htail | lia]).
      lia.
    + assert (0 <= f lo) by (apply Hnn; lia).
      assert (f p + f q <= wsum f (lo + 1) k)
        by (apply IH; try lia; exact Htail).
      lia.
Qed.

Print Assumptions wsum_point_delta.
Print Assumptions wcount_zset_in.
Print Assumptions wcount_le1_distinct.
Print Assumptions wcount_pos_inv.
Print Assumptions wcount_of_member.
