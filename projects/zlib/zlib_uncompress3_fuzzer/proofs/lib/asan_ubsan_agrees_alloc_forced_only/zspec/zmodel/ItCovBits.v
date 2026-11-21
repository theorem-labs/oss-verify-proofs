(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import Prog ZIface InflateState Inftrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.


Fixpoint write_bits (n : nat) (v : Z) : list bool :=
  match n with
  | O => []
  | S k => Z.odd v :: write_bits k (v / 2)
  end.

Lemma write_bits_length : forall n v, (length (write_bits n v) = n)%nat.
Proof.
  induction n as [|n IH]; intro v; cbn [write_bits length]; [reflexivity|].
  now rewrite IH.
Qed.

Lemma write_bits_testbit : forall n v,
  write_bits n v = map (fun i => Z.testbit v (Z.of_nat i)) (seq 0 n).
Proof.
  induction n as [|n IH]; intro v; [reflexivity|].
  assert (Htail : write_bits n (v / 2)
                  = map (fun i : nat => Z.testbit v (Z.of_nat i)) (seq 1 n)).
  { rewrite IH, <- seq_shift, map_map. apply map_ext; intro i.
    rewrite Nat2Z.inj_succ. apply Z.div2_bits. lia. }
  cbn [write_bits seq map]. rewrite Htail. reflexivity.
Qed.

Fixpoint code_bits (v : Z) (w : nat) : list bool :=
  match w with
  | O => []
  | S k => Z.testbit v (Z.of_nat k) :: code_bits v k
  end.

Lemma code_bits_length : forall v w, length (code_bits v w) = w.
Proof.
  intros v w; induction w as [|k IH]; cbn [code_bits length]; [reflexivity|].
  now rewrite IH.
Qed.

Lemma code_bits_snoc : forall k v,
  code_bits v (S k) = code_bits (v / 2)%Z k ++ [Z.odd v].
Proof.
  induction k as [|k IH]; intro v.
  - reflexivity.
  - change (code_bits v (S (S k)))
      with (Z.testbit v (Z.of_nat (S k)) :: code_bits v (S k)).
    change (code_bits (v / 2)%Z (S k))
      with (Z.testbit (v / 2)%Z (Z.of_nat k) :: code_bits (v / 2)%Z k).
    rewrite (IH v). cbn [app]. f_equal.
    rewrite Nat2Z.inj_succ. symmetry. apply Z.div2_bits. lia.
Qed.

Lemma code_bits_rev_write_bits : forall w v, code_bits v w = rev (write_bits w v).
Proof.
  intro w; induction w as [|k IH]; intro v; [reflexivity|].
  rewrite code_bits_snoc, (IH (v / 2)%Z).
  cbn [write_bits rev]. reflexivity.
Qed.

Fixpoint it_shift_down (n : nat) (huff incr : Z) : Z :=
  match n with
  | O => incr
  | S k => if Z.eqb (Z.land huff incr) 0 then incr
           else it_shift_down k huff (Z.shiftr incr 1)
  end.

Definition it_rev_incr (huff len : Z) : Z :=
  let incr := it_shift_down 17%nat huff (Z.shiftl 1 (len - 1)) in
  if Z.eqb incr 0 then 0 else Z.land huff (incr - 1) + incr.



Fixpoint bits_val (l : list bool) : Z :=
  match l with
  | [] => 0
  | b :: r => (if b then 1 else 0) + 2 * bits_val r
  end.

Lemma bits_val_nonneg : forall l, 0 <= bits_val l.
Proof. induction l as [|b l IH]; cbn [bits_val]; [lia | destruct b; lia]. Qed.

Lemma bits_val_bound : forall l, bits_val l < 2 ^ Z.of_nat (length l).
Proof.
  induction l as [|b l IH]; cbn [bits_val length]; [cbn; lia|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  destruct b; lia.
Qed.

Lemma bits_val_app : forall l1 l2,
  bits_val (l1 ++ l2) = bits_val l1 + 2 ^ Z.of_nat (length l1) * bits_val l2.
Proof.
  induction l1 as [|b l1 IH]; intro l2; cbn [app bits_val length].
  - change (Z.of_nat 0) with 0%Z. rewrite Z.pow_0_r. lia.
  - rewrite IH, Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma bits_val_repeat_false : forall n, bits_val (repeat false n) = 0.
Proof. induction n as [|n IH]; cbn [repeat bits_val]; lia. Qed.

Lemma rev_repeat_false : forall n, rev (repeat false n) = repeat false n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [repeat rev]. rewrite IH. symmetry. apply repeat_cons.
Qed.

Lemma write_bits_bits_val : forall l, write_bits (length l) (bits_val l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|].
  cbn [length write_bits bits_val].
  assert (Hodd : Z.odd ((if b then 1 else 0) + 2 * bits_val l) = b).
  { rewrite Z.odd_add_mul_2. destruct b; reflexivity. }
  assert (Hdiv : ((if b then 1 else 0) + 2 * bits_val l) / 2 = bits_val l).
  { replace ((if b then 1 else 0) + 2 * bits_val l)
      with (bits_val l * 2 + (if b then 1 else 0)) by lia.
    rewrite Z.div_add_l by lia. destruct b; cbn; lia. }
  rewrite Hodd, Hdiv, IH. reflexivity.
Qed.

Lemma bits_val_write_bits : forall n v,
  0 <= v < 2 ^ Z.of_nat n -> bits_val (write_bits n v) = v.
Proof.
  induction n as [|n IH]; intros v Hv.
  - cbn in *. lia.
  - cbn [write_bits bits_val].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hv by lia.
    rewrite IH by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Hm : v mod 2 = if Z.odd v then 1 else 0).
    { destruct (Z.odd v) eqn:E.
      - apply Z.odd_spec in E as [k ->].
        replace (2 * k + 1) with (1 + k * 2) by lia. rewrite Z_mod_plus_full. reflexivity.
      - assert (Hev : Z.even v = true) by (rewrite <- Z.negb_odd, E; reflexivity).
        apply Z.even_spec in Hev as [k ->].
        replace (2 * k) with (k * 2) by lia. rewrite Z_mod_mult. reflexivity. }
    pose proof (Z.div_mod v 2 ltac:(lia)) as Hdm. lia.
Qed.


Definition brv (w : nat) (v : Z) : Z := bits_val (rev (write_bits w v)).

Lemma brv_nonneg : forall w v, 0 <= brv w v.
Proof. intros. apply bits_val_nonneg. Qed.

Lemma brv_bound : forall w v, brv w v < 2 ^ Z.of_nat w.
Proof.
  intros w v. unfold brv.
  pose proof (bits_val_bound (rev (write_bits w v))) as H.
  rewrite length_rev, write_bits_length in H. exact H.
Qed.

Lemma brv_range : forall w v, 0 <= brv w v < 2 ^ Z.of_nat w.
Proof. intros. split; [apply brv_nonneg | apply brv_bound]. Qed.

Lemma write_bits_brv : forall w v, write_bits w (brv w v) = rev (write_bits w v).
Proof.
  intros w v. unfold brv.
  pose proof (write_bits_bits_val (rev (write_bits w v))) as H.
  rewrite length_rev, write_bits_length in H. exact H.
Qed.

Lemma bits_val_testbit : forall l j,
  0 <= j -> Z.testbit (bits_val l) j = nth (Z.to_nat j) l false.
Proof.
  induction l as [|b l IH]; intros j Hj.
  - cbn [bits_val]. rewrite Z.bits_0. now destruct (Z.to_nat j).
  - cbn [bits_val].
    replace ((if b then 1 else 0) + 2 * bits_val l)
      with (2 * bits_val l + Z.b2z b) by (destruct b; cbn [Z.b2z]; lia).
    destruct (Z.eq_dec j 0) as [->|Hne].
    + cbn [Z.to_nat nth]. now rewrite Z.testbit_0_r.
    + replace j with (Z.succ (j - 1)) by lia.
      rewrite Z.testbit_succ_r by lia.
      rewrite IH by lia.
      replace (Z.to_nat (Z.succ (j - 1))) with (S (Z.to_nat (j - 1))) by lia.
      reflexivity.
Qed.

Lemma nth_write_bits : forall w x k,
  (k < w)%nat -> nth k (write_bits w x) false = Z.testbit x (Z.of_nat k).
Proof.
  intros w x k Hk. rewrite write_bits_testbit.
  rewrite (nth_indep _ false (Z.testbit x (Z.of_nat 0)))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth (fun i : nat => Z.testbit x (Z.of_nat i)) (seq 0 w) 0%nat k).
  now rewrite seq_nth by lia.
Qed.

Lemma brv_testbit : forall w v j,
  (0 <= j < Z.of_nat w)%Z -> Z.testbit (brv w v) j = Z.testbit v (Z.of_nat w - 1 - j).
Proof.
  intros w v j Hj. unfold brv.
  rewrite bits_val_testbit by lia.
  rewrite rev_nth by (rewrite write_bits_length; lia).
  rewrite write_bits_length.
  rewrite nth_write_bits by lia. f_equal. lia.
Qed.

Lemma brv_testbit_high : forall w v j,
  (Z.of_nat w <= j)%Z -> Z.testbit (brv w v) j = false.
Proof.
  intros w v j Hj.
  pose proof (brv_range w v) as Hr.
  rewrite <- (Z.mod_small (brv w v) (2 ^ Z.of_nat w)) by lia.
  apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma brv_mod : forall w v, brv w (v mod 2 ^ Z.of_nat w) = brv w v.
Proof.
  intros w v. unfold brv. f_equal. f_equal.
  rewrite !write_bits_testbit. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  apply Z.mod_pow2_bits_low. lia.
Qed.

Lemma write_bits_mul_pow2 : forall k w v,
  write_bits (k + w) (2 ^ Z.of_nat k * v) = repeat false k ++ write_bits w v.
Proof.
  induction k as [|k IH]; intros w v.
  - cbn [repeat app Nat.add]. change (Z.of_nat 0) with 0%Z.
    rewrite Z.pow_0_r, Z.mul_1_l. reflexivity.
  - cbn [repeat app]. replace (S k + w)%nat with (S (k + w))%nat by lia.
    cbn [write_bits]. f_equal.
    + rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite <- Z.mul_assoc, Z.odd_mul. reflexivity.
    + rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite <- Z.mul_assoc, Z.mul_comm, Z.div_mul by lia.
      apply IH.
Qed.

Lemma brv_shift : forall k w v, brv (k + w) (2 ^ Z.of_nat k * v) = brv w v.
Proof.
  intros k w v. unfold brv.
  rewrite write_bits_mul_pow2, rev_app_distr, bits_val_app.
  rewrite rev_repeat_false, bits_val_repeat_false. lia.
Qed.

Lemma write_bits_eq_code_bits_iff : forall w (i C : Z),
  write_bits w i = code_bits C w <-> i mod 2 ^ Z.of_nat w = brv w C.
Proof.
  intros w i C.
  rewrite code_bits_rev_write_bits, <- write_bits_brv.
  split; intro H.
  - assert (Hv : bits_val (write_bits w i) = bits_val (write_bits w (brv w C)))
      by now rewrite H.
    rewrite (bits_val_write_bits w (brv w C)) in Hv by apply brv_range.
    rewrite <- Hv.
    assert (Hmod : write_bits w i = write_bits w (i mod 2 ^ Z.of_nat w)).
    { rewrite !write_bits_testbit. apply map_ext_in. intros j Hj. apply in_seq in Hj.
      symmetry. apply Z.mod_pow2_bits_low. lia. }
    rewrite Hmod at 1.
    rewrite bits_val_write_bits; [reflexivity|].
    split; [apply Z.mod_pos_bound | apply Z.mod_pos_bound]; apply Z.pow_pos_nonneg; lia.
  - assert (Hmod : write_bits w i = write_bits w (i mod 2 ^ Z.of_nat w)).
    { rewrite !write_bits_testbit. apply map_ext_in. intros j Hj. apply in_seq in Hj.
      symmetry. apply Z.mod_pow2_bits_low. lia. }
    rewrite Hmod, H. reflexivity.
Qed.


Lemma land_pow2 : forall a m, 0 <= m ->
  Z.land a (2 ^ m) = if Z.testbit a m then 2 ^ m else 0.
Proof.
  intros a m Hm. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, (Z.pow2_bits_eqb m n) by lia.
  destruct (Z.testbit a m) eqn:Ea.
  - rewrite (Z.pow2_bits_eqb m n) by lia.
    destruct (Z.eqb_spec m n) as [->|Hne]; [now rewrite Ea | now rewrite andb_false_r].
  - rewrite Z.bits_0.
    destruct (Z.eqb_spec m n) as [->|Hne]; [now rewrite Ea, andb_false_l | now rewrite andb_false_r].
Qed.

Lemma shiftr_pow2_1 : forall m, 0 < m -> Z.shiftr (2 ^ m) 1 = 2 ^ (m - 1).
Proof.
  intros m Hm. rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 1) with 2 by reflexivity.
  replace (2 ^ m) with (2 ^ (m - 1) * 2)
    by (rewrite Z.mul_comm, <- (Z.pow_succ_r 2 (m-1)) by lia; f_equal; lia).
  rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma shiftr_1_1 : Z.shiftr 1 1 = 0.
Proof. reflexivity. Qed.

Lemma shift_down_find : forall (d f : nat) (huff m k : Z),
  0 <= k <= m -> m - k = Z.of_nat d -> (d < f)%nat ->
  Z.testbit huff k = false ->
  (forall j, k < j <= m -> Z.testbit huff j = true) ->
  it_shift_down f huff (2 ^ m) = 2 ^ k.
Proof.
  induction d as [|d IH]; intros f huff m k Hkm Hd Hf Hk Hj.
  -
    assert (m = k) by lia. subst m.
    destruct f as [|f]; [lia|]. cbn [it_shift_down].
    rewrite land_pow2 by lia. rewrite Hk. cbn. reflexivity.
  - destruct f as [|f]; [lia|]. cbn [it_shift_down].
    assert (Hmk : k < m) by lia.
    rewrite land_pow2 by lia.
    rewrite (Hj m) by lia.
    destruct (Z.eqb_spec (2 ^ m) 0) as [Hz|_].
    { exfalso. pose proof (Z.pow_pos_nonneg 2 m ltac:(lia) ltac:(lia)). lia. }
    rewrite shiftr_pow2_1 by lia.
    apply (IH f huff (m - 1) k); try lia; auto.
    intros j Hj'. apply Hj. lia.
Qed.

Lemma shift_down_all : forall (d f : nat) (huff m : Z),
  0 <= m -> m = Z.of_nat d -> (S d < f)%nat ->
  (forall j, 0 <= j <= m -> Z.testbit huff j = true) ->
  it_shift_down f huff (2 ^ m) = 0.
Proof.
  induction d as [|d IH]; intros f huff m Hm Hd Hf Hj.
  - change (Z.of_nat 0) with 0 in Hd. subst m.
    destruct f as [|f]; [lia|]. cbn [it_shift_down].
    rewrite land_pow2 by lia. rewrite (Hj 0) by lia.
    change (2 ^ 0) with 1. cbn [Z.eqb].
    destruct f as [|f]; [lia|]. cbn [it_shift_down].
    rewrite shiftr_1_1, Z.land_0_r. reflexivity.
  - destruct f as [|f]; [lia|]. cbn [it_shift_down].
    rewrite land_pow2 by lia. rewrite (Hj m) by lia.
    destruct (Z.eqb_spec (2 ^ m) 0) as [Hz|_].
    { exfalso. pose proof (Z.pow_pos_nonneg 2 m ltac:(lia) ltac:(lia)). lia. }
    rewrite shiftr_pow2_1 by lia.
    apply (IH f huff (m - 1)); try lia.
    intros j Hj'. apply Hj. lia.
Qed.


Lemma least_false : forall (n : nat) (P : nat -> bool),
  (exists j, (j < n)%nat /\ P j = false) ->
  exists t, (t < n)%nat /\ P t = false /\ (forall j, (j < t)%nat -> P j = true).
Proof.
  induction n as [|n IH]; intros P (j & Hj & HP); [lia|].
  destruct (P 0%nat) eqn:E0.
  - destruct j as [|j]; [congruence|].
    assert (Hpre : exists i, (i < n)%nat /\ (fun i => P (S i)) i = false).
    { exists j. split; [lia | exact HP]. }
    destruct (IH (fun i => P (S i)) Hpre) as (t & Ht & Hf & Hl).
    exists (S t). split; [lia|]. split; [exact Hf|].
    intros [|i] Hi; [exact E0 | apply (Hl i); lia].
  - exists 0%nat. split; [lia|]. split; [exact E0 | intros; lia].
Qed.

Lemma all_ones_eq : forall (w : nat) (C : Z),
  0 <= C < 2 ^ Z.of_nat w ->
  (forall j, 0 <= j < Z.of_nat w -> Z.testbit C j = true) ->
  C = 2 ^ Z.of_nat w - 1.
Proof.
  intros w C HC Hall.
  replace (2 ^ Z.of_nat w - 1) with (Z.ones (Z.of_nat w))
    by (rewrite Z.ones_equiv; lia).
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.testbit_ones by lia.
  destruct (Z.ltb_spec n (Z.of_nat w)) as [Hlt|Hge].
  - rewrite Hall by lia. destruct (Z.leb_spec 0 n); [reflexivity|lia].
  - rewrite <- (Z.mod_small C (2 ^ Z.of_nat w)) by lia.
    rewrite Z.mod_pow2_bits_high by lia.
    destruct (Z.leb_spec 0 n); destruct (Z.ltb_spec n (Z.of_nat w)); cbn; lia.
Qed.

Lemma all_or_clear : forall (w : nat) (C : Z),
  (forall j, 0 <= j < Z.of_nat w -> Z.testbit C j = true)
  \/ (exists j, (j < w)%nat /\ Z.testbit C (Z.of_nat j) = false).
Proof.
  induction w as [|w IH]; intro C.
  - left. intros j Hj. cbn in Hj. lia.
  - destruct (IH C) as [Hall | (j & Hj & Hf)].
    + destruct (Z.testbit C (Z.of_nat w)) eqn:E.
      * left. intros j Hj. rewrite Nat2Z.inj_succ in Hj.
        destruct (Z.eq_dec j (Z.of_nat w)) as [->|Hne]; [exact E | apply Hall; lia].
      * right. exists w. split; [lia | exact E].
    + right. exists j. split; [lia | exact Hf].
Qed.

Lemma exists_first_clear : forall (w : nat) (C : Z),
  0 <= C < 2 ^ Z.of_nat w - 1 ->
  exists t, (0 <= t < Z.of_nat w)%Z /\ Z.testbit C t = false
            /\ forall j, 0 <= j < t -> Z.testbit C j = true.
Proof.
  intros w C HC.
  assert (Hex : exists j, (j < w)%nat /\ Z.testbit C (Z.of_nat j) = false).
  { destruct (all_or_clear w C) as [H|H]; [|exact H].
    exfalso. pose proof (all_ones_eq w C ltac:(lia) H). lia. }
  destruct (least_false w (fun j => Z.testbit C (Z.of_nat j)) Hex)
    as (t & Ht & Hf & Hl).
  exists (Z.of_nat t). split; [lia|]. split; [exact Hf|].
  intros j Hj. replace j with (Z.of_nat (Z.to_nat j)) by lia.
  apply Hl. lia.
Qed.


Lemma succ_bits : forall C t,
  0 <= t -> 0 <= C ->
  Z.testbit C t = false ->
  (forall j, 0 <= j < t -> Z.testbit C j = true) ->
  (forall m, 0 <= m < t -> Z.testbit (C + 1) m = false)
  /\ Z.testbit (C + 1) t = true
  /\ (forall m, t < m -> Z.testbit (C + 1) m = Z.testbit C m).
Proof.
  intros C t Ht HC Hclear Hones.
  set (q := C / 2 ^ (t + 1)).
  assert (Hpow : 0 < 2 ^ (t + 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hmod : C mod 2 ^ (t + 1) = 2 ^ t - 1).
  { replace (2 ^ t - 1) with (Z.ones t) by (rewrite Z.ones_equiv; lia).
    apply Z.bits_inj'. intros n Hn.
    rewrite Z.testbit_ones by lia.
    destruct (Z.ltb_spec n (t + 1)) as [Hlt|Hge].
    - rewrite Z.mod_pow2_bits_low by lia.
      destruct (Z.eq_dec n t) as [->|Hne].
      + rewrite Hclear. destruct (Z.leb_spec 0 t); destruct (Z.ltb_spec t t); cbn; lia.
      + rewrite Hones by lia.
        destruct (Z.leb_spec 0 n); destruct (Z.ltb_spec n t); cbn; lia.
    - rewrite Z.mod_pow2_bits_high by lia.
      destruct (Z.leb_spec 0 n); destruct (Z.ltb_spec n t); cbn; lia. }
  assert (HCq : C = q * 2 ^ (t + 1) + (2 ^ t - 1)).
  { unfold q. pose proof (Z.div_mod C (2 ^ (t + 1)) ltac:(lia)) as H. lia. }
  assert (Hsucc : C + 1 = (1 + 2 * q) * 2 ^ t).
  { rewrite HCq. rewrite Z.pow_add_r by lia. cbn [Z.pow Z.pow_pos Pos.iter]. lia. }
  split; [| split].
  - intros m Hm. rewrite Hsucc. apply Z.mul_pow2_bits_low. lia.
  - rewrite Hsucc.
    apply (Z.testbit_unique _ _ true 0 q); [split; [lia | apply Z.pow_pos_nonneg; lia] | cbn [Z.b2z]; lia].
  - intros m Hm.
    assert (Hj0 : 0 <= m - t - 1) by lia.
    remember (m - t - 1) as j eqn:Hjd.
    assert (HC2 : Z.testbit C m = Z.testbit q j).
    { unfold q. rewrite Z.div_pow2_bits by lia. f_equal. lia. }
    rewrite HC2, Hsucc, Z.mul_pow2_bits by lia.
    replace (m - t) with (Z.succ j) by lia.
    replace (1 + 2 * q) with (2 * q + Z.b2z true) by (cbn [Z.b2z]; lia).
    rewrite Z.testbit_succ_r by lia. reflexivity.
Qed.


Lemma testbit_lt_pow2 : forall a k j, 0 <= a < 2 ^ k -> k <= j -> Z.testbit a j = false.
Proof.
  intros a k j Ha Hj.
  rewrite <- (Z.mod_small a (2 ^ k)) by lia.
  apply Z.mod_pow2_bits_high. split; [|exact Hj].
  destruct (Z.leb_spec 0 k) as [|Hneg]; [assumption|].
  exfalso. rewrite Z.pow_neg_r in Ha by lia. lia.
Qed.

Lemma testbit_add_pow2 : forall a k j,
  0 <= k -> 0 <= a < 2 ^ k -> 0 <= j ->
  Z.testbit (a + 2 ^ k) j = xorb (Z.testbit a j) (k =? j).
Proof.
  intros a k j Hk Ha Hj.
  assert (Hak : Z.land a (2 ^ k) = 0).
  { rewrite land_pow2 by lia. now rewrite (testbit_lt_pow2 a k k Ha ltac:(lia)). }
  rewrite (Z.add_nocarry_lxor a (2 ^ k) Hak), Z.lxor_spec.
  now rewrite Z.pow2_bits_eqb by lia.
Qed.

Theorem it_rev_incr_succ : forall (w : nat) (C : Z),
  (0 < w <= 16)%nat -> 0 <= C < 2 ^ Z.of_nat w - 1 ->
  it_rev_incr (brv w C) (Z.of_nat w) = brv w (C + 1).
Proof.
  intros w C Hw HC.
  destruct (exists_first_clear w C HC) as (t & Ht & Hclear & Hones).
  pose (k := Z.of_nat w - 1 - t).
  assert (Hkdef : k = Z.of_nat w - 1 - t) by reflexivity.
  clearbody k.
  assert (Hk : 0 <= k <= Z.of_nat w - 1) by lia.
  assert (Hhk : Z.testbit (brv w C) k = false).
  { rewrite brv_testbit by lia.
    replace (Z.of_nat w - 1 - k) with t by lia. exact Hclear. }
  assert (Hhj : forall j, k < j <= Z.of_nat w - 1 -> Z.testbit (brv w C) j = true).
  { intros j Hj. rewrite brv_testbit by lia. apply Hones. lia. }
  assert (Hscan : it_shift_down 17%nat (brv w C) (2 ^ (Z.of_nat w - 1)) = 2 ^ k).
  { apply (shift_down_find (Z.to_nat t) 17%nat (brv w C) (Z.of_nat w - 1) k);
      [ lia | lia | lia | exact Hhk | exact Hhj ]. }
  assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  unfold it_rev_incr. rewrite Z.shiftl_1_l, Hscan.
  destruct (Z.eqb_spec (2 ^ k) 0) as [Hz|_]; [lia|].
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  assert (Hhmod : 0 <= brv w C mod 2 ^ k < 2 ^ k) by (apply Z.mod_pos_bound; lia).
  destruct (succ_bits C t ltac:(lia) ltac:(lia) Hclear Hones) as (S1 & S2 & S3).
  apply Z.bits_inj'. intros n Hn.
  assert (Hb : 0 <= C + 1 < 2 ^ Z.of_nat w) by lia.
  destruct (Z.ltb_spec n (Z.of_nat w)) as [Hlt|Hge].
  - rewrite brv_testbit by lia.
    rewrite testbit_add_pow2 by lia.
    destruct (Z.compare_spec n k) as [Heq|Hnk|Hnk].
    +
      subst n. rewrite Z.eqb_refl.
      rewrite (testbit_lt_pow2 (brv w C mod 2 ^ k) k k Hhmod ltac:(lia)).
      cbn [xorb]. replace (Z.of_nat w - 1 - k) with t by lia. symmetry. exact S2.
    +
      rewrite Z.mod_pow2_bits_low by lia.
      destruct (Z.eqb_spec k n); [lia|]. rewrite xorb_false_r.
      rewrite brv_testbit by lia. symmetry. apply S3. lia.
    +
      rewrite (testbit_lt_pow2 (brv w C mod 2 ^ k) k n Hhmod ltac:(lia)).
      destruct (Z.eqb_spec k n); [lia|]. cbn [xorb].
      symmetry. apply S1. lia.
  - rewrite (brv_testbit_high w (C + 1) n) by lia.
    assert (Hsmall : 0 <= brv w C mod 2 ^ k + 2 ^ k < 2 ^ (k + 1)).
    { rewrite Z.pow_add_r by lia. cbn [Z.pow Z.pow_pos Pos.iter]. lia. }
    rewrite (testbit_lt_pow2 _ (k + 1) n Hsmall ltac:(lia)). reflexivity.
Qed.

Theorem it_rev_incr_last : forall (w : nat),
  (0 < w <= 16)%nat ->
  it_rev_incr (brv w (2 ^ Z.of_nat w - 1)) (Z.of_nat w) = 0.
Proof.
  intros w Hw.
  assert (Hall : forall j, 0 <= j <= Z.of_nat w - 1 ->
                 Z.testbit (brv w (2 ^ Z.of_nat w - 1)) j = true).
  { intros j Hj. rewrite brv_testbit by lia.
    replace (2 ^ Z.of_nat w - 1) with (Z.ones (Z.of_nat w)) by (rewrite Z.ones_equiv; lia).
    rewrite Z.testbit_ones by lia.
    destruct (Z.leb_spec 0 (Z.of_nat w - 1 - j)); destruct (Z.ltb_spec (Z.of_nat w - 1 - j) (Z.of_nat w)); cbn; lia. }
  unfold it_rev_incr. rewrite Z.shiftl_1_l.
  rewrite (shift_down_all (Z.to_nat (Z.of_nat w - 1)) 17%nat _ (Z.of_nat w - 1));
    try lia; [reflexivity | exact Hall].
Qed.


Lemma brv_mod_pow2 : forall (w u : nat) (C : Z),
  (u <= w)%nat -> 0 <= C ->
  brv w C mod 2 ^ Z.of_nat u = brv u (C / 2 ^ Z.of_nat (w - u)).
Proof.
  intros w u C Huw HC.
  assert (Hp : 0 < 2 ^ Z.of_nat u) by (apply Z.pow_pos_nonneg; lia).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z.ltb_spec n (Z.of_nat u)) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low by lia.
    rewrite brv_testbit by lia. rewrite brv_testbit by lia.
    rewrite Z.div_pow2_bits by lia. f_equal. lia.
  - rewrite Z.mod_pow2_bits_high by lia.
    symmetry. apply brv_testbit_high. lia.
Qed.

Lemma brv_inj : forall (u : nat) (X Y : Z),
  0 <= X < 2 ^ Z.of_nat u -> 0 <= Y < 2 ^ Z.of_nat u ->
  brv u X = brv u Y -> X = Y.
Proof.
  intros u X Y HX HY H.
  assert (Hw : rev (write_bits u X) = rev (write_bits u Y))
    by (rewrite <- !write_bits_brv; now rewrite H).
  assert (Hw' : write_bits u X = write_bits u Y)
    by (rewrite <- (rev_involutive (write_bits u X)), Hw, rev_involutive; reflexivity).
  rewrite <- (bits_val_write_bits u X HX), <- (bits_val_write_bits u Y HY).
  now rewrite Hw'.
Qed.

Lemma brv_eq_0 : forall (u : nat) (X : Z),
  0 <= X < 2 ^ Z.of_nat u -> brv u X = 0 -> X = 0.
Proof.
  intros u X HX H. apply (brv_inj u X 0); [exact HX | | ].
  - split; [lia | apply Z.pow_pos_nonneg; lia].
  - rewrite H. unfold brv.
    assert (Hz : write_bits u 0 = repeat false u).
    { clear. induction u as [|u IH]; [reflexivity|].
      cbn [write_bits repeat]. rewrite Zdiv_0_l. now rewrite IH. }
    rewrite Hz, rev_repeat_false. symmetry. apply bits_val_repeat_false.
Qed.

Lemma it_rev_incr_succZ : forall (w C : Z),
  1 <= w <= 16 -> 0 <= C < 2 ^ w - 1 ->
  it_rev_incr (brv (Z.to_nat w) C) w = brv (Z.to_nat w) (C + 1).
Proof.
  intros w C Hw HC.
  assert (Hid : Z.of_nat (Z.to_nat w) = w) by lia.
  pose proof (it_rev_incr_succ (Z.to_nat w) C ltac:(lia) ltac:(rewrite Hid; lia)) as H.
  rewrite Hid in H. exact H.
Qed.

Lemma it_rev_incr_lastZ : forall (w : Z),
  1 <= w <= 16 -> it_rev_incr (brv (Z.to_nat w) (2 ^ w - 1)) w = 0.
Proof.
  intros w Hw.
  assert (Hid : Z.of_nat (Z.to_nat w) = w) by lia.
  pose proof (it_rev_incr_last (Z.to_nat w) ltac:(lia)) as H.
  rewrite Hid in H. exact H.
Qed.

Lemma brv_0 : forall w, brv w 0 = 0.
Proof.
  intro w. unfold brv.
  assert (Hz : write_bits w 0 = repeat false w).
  { induction w as [|w IH]; [reflexivity|].
    cbn [write_bits repeat]. rewrite Zdiv_0_l. now rewrite IH. }
  rewrite Hz, rev_repeat_false. apply bits_val_repeat_false.
Qed.

Lemma brv_mod_shiftr : forall (w u : nat) (C : Z),
  (u <= w)%nat -> 0 <= C ->
  brv w C mod 2 ^ Z.of_nat u = brv u (Z.shiftr C (Z.of_nat (w - u))).
Proof.
  intros w u C Huw HC. rewrite Z.shiftr_div_pow2 by lia.
  apply brv_mod_pow2; assumption.
Qed.


Lemma it_scan_loopZ_eq : forall (k : nat) (n : Z) (f : nat) (huff : Z),
  Z.of_nat k + 2 <= n -> (k + 2 <= f)%nat ->
  loopZ n (fun incr => if negb (Z.land huff incr =? 0) then (true, Z.shiftr incr 1) else (false, incr))
        (2 ^ Z.of_nat k)
  = it_shift_down f huff (2 ^ Z.of_nat k).
Proof.
  induction k as [|k IH]; intros n f huff Hn Hf.
  - rewrite loopZ_step by lia. destruct f as [|f]; [lia|]. cbn [it_shift_down].
    change (2 ^ Z.of_nat 0) with 1.
    destruct (Z.land huff 1 =? 0) eqn:E; cbn [negb].
    + reflexivity.
    + rewrite shiftr_1_1. rewrite loopZ_step by lia. rewrite Z.land_0_r. cbn.
      destruct f as [|f]; cbn [it_shift_down]; [reflexivity|]. rewrite Z.land_0_r. reflexivity.
  - rewrite loopZ_step by lia. destruct f as [|f]; [lia|]. cbn [it_shift_down].
    destruct (Z.land huff (2 ^ Z.of_nat (S k)) =? 0) eqn:E; cbn [negb].
    + reflexivity.
    + rewrite shiftr_pow2_1 by lia.
      replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia.
      apply IH; lia.
Qed.

Lemma it_incr_back_eq : forall huff len, 1 <= len <= 16 ->
  it_incr_back huff len = it_shift_down 17 huff (Z.shiftl 1 (len - 1)).
Proof.
  intros huff len Hlen. unfold it_incr_back.
  assert (Hs : shl32 1 (len - 1) = 2 ^ Z.of_nat (Z.to_nat (len - 1))).
  { unfold shl32. rewrite Z.shiftl_1_l. rewrite Z2Nat.id by lia. apply wrap32_id.
    split; [apply Z.pow_nonneg; lia|].
    apply Z.le_lt_trans with (m := 2 ^ 15); [apply Z.pow_le_mono_r; lia | reflexivity]. }
  rewrite Hs. rewrite Z.shiftl_1_l.
  replace (2 ^ (len - 1)) with (2 ^ Z.of_nat (Z.to_nat (len - 1))) by (rewrite Z2Nat.id by lia; reflexivity).
  apply it_scan_loopZ_eq; lia.
Qed.

Lemma it_huff_next_eq : forall huff len, 1 <= len <= 16 ->
  (let incr := it_incr_back huff len in
   if negb (incr =? 0) then Z.land huff (incr - 1) + incr else 0) = it_rev_incr huff len.
Proof.
  intros huff len Hlen. cbv zeta. rewrite it_incr_back_eq by exact Hlen.
  unfold it_rev_incr. destruct (_ =? 0); reflexivity.
Qed.
