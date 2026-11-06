(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition sf_e2 (E : Z) : Z := if E =? 0 then -1074 else E - 1075.

Definition sf_index (e2 : Z) : Z := 294 - Z.shiftr (e2 * 315653) 20.

Definition sf_index2 (e2 : Z) : Z := 292 - Z.shiftr (e2 * 631305 - 261663) 21.

Definition SF_TABLE_ENTRIES : Z := 619.

Lemma sf_e2_range : forall E, 0 <= E <= 2047 -> -1074 <= sf_e2 E <= 972.
Proof. intros E H. unfold sf_e2. destruct (Z.eqb_spec E 0); lia. Qed.

Lemma shiftr_bounds : forall x n lo hi, 0 <= n -> lo * 2 ^ n <= x -> x < (hi + 1) * 2 ^ n -> lo <= Z.shiftr x n <= hi.
Proof.
  intros x n lo hi Hn Hlo Hhi. rewrite Z.shiftr_div_pow2 by exact Hn.
  assert (Hp : 0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  split.
  - apply Z.div_le_lower_bound; [exact Hp| lia].
  - assert (x / 2 ^ n < hi + 1) by (apply Z.div_lt_upper_bound; [exact Hp| lia]). lia.
Qed.

Lemma sf_prod_small : forall e2, -1074 <= e2 <= 972 -> - 2 ^ 31 <= e2 * 315653 < 2 ^ 31 /\ - 2 ^ 31 <= e2 * 631305 - 261663 < 2 ^ 31.
Proof. intros e2 H. change (2 ^ 31) with 2147483648. lia. Qed.

Theorem sf_index_range : forall e2, -1074 <= e2 <= 972 -> 2 <= sf_index e2 <= 618 /\ 0 <= 16 * sf_index e2 /\ 16 * sf_index e2 + 16 <= 16 * SF_TABLE_ENTRIES.
Proof.
  intros e2 H. unfold sf_index, SF_TABLE_ENTRIES.
  pose proof (shiftr_bounds (e2 * 315653) 20 (-324) 292 ltac:(lia)) as HB.
  change (2 ^ 20) with 1048576 in HB. specialize (HB ltac:(lia) ltac:(lia)). lia.
Qed.

Theorem sf_index2_range : forall e2, -1074 <= e2 <= 972 -> 0 <= sf_index2 e2 <= 616 /\ 16 * sf_index2 e2 + 8 <= 16 * SF_TABLE_ENTRIES.
Proof.
  intros e2 H. unfold sf_index2, SF_TABLE_ENTRIES.
  pose proof (shiftr_bounds (e2 * 631305 - 261663) 21 (-324) 292 ltac:(lia)) as HB.
  change (2 ^ 21) with 2097152 in HB. specialize (HB ltac:(lia) ltac:(lia)). lia.
Qed.

Corollary sf_index_field : forall E, 0 <= E <= 2047 ->
  2 <= sf_index (sf_e2 E) <= 618 /\ 0 <= sf_index2 (sf_e2 E) <= 616.
Proof.
  intros E H. pose proof (sf_e2_range E H) as R.
  split; [exact (proj1 (sf_index_range _ R))| exact (proj1 (sf_index2_range _ R))].
Qed.

Fixpoint ndig (fuel : nat) (w : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if w <? 10 then 1 else if w <? 100 then 2 else 2 + ndig f (w / 100)
  end.

Lemma ndig_bound : forall fuel w k, 0 <= w < 100 ^ k -> (Z.to_nat k <= fuel)%nat -> 1 <= k -> 1 <= ndig fuel w <= 2 * k.
Proof.
  induction fuel as [|f IH]; intros w k Hw Hf Hk; [lia|]. cbn [ndig].
  destruct (Z.ltb_spec w 10); [lia|]. destruct (Z.ltb_spec w 100); [lia|].
  assert (Hk2 : 2 <= k).
  { destruct (Z.eq_dec k 1) as [->|]; [change (100 ^ 1) with 100 in Hw; lia| lia]. }
  assert (Hd : 0 <= w / 100 < 100 ^ (k - 1)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    replace (100 * 100 ^ (k - 1)) with (100 ^ k); [lia|]. rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  specialize (IH (w / 100) (k - 1) Hd ltac:(lia) ltac:(lia)). lia.
Qed.

Theorem ndig_u64 : forall w, 0 <= w < 2 ^ 64 -> 1 <= ndig 10 w <= 20.
Proof.
  intros w H. apply (ndig_bound 10 w 10); [| cbn; lia| lia].
  change (2 ^ 64) with 18446744073709551616 in H. change (100 ^ 10) with 100000000000000000000. lia.
Qed.

Inductive layout := LFixedInt | LFixedFrac | LSmall | LExp.

Definition tc_layout (n e : Z) : layout :=
  let pt := n + e in
  if (0 <=? e) && (pt <=? 15) then LFixedInt
  else if (1 <=? pt) && (pt <=? 15) then LFixedFrac
  else if (-3 <=? pt) && (pt <=? 0) then LSmall
  else LExp.

Definition tc_writes (n e : Z) : list (Z * Z) :=
  let pt := n + e in
  (0, 17) ::
  match tc_layout n e with
  | LFixedInt  => [(n, n + 16); (pt, pt + 2)]
  | LFixedFrac => [(pt + 1, pt + 17); (pt, pt + 1)]
  | LSmall     => [(0, 6); (2 - pt, 2 - pt + 17)]
  | LExp       => (if n =? 1 then [] else [(2, 18); (1, 2)])
                  ++ (let b := if n =? 1 then 0 else n in [(b + 1, b + 6)])
  end.

Definition tc_end (n e : Z) (x3 : bool) : Z :=
  let pt := n + e in
  match tc_layout n e with
  | LFixedInt  => pt + 2
  | LFixedFrac => n + 1
  | LSmall     => n + (- pt) + 2
  | LExp       => (if n =? 1 then 0 else n) + (if x3 then 6 else 5)
  end.

Definition within (lim : Z) (iv : Z * Z) : Prop := 0 <= fst iv /\ fst iv <= snd iv /\ snd iv <= lim.

Theorem tc_writes_bound : forall n e, 1 <= n <= 20 -> Forall (within 37) (tc_writes n e).
Proof.
  intros n e Hn. unfold tc_writes, tc_layout.
  constructor; [unfold within; cbn; lia|].
  destruct ((0 <=? e) && (n + e <=? 15)) eqn:E1.
  { apply andb_prop in E1. destruct E1 as [A B]. apply Z.leb_le in A, B.
    repeat constructor; unfold within; cbn [fst snd]; lia. }
  destruct ((1 <=? n + e) && (n + e <=? 15)) eqn:E2.
  { apply andb_prop in E2. destruct E2 as [A B]. apply Z.leb_le in A, B.
    repeat constructor; unfold within; cbn [fst snd]; lia. }
  destruct ((-3 <=? n + e) && (n + e <=? 0)) eqn:E3.
  { apply andb_prop in E3. destruct E3 as [A B]. apply Z.leb_le in A, B.
    repeat constructor; unfold within; cbn [fst snd]; lia. }
  destruct (Z.eqb_spec n 1); cbn [app]; repeat constructor; unfold within; cbn [fst snd]; lia.
Qed.

Theorem tc_end_bound : forall n e x3, 1 <= n <= 20 -> 2 <= tc_end n e x3 <= 26.
Proof.
  intros n e x3 Hn. unfold tc_end, tc_layout.
  destruct ((0 <=? e) && (n + e <=? 15)) eqn:E1.
  { apply andb_prop in E1. destruct E1 as [A B]. apply Z.leb_le in A, B. lia. }
  destruct ((1 <=? n + e) && (n + e <=? 15)) eqn:E2.
  { apply andb_prop in E2. destruct E2 as [A B]. apply Z.leb_le in A, B. lia. }
  destruct ((-3 <=? n + e) && (n + e <=? 0)) eqn:E3.
  { apply andb_prop in E3. destruct E3 as [A B]. apply Z.leb_le in A, B. lia. }
  destruct (Z.eqb_spec n 1); destruct x3; lia.
Qed.

Corollary tc_buffer_40 : forall (neg : bool) n e x3, 1 <= n <= 20 ->
  let s := if neg then 1 else 0 in
  Forall (fun iv => 0 <= s + fst iv /\ s + snd iv <= 40) (tc_writes n e) /\ 3 <= s + tc_end n e x3 + 1 /\ s + tc_end n e x3 <= 27.
Proof.
  intros neg n e x3 Hn s. pose proof (tc_writes_bound n e Hn) as W. pose proof (tc_end_bound n e x3 Hn) as E.
  split; [| subst s; destruct neg; lia].
  eapply Forall_impl; [| exact W]. intros [lo hi] (A & B & C). cbn [fst snd] in *. subst s. destruct neg; lia.
Qed.

Definition sf_k (e2 : Z) : Z := Z.shiftr (e2 * 315653) 20.
Lemma sf_exp_range : forall e2 t, -1074 <= e2 <= 972 -> 0 <= t <= 16 -> -324 <= sf_k e2 + t <= 308.
Proof.
  intros e2 t H Ht. unfold sf_k.
  pose proof (shiftr_bounds (e2 * 315653) 20 (-324) 292 ltac:(lia)) as HB.
  change (2 ^ 20) with 1048576 in HB. specialize (HB ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma tc_pt_int32 : forall n e, 1 <= n <= 20 -> -324 <= e <= 308 -> - 2 ^ 31 <= n + e - 16 /\ n + e + 3 < 2 ^ 31.
Proof. intros n e Hn He. change (2 ^ 31) with 2147483648. lia. Qed.

Definition tc_zero_end : Z := 3.
