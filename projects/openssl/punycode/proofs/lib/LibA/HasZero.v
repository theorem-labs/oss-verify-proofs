(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint V (l : list Z) : Z := match l with [] => 0 | b :: r => b + 256 * V r end.
Fixpoint ONES (k : nat) : Z := match k with O => 0 | S k' => 1 + 256 * ONES k' end.
Fixpoint HIGHS (k : nat) : Z := match k with O => 0 | S k' => 128 + 256 * HIGHS k' end.
Definition bytes_ok (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.
Fixpoint allnz (l : list Z) : bool := match l with [] => true | b :: r => negb (b =? 0) && allnz r end.

(* [comment removed for export] *)
Definition E (l : list Z) (w : Z) : Z :=
  Z.land (Z.lor (Z.lnot (V l - ONES (length l) - w)) (V l)) (HIGHS (length l)).

Lemma V_nonneg l : bytes_ok l -> 0 <= V l.
Proof. induction 1; cbn [V]; lia. Qed.
Lemma V_bound l : bytes_ok l -> V l < 256 ^ Z.of_nat (length l).
Proof.
  induction 1 as [|b l Hb Hl IH]; cbn [V length]. lia.
  replace (Z.of_nat (S (length l))) with (Z.of_nat (length l) + 1) by lia.
  rewrite Z.pow_add_r by lia. change (256 ^ 1) with 256. lia.
Qed.
Lemma HIGHS_nonneg k : 0 <= HIGHS k. Proof. induction k; cbn [HIGHS]; lia. Qed.
Lemma HIGHS_bound k : HIGHS k < 256 ^ Z.of_nat k.
Proof.
  induction k; cbn [HIGHS]. lia.
  replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. rewrite Z.pow_add_r by lia. change (256 ^ 1) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma testbit_lo m T j : 0 <= m < 256 -> 0 <= j < 8 -> Z.testbit (m + 256 * T) j = Z.testbit m j.
Proof.
  intros Hm Hj. rewrite <- (Z.mod_pow2_bits_low (m + 256 * T) 8 j) by lia.
  change (2^8) with 256. replace (m + 256 * T) with (m + T * 256) by lia.
  rewrite Z_mod_plus_full, Z.mod_small by lia. reflexivity.
Qed.
Lemma testbit_hi m T j : 0 <= m < 256 -> 0 <= j -> Z.testbit (m + 256 * T) (j + 8) = Z.testbit T j.
Proof.
  intros Hm Hj. rewrite <- (Z.div_pow2_bits (m + 256 * T) 8 j) by lia.
  change (2^8) with 256. f_equal. replace (m + 256 * T) with (T * 256 + m) by lia.
  rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma testbit_small_hi m j : 0 <= m < 256 -> 8 <= j -> Z.testbit m j = false.
Proof.
  intros Hm Hj. destruct (Z.eq_dec m 0) as [->|]. apply Z.bits_0.
  apply Z.bits_above_log2; [lia|]. eapply Z.lt_le_trans with (m := 8); [|lia].
  apply Z.log2_lt_pow2; lia || (change (2^8) with 256; lia).
Qed.

(* [comment removed for export] *)
Lemma bits_eq_split (x y : Z) :
  (forall j, 0 <= j < 8 -> Z.testbit x j = Z.testbit y j) ->
  (forall j, 0 <= j -> Z.testbit x (j + 8) = Z.testbit y (j + 8)) -> x = y.
Proof.
  intros Hl Hh. apply Z.bits_inj'. intros n Hn.
  destruct (Z.lt_ge_cases n 8). apply Hl; lia.
  replace n with ((n - 8) + 8) by lia. apply Hh. lia.
Qed.

Lemma Zdiv_eqn' a b q : 0 < b -> q * b <= a < q * b + b -> a / b = q.
Proof. intros Hb H. symmetry. apply Z.div_unique with (r := a - q * b); lia. Qed.

(* [comment removed for export] *)
Definition cond (b w : Z) : bool :=
  Z.land (Z.lor (Z.lnot ((b - 1 - w) mod 256)) b) 128 =? 128.
Definition borrow (b w : Z) : Z := if b - 1 - w <? 0 then 1 else 0.

Lemma E_cons b r w :
  0 <= b < 256 -> bytes_ok r -> 0 <= w <= 1 ->
  (E (b :: r) w = HIGHS (S (length r))) <->
  (cond b w = true /\ E r (borrow b w) = HIGHS (length r)).
Proof.
  intros Hb Hr Hw. unfold E, cond, borrow. cbn [V length HIGHS ONES].
  set (d := b - 1 - w). set (m := d mod 256).
  pose proof (Z.div_mod d 256 ltac:(lia)) as Ed. pose proof (Z.mod_pos_bound d 256 ltac:(lia)) as Hm.
  fold m in Ed, Hm.
  set (w' := if d <? 0 then 1 else 0).
  assert (Hq : d / 256 = - w').
  { subst w'. destruct (Z.ltb_spec d 0).
    - apply Zdiv_eqn'; lia.
    - apply Zdiv_eqn'; lia. }
  assert (ED : b + 256 * V r - (1 + 256 * ONES (length r)) - w = m + 256 * (V r - ONES (length r) - w')) by lia.
  rewrite ED. set (Dr := V r - ONES (length r) - w').
  pose proof (V_nonneg r Hr) as HV. pose proof (HIGHS_nonneg (length r)) as HH0.
  rewrite Z.eqb_eq.
  split.
  - intros H. split.
    + apply bits_eq_split.
      * intros j Hj. apply (f_equal (fun z => Z.testbit z j)) in H.
        rewrite !Z.land_spec, !Z.lor_spec, !Z.lnot_spec in * by lia.
        rewrite !testbit_lo in H by lia. exact H.
      * intros j Hj. rewrite !Z.land_spec. change 128 with (128 + 256 * 0).
        rewrite testbit_hi, Z.bits_0, andb_false_r by lia. reflexivity.
    + apply Z.bits_inj'. intros j Hj. apply (f_equal (fun z => Z.testbit z (j + 8))) in H.
      rewrite !Z.land_spec, !Z.lor_spec, !Z.lnot_spec in * by lia.
      rewrite !testbit_hi in H by lia. exact H.
  - intros [HL HH]. apply bits_eq_split.
    + intros j Hj. apply (f_equal (fun z => Z.testbit z j)) in HL.
      rewrite !Z.land_spec, !Z.lor_spec, !Z.lnot_spec in * by lia.
      rewrite !testbit_lo by lia. change 128 with (128 + 256 * 0) in HL at 1.
      rewrite testbit_lo in HL by lia. exact HL.
    + intros j Hj. apply (f_equal (fun z => Z.testbit z j)) in HH.
      rewrite !Z.land_spec, !Z.lor_spec, !Z.lnot_spec in * by lia.
      rewrite !testbit_hi by lia. exact HH.
Qed.

(* [comment removed for export] *)
Lemma cond0_table : forallb (fun b => Bool.eqb (cond b 0) (negb (b =? 0)) && (borrow b 0 =? (if b =? 0 then 1 else 0)))
                            (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cond0 b : 0 <= b < 256 -> cond b 0 = negb (b =? 0) /\ (b <> 0 -> borrow b 0 = 0).
Proof.
  intros Hb. pose proof cond0_table as T. rewrite forallb_forall in T.
  specialize (T b). rewrite in_map_iff in T.
  assert (Hin : exists x, Z.of_nat x = b /\ In x (seq 0 256)).
  { exists (Z.to_nat b). split; [lia|]. apply in_seq. lia. }
  specialize (T Hin). apply andb_prop in T. destruct T as [T1 T2].
  apply Bool.eqb_prop in T1. apply Z.eqb_eq in T2. split; [exact T1|].
  intros Hnz. rewrite T2. destruct (Z.eqb_spec b 0); lia.
Qed.

Theorem E_allnz l : bytes_ok l -> (E l 0 = HIGHS (length l) <-> allnz l = true).
Proof.
  induction 1 as [|b r Hb Hr IH]; cbn [allnz length].
  - unfold E. cbn. tauto.
  - rewrite E_cons by (auto; lia). destruct (cond0 b Hb) as [C B].
    rewrite C. destruct (Z.eqb_spec b 0); cbn [negb andb].
    + split; [intros [H _]; discriminate | discriminate].
    + rewrite B by auto. rewrite <- IH. tauto.
Qed.

(* [comment removed for export] *)
Definition ONES8m1 : Z := 0x0101010101010100.
Definition HIGHS8 : Z := 0x8080808080808080.

Lemma land_mod64_HIGHS8 a : Z.land (a mod 2^64) HIGHS8 = Z.land a HIGHS8.
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases n 64).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit HIGHS8 n) with false. { rewrite !andb_false_r. reflexivity. }
    symmetry. apply Z.bits_above_log2; [unfold HIGHS8; lia|].
    eapply Z.lt_le_trans; [|exact H]. vm_compute. reflexivity.
Qed.

Lemma lor_mod64 a b : 0 <= b < 2^64 ->
  Z.land (Z.lor (a mod 2^64) b) HIGHS8 = Z.land (Z.lor a b) HIGHS8.
Proof.
  intros Hb. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.lor_spec.
  destruct (Z.lt_ge_cases n 64).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit HIGHS8 n) with false. { rewrite !andb_false_r. reflexivity. }
    symmetry. apply Z.bits_above_log2; [unfold HIGHS8; lia|].
    eapply Z.lt_le_trans; [|exact H]. vm_compute. reflexivity.
Qed.

Theorem haszero_machine l : bytes_ok l -> length l = 8%nat ->
  (Z.land (Z.lor ((ONES8m1 - V l) mod 2^64) (V l)) HIGHS8 = HIGHS8 <-> allnz l = true).
Proof.
  intros Hl Hlen. pose proof (V_nonneg l Hl). pose proof (V_bound l Hl) as VB. rewrite Hlen in VB.
  change (256 ^ Z.of_nat 8) with (2^64) in VB.
  rewrite lor_mod64 by lia.
  replace (ONES8m1 - V l) with (Z.lnot (V l - ONES 8 - 0)).
  2:{ unfold Z.lnot, ONES8m1. cbn [ONES]. lia. }
  change HIGHS8 with (HIGHS 8). rewrite <- Hlen. apply E_allnz. exact Hl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lxor_byte_range a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lxor a b < 256.
Proof.
  intros Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hn]; [lia|].
  assert (0 < Z.lxor a b) by (pose proof (proj2 (Z.lxor_nonneg a b) ltac:(lia)); lia).
  change 256 with (2 ^ 8). apply Z.log2_lt_pow2; [lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma lxor_split b c R S : 0 <= b < 256 -> 0 <= c < 256 ->
  Z.lxor (b + 256 * R) (c + 256 * S) = Z.lxor b c + 256 * Z.lxor R S.
Proof.
  intros Hb Hc. pose proof (lxor_byte_range b c Hb Hc) as Hx.
  apply bits_eq_split.
  - intros j Hj. rewrite Z.lxor_spec, !testbit_lo by lia. rewrite Z.lxor_spec. reflexivity.
  - intros j Hj. rewrite Z.lxor_spec, !testbit_hi by lia. rewrite Z.lxor_spec. reflexivity.
Qed.

Lemma V_lxor_ones l c : bytes_ok l -> 0 <= c < 256 ->
  Z.lxor (V l) (c * ONES (length l)) = V (map (fun b => Z.lxor b c) l).
Proof.
  intros Hl Hc. induction Hl as [|b r Hb Hr IH]; cbn [V length ONES map].
  - rewrite Z.mul_0_r. reflexivity.
  - replace (c * (1 + 256 * ONES (length r))) with (c + 256 * (c * ONES (length r))) by lia.
    rewrite lxor_split by assumption. rewrite IH. reflexivity.
Qed.

Lemma bytes_ok_lxor l c : bytes_ok l -> 0 <= c < 256 -> bytes_ok (map (fun b => Z.lxor b c) l).
Proof.
  intros Hl Hc. induction Hl as [|b r Hb Hr IH]; cbn [map]; constructor; [|exact IH].
  apply lxor_byte_range; assumption.
Qed.

Lemma allnz_lxor l c : allnz (map (fun b => Z.lxor b c) l) = true -> Forall (fun b => b <> c) l.
Proof.
  induction l as [|b r IH]; cbn [map allnz]; intros H; constructor.
  - apply andb_prop in H as [H _]. apply negb_true_iff, Z.eqb_neq in H.
    intros ->. apply H. apply Z.lxor_nilpotent.
  - apply IH. apply andb_prop in H as [_ H]. exact H.
Qed.

Theorem haszero_machine_xor l c : bytes_ok l -> length l = 8%nat -> 0 <= c < 256 ->
  Z.land (Z.lor ((ONES8m1 - Z.lxor (V l) (c * 0x0101010101010101)) mod 2^64) (Z.lxor (V l) (c * 0x0101010101010101))) HIGHS8 = HIGHS8 ->
  Forall (fun b => b <> c) l.
Proof.
  intros Hl Hlen Hc H. apply allnz_lxor.
  change 0x0101010101010101 with (ONES 8) in H. rewrite <- Hlen in H.
  rewrite V_lxor_ones in H by assumption.
  apply (haszero_machine _ (bytes_ok_lxor l c Hl Hc)); [rewrite length_map; exact Hlen | exact H].
Qed.
