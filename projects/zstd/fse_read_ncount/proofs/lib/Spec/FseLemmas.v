(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma pow2_pos n : 0 <= n -> 0 < 2^n.
Proof. intros; apply Z.pow_pos_nonneg; lia. Qed.
Lemma pow2_S a : 0 <= a -> 2^(a+1) = 2 * 2^a.
Proof. intros; rewrite Z.pow_add_r by lia. change (2^1) with 2. lia. Qed.
#[global] Hint Resolve pow2_pos : core.
Lemma mod_pow2_mod_pow2 x m n : 0 <= n <= m -> (x mod 2^m) mod 2^n = x mod 2^n.
Proof.
intros. apply Z.mod_mod_divide.
exists (2^(m-n)). rewrite <- Z.pow_add_r by lia. f_equal; lia.
Qed.
Lemma mod_pow2_div_pow2 x m n : 0 <= n <= m -> (x mod 2^m) / 2^n = (x / 2^n) mod 2^(m-n).
Proof.
intros.
assert (Hm : 2^m = 2^n * 2^(m-n)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Hm. rewrite Z.rem_mul_r by (try apply Z.pow_nonzero; try apply pow2_pos; lia).
rewrite Z.mul_comm. rewrite Z.div_add by (apply Z.pow_nonzero; lia).
rewrite Z.div_small by (apply Z.mod_pos_bound; apply pow2_pos; lia). lia.
Qed.
Lemma div_pow2_div_pow2 x a b : 0 <= a -> 0 <= b -> x / 2^a / 2^b = x / 2^(a+b).
Proof.
intros. rewrite Z.div_div by (try apply pow2_pos; try apply Z.lt_le_incl, pow2_pos; lia).
rewrite <- Z.pow_add_r by lia. reflexivity.
Qed.
Lemma mod_add_mul_pow2 a b n : 0 <= n -> (a + b * 2^n) mod 2^n = a mod 2^n.
Proof. intros. apply Z.mod_add. apply Z.pow_nonzero; lia. Qed.
Lemma div_add_mul_pow2 a b n : 0 <= n -> (a + b * 2^n) / 2^n = a / 2^n + b.
Proof. intros. apply Z.div_add. apply Z.pow_nonzero; lia. Qed.
Lemma mod_add_mul_pow2_le a b n m : 0 <= n <= m -> (a + b * 2^m) mod 2^n = a mod 2^n.
Proof.
intros. replace (b * 2^m) with ((b * 2^(m-n)) * 2^n).
apply mod_add_mul_pow2; lia.
rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal; f_equal; lia.
Qed.
Lemma div_mod_split x n : 0 <= n -> x = x mod 2^n + 2^n * (x / 2^n).
Proof. intros. pose proof (Z.div_mod x (2^n) ltac:(apply Z.pow_nonzero; lia)). lia. Qed.
Lemma mod_pow2_range x n : 0 <= n -> 0 <= x mod 2^n < 2^n.
Proof. intros; apply Z.mod_pos_bound; apply pow2_pos; lia. Qed.
Lemma low_bits_append a v T : 0 <= T -> 0 <= a < 2^T -> (a + v * 2^T) mod 2^T = a.
Proof. intros. rewrite mod_add_mul_pow2 by lia. apply Z.mod_small; lia. Qed.
Lemma high_bits_append a v T : 0 <= T -> 0 <= a < 2^T -> (a + v * 2^T) / 2^T = v.
Proof. intros. rewrite div_add_mul_pow2 by lia. rewrite Z.div_small; lia. Qed.
Lemma append_bound a v T w :
0 <= T -> 0 <= w -> 0 <= a < 2^T -> 0 <= v < 2^w -> 0 <= a + v * 2^T < 2^(T+w).
Proof.
intros. rewrite Z.pow_add_r by lia.
assert (0 < 2^T) by (apply pow2_pos; lia). nia.
Qed.
Definition bits (x p w : Z) : Z := (x / 2^p) mod 2^w.
Lemma bits_mod x m p w : 0 <= p -> 0 <= w -> p + w <= m -> bits (x mod 2^m) p w = bits x p w.
Proof.
intros. unfold bits. rewrite mod_pow2_div_pow2 by lia.
apply mod_pow2_mod_pow2. lia.
Qed.
Lemma bits_shift x a p w : 0 <= a -> 0 <= p -> bits (x / 2^a) p w = bits x (a + p) w.
Proof. intros. unfold bits. rewrite div_pow2_div_pow2 by lia. reflexivity. Qed.
Lemma bits_append_lo a v T p w :
0 <= p -> 0 <= w -> p + w <= T -> 0 <= a < 2^T -> bits (a + v * 2^T) p w = bits a p w.
Proof.
intros. rewrite <- (bits_mod (a + v * 2^T) T) by lia.
rewrite low_bits_append by lia. reflexivity.
Qed.
Lemma bits_append_hi a v T p w :
0 <= T <= p -> 0 <= w -> 0 <= a < 2^T -> bits (a + v * 2^T) p w = bits v (p - T) w.
Proof.
intros. unfold bits. replace (2^p) with (2^T * 2^(p-T)).
2:{ rewrite <- Z.pow_add_r by lia. f_equal; lia. }
rewrite <- Z.div_div by (try apply pow2_pos; try apply Z.lt_le_incl, pow2_pos; lia).
rewrite high_bits_append by lia. reflexivity.
Qed.
Lemma bits_0_w v w : 0 <= w -> 0 <= v < 2^w -> bits v 0 w = v.
Proof. intros. unfold bits. change (2^0) with 1. rewrite Z.div_1_r. apply Z.mod_small; lia. Qed.
Lemma u32_id x : 0 <= x < 2^32 -> u32 x = x.
Proof. intros; unfold u32; apply Z.mod_small; lia. Qed.
Lemma u32_range x : 0 <= u32 x < 2^32.
Proof. unfold u32. apply Z.mod_pos_bound. reflexivity. Qed.
Lemma land_ones_mod x n : 0 <= n -> Z.land x (2^n - 1) = x mod 2^n.
Proof.
intros. replace (2^n - 1) with (Z.ones n). apply Z.land_ones; lia.
unfold Z.ones. rewrite Z.shiftl_1_l. lia.
Qed.
Lemma land_7 x : Z.land x 7 = x mod 8.
Proof. change 7 with (2^3 - 1). rewrite land_ones_mod by lia. reflexivity. Qed.
Lemma land_31 x : Z.land x 31 = x mod 32.
Proof. change 31 with (2^5 - 1). rewrite land_ones_mod by lia. reflexivity. Qed.
Lemma land_15 x : Z.land x 15 = x mod 16.
Proof. change 15 with (2^4 - 1). rewrite land_ones_mod by lia. reflexivity. Qed.
Lemma land_3 x : Z.land x 3 = x mod 4.
Proof. change 3 with (2^2 - 1). rewrite land_ones_mod by lia. reflexivity. Qed.
Lemma shiftr_3 x : Z.shiftr x 3 = x / 8.
Proof. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shl32_ok x n : 0 <= n < 32 -> shl32 x n = Ok (u32 (x * 2^n)).
Proof. intros. unfold shl32. destruct (Z.leb_spec 0 n), (Z.ltb_spec n 32); simpl; try lia; auto. Qed.
Lemma shr32_ok x n : 0 <= n < 32 -> shr32 x n = Ok (x / 2^n).
Proof. intros. unfold shr32. destruct (Z.leb_spec 0 n), (Z.ltb_spec n 32); simpl; try lia; auto. Qed.
Lemma odd_mod2 x : Z.odd x = (x mod 2 =? 1).
Proof.
rewrite Zmod_odd. destruct (Z.odd x); reflexivity.
Qed.
Lemma mod2_of_mod_pow2 x k : 1 <= k -> x mod 2 = (x mod 2^k) mod 2.
Proof.
intros. symmetry. apply Z.mod_mod_divide. exists (2^(k-1)).
rewrite <- (Z.pow_1_r 2) at 3. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.
Lemma div2_of_mod_pow2 x k : 1 <= k -> (Z.div2 x) mod 2^(k-1) = (x mod 2^k) / 2.
Proof.
intros. rewrite Z.div2_div.
replace (2^k) with (2 * 2^(k-1)).
2:{ rewrite <- (Z.pow_1_r 2) at 1. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
rewrite Z.rem_mul_r by (try apply pow2_pos; lia).
pose proof (Z.mod_pos_bound x 2 ltac:(lia)).
set (q := (x/2) mod 2^(k-1)).
replace (x mod 2 + 2 * q) with (q * 2 + x mod 2) by lia.
rewrite Z.div_add_l by lia. rewrite (Z.div_small (x mod 2) 2) by lia. lia.
Qed.
Lemma ctz_aux_exact : forall (j : nat) f x,
(j < f)%nat -> x mod 2^(Z.of_nat j + 1) = 2^(Z.of_nat j) -> ctz_aux f x = Z.of_nat j.
Proof.
induction j as [|j IH]; intros f x Hf Hx.
- destruct f; [lia|]. cbn [ctz_aux].
rewrite odd_mod2, (mod2_of_mod_pow2 x (Z.of_nat 0 + 1)), Hx by lia. reflexivity.
- destruct f; [lia|]. cbn [ctz_aux].
rewrite odd_mod2, (mod2_of_mod_pow2 x (Z.of_nat (S j) + 1)), Hx by lia.
rewrite Nat2Z.inj_succ. rewrite <- Z.add_1_l, Z.pow_add_r, Z.pow_1_r by lia.
rewrite Z.mul_comm, Z_mod_mult. cbn [Z.eqb].
rewrite (IH f (Z.div2 x)); [lia|lia|].
replace (Z.of_nat j + 1) with ((Z.of_nat (S j) + 1) - 1) by lia.
rewrite div2_of_mod_pow2, Hx by lia.
rewrite Nat2Z.inj_succ. rewrite <- Z.add_1_l, Z.pow_add_r, Z.pow_1_r by lia.
rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma ctz_aux_le : forall f x, 0 <= ctz_aux f x <= Z.of_nat f.
Proof.
induction f; intros; cbn [ctz_aux]; [lia|]. rewrite Nat2Z.inj_succ. destruct (Z.odd x); [lia|]. specialize (IHf (Z.div2 x)). lia.
Qed.
Lemma ctz_aux_lower : forall (j : nat) f x,
(j <= f)%nat -> x mod 2^(Z.of_nat j) = 0 -> Z.of_nat j <= ctz_aux f x.
Proof.
induction j as [|j IH]; intros f x Hf Hx.
- pose proof (ctz_aux_le f x). lia.
- destruct f; [lia|]. cbn [ctz_aux].
rewrite odd_mod2, (mod2_of_mod_pow2 x (Z.of_nat (S j))), Hx by lia. simpl (0 mod 2 =? 1).
assert (Z.of_nat j <= ctz_aux f (Z.div2 x)). 2:{ rewrite Nat2Z.inj_succ; lia. }
apply IH; [lia|].
replace (Z.of_nat j) with (Z.of_nat (S j) - 1) at 1 by lia.
rewrite div2_of_mod_pow2, Hx by lia. reflexivity.
Qed.
Lemma upd_nat_length n v l : length (upd_nat n v l) = length l.
Proof. revert n; induction l; intros [|n]; simpl; auto. Qed.
Lemma Zupd_length i v l : length (Zupd i v l) = length l.
Proof. apply upd_nat_length. Qed.
Lemma nth_upd_nat_same n v l : (n < length l)%nat -> nth n (upd_nat n v l) 0 = v.
Proof. revert n; induction l; intros [|n] H; simpl in *; try lia; auto. apply IHl; lia. Qed.
Lemma nth_upd_nat_other n m v l : n <> m -> nth m (upd_nat n v l) 0 = nth m l 0.
Proof. revert n m; induction l; intros [|n] [|m] H; simpl in *; auto; try lia. Qed.
Lemma Znth_Zupd_same i v l : 0 <= i < Zlength l -> Znth i (Zupd i v l) = v.
Proof. intros. unfold Znth, Zupd. apply nth_upd_nat_same. unfold Zlength in H. lia. Qed.
Lemma Znth_Zupd_other i j v l : 0 <= i -> 0 <= j -> i <> j -> Znth j (Zupd i v l) = Znth j l.
Proof. intros. unfold Znth, Zupd. apply nth_upd_nat_other. lia. Qed.
Lemma zload_ok l i : 0 <= i < Zlength l -> load l i = Ok (Znth i l).
Proof. intros. unfold load. destruct (Z.leb_spec 0 i), (Z.ltb_spec i (Zlength l)); simpl; auto; lia. Qed.
Lemma zstore_ok l i v : 0 <= i < Zlength l -> store l i v = Ok (Zupd i v l).
Proof. intros. unfold store. destruct (Z.leb_spec 0 i), (Z.ltb_spec i (Zlength l)); simpl; auto; lia. Qed.
Fixpoint bytes_val (l : list Z) : Z :=
match l with [] => 0 | b :: t => b + 256 * bytes_val t end.
Definition all_bytes (l : list Z) : Prop := forall i, 0 <= Znth i l < 256.
Lemma all_bytes_cons_inv b l : all_bytes (b :: l) -> 0 <= b < 256 /\ all_bytes l.
Proof.
intros H. split. { specialize (H 0). exact H. }
intros i. destruct (Z_lt_le_dec i 0).
{ unfold Znth. replace (Z.to_nat i) with 0%nat by lia. specialize (H 1). unfold Znth in H. simpl in H.
destruct l; simpl in *; lia. }
specialize (H (i+1)). unfold Znth in *. replace (Z.to_nat (i+1)) with (S (Z.to_nat i)) in H by lia. exact H.
Qed.
Lemma Forall_all_bytes l : Forall (fun b => 0 <= b < 256) l -> all_bytes l.
Proof.
intros H i. unfold Znth. revert l H. generalize (Z.to_nat i) as n. clear i.
induction n; intros [|b l] H; simpl; try lia; inversion H; subst; auto.
Qed.
Lemma all_bytes_Forall l : all_bytes l -> Forall (fun b => 0 <= b < 256) l.
Proof.
induction l; intros H; constructor.
- apply (all_bytes_cons_inv _ _ H).
- apply IHl. apply (all_bytes_cons_inv _ _ H).
Qed.
Lemma bytes_val_range l : all_bytes l -> 0 <= bytes_val l < 2^(8 * Zlength l).
Proof.
induction l; intros H; cbn [bytes_val]. { unfold Zlength; cbn [length Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r. lia. }
apply all_bytes_cons_inv in H. destruct H as [Ha Hl]. specialize (IHl Hl).
unfold Zlength in *. cbn [length].
replace (8 * Z.of_nat (S (length l))) with (8 + 8 * Z.of_nat (length l)) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256. lia.
Qed.
Lemma bytes_val_app l1 l2 : bytes_val (l1 ++ l2) = bytes_val l1 + 2^(8 * Zlength l1) * bytes_val l2.
Proof.
induction l1; cbn [bytes_val app].
- unfold Zlength; cbn [length Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r. lia.
- rewrite IHl1. unfold Zlength. cbn [length].
replace (8 * Z.of_nat (S (length l1))) with (8 + 8 * Z.of_nat (length l1)) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256. lia.
Qed.
Lemma nth_bytes_val l n : all_bytes l -> nth n l 0 = (bytes_val l / 2^(8*Z.of_nat n)) mod 256.
Proof.
revert l. induction n; intros l Hb.
- cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
destruct l as [|b l]; cbn [nth bytes_val]; [reflexivity|]. apply all_bytes_cons_inv in Hb.
replace (b + 256 * bytes_val l) with (b + bytes_val l * 256) by lia.
rewrite Z.mod_add by lia. symmetry; apply Z.mod_small; lia.
- destruct l as [|b l]; cbn [nth].
+ cbn [bytes_val]. rewrite Z.div_0_l; [reflexivity|]. apply Z.pow_nonzero; lia.
+ apply all_bytes_cons_inv in Hb. destruct Hb as [H1 H2]. rewrite (IHn l H2).
cbn [bytes_val]. f_equal.
replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia.
rewrite Z.pow_add_r by lia. change (2^8) with 256.
rewrite <- Z.div_div by (try apply pow2_pos; lia).
f_equal. replace (b + 256 * bytes_val l) with (b + bytes_val l * 256) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma Znth_bytes_val l i : all_bytes l -> 0 <= i -> Znth i l = (bytes_val l / 2^(8*i)) mod 256.
Proof.
intros Hb Hi. unfold Znth. rewrite nth_bytes_val by auto. rewrite Z2Nat.id by lia. reflexivity.
Qed.
Lemma bytes_val_firstn l n : all_bytes l -> (n <= length l)%nat ->
bytes_val (firstn n l) = bytes_val l mod 2^(8 * Z.of_nat n).
Proof.
intros Hb Hn.
rewrite <- (firstn_skipn n l) at 2. rewrite bytes_val_app.
unfold Zlength. rewrite firstn_length_le by lia.
rewrite Z.mul_comm, mod_add_mul_pow2 by lia. symmetry. apply Z.mod_small.
pose proof (bytes_val_range (firstn n l)) as R.
unfold Zlength in R. rewrite firstn_length_le in R by lia. apply R.
apply Forall_all_bytes. apply all_bytes_Forall in Hb.
rewrite <- (firstn_skipn n l) in Hb. apply Forall_app in Hb. tauto.
Qed.
Lemma split32 y : 0 <= y < 2^32 ->
y = y mod 2^8 + 2^8 * ((y / 2^8) mod 2^8) + 2^16 * ((y / 2^16) mod 2^8) + 2^24 * (y / 2^24).
Proof.
intros.
assert (E1 := div_mod_split y 8 ltac:(lia)).
assert (E2 := div_mod_split (y / 2^8) 8 ltac:(lia)).
assert (E3 := div_mod_split (y / 2^16) 8 ltac:(lia)).
rewrite (div_pow2_div_pow2 y 8 8) in E2 by lia.
rewrite (div_pow2_div_pow2 y 16 8) in E3 by lia.
change (8+8) with 16 in E2. change (16+8) with 24 in E3.
change (2^8) with 256 in *. change (2^16) with 65536 in *. change (2^24) with 16777216 in *. lia.
Qed.
Lemma bits32_decomp x :
(x mod 2^32) = x mod 2^8 + 2^8 * ((x / 2^8) mod 2^8) + 2^16 * ((x / 2^16) mod 2^8) + 2^24 * ((x / 2^24) mod 2^8).
Proof.
pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)) as R.
rewrite (split32 (x mod 2^32)) at 1 by lia.
rewrite !mod_pow2_div_pow2 by lia. rewrite !mod_pow2_mod_pow2 by lia.
change (32-24) with 8. reflexivity.
Qed.
Lemma readLE32_val buf ip : all_bytes buf -> 0 <= ip -> ip + 4 <= Zlength buf ->
readLE32 buf ip = Ok ((bytes_val buf / 2^(8*ip)) mod 2^32).
Proof.
intros Hb H0 H4. unfold readLE32.
destruct (Z.leb_spec 0 ip); [|lia]. destruct (Z.leb_spec (ip+4) (Zlength buf)); [|lia].
cbn [andb]. f_equal.
rewrite !Znth_bytes_val by (auto; lia).
set (B := bytes_val buf).
replace (8 * (ip+1)) with (8*ip + 8) by lia.
replace (8 * (ip+2)) with (8*ip + 16) by lia.
replace (8 * (ip+3)) with (8*ip + 24) by lia.
rewrite <- !(div_pow2_div_pow2 B (8*ip)) by lia.
set (x := B / 2^(8*ip)). rewrite bits32_decomp. change 256 with (2^8). lia.
Qed.
Lemma lor_bit31 a : 0 <= a < 2^32 -> Z.lor a (2^31) = a mod 2^31 + 2^31.
Proof.
intros Ha.
assert (E : Z.lor a (2^31) = Z.lor (a mod 2^31) (2^31)).
{ apply Z.bits_inj'. intros n Hn. rewrite !Z.lor_spec.
rewrite Z.testbit_mod_pow2 by lia. rewrite Z.pow2_bits_eqb by lia.
destruct (Z.ltb_spec n 31); destruct (Z.eqb_spec 31 n); simpl; try lia; rewrite ?orb_true_r, ?orb_false_r; auto.
rewrite Z.bits_above_log2; auto; try lia.
destruct (Z.eq_dec a 0). { subst; simpl. lia. }
apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (2^32); [lia|]. apply Z.pow_le_mono_r; lia. }
rewrite E. rewrite <- Z.lxor_lor.
- symmetry. apply Z.add_nocarry_lxor.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.testbit_mod_pow2, Z.pow2_bits_eqb, Z.bits_0 by lia.
destruct (Z.ltb_spec n 31); destruct (Z.eqb_spec 31 n); simpl; try lia; rewrite ?andb_true_r, ?andb_false_r; auto.
- apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.testbit_mod_pow2, Z.pow2_bits_eqb, Z.bits_0 by lia.
destruct (Z.ltb_spec n 31); destruct (Z.eqb_spec 31 n); simpl; try lia; rewrite ?andb_true_r, ?andb_false_r; auto.
Qed.
Lemma not32_mod x n : 0 <= n <= 32 -> (not32 x) mod 2^n = 2^n - 1 - x mod 2^n.
Proof.
intros. unfold not32.
pose proof (mod_pow2_range x n ltac:(lia)).
replace (2^32 - 1 - x) with ((2^n - 1 - x mod 2^n) + (2^(32-n) - 1 - x / 2^n) * 2^n).
- rewrite mod_add_mul_pow2 by lia. apply Z.mod_small. lia.
- rewrite (div_mod_split x n) at 3 by lia.
replace (2^32) with (2^n * 2^(32-n)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). nia.
Qed.
Lemma repeats_arg_mod x n : 0 <= x < 2^32 -> 0 <= n <= 31 ->
(Z.lor (not32 x) (2^31)) mod 2^n = 2^n - 1 - x mod 2^n
/\ 0 < Z.lor (not32 x) (2^31) < 2^32.
Proof.
intros. assert (Hn : 0 <= not32 x < 2^32) by (unfold not32; lia).
rewrite lor_bit31 by lia. split.
- replace (2^31) with (2^(31-n) * 2^n) at 2 by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite mod_add_mul_pow2 by lia. rewrite mod_pow2_mod_pow2 by lia. apply not32_mod. lia.
- pose proof (mod_pow2_range (not32 x) 31 ltac:(lia)).
change (2^32) with (2^31 + 2^31). lia.
Qed.
Lemma repeats_of_exact x m r :
0 <= x < 2^32 -> 0 <= m <= 11 -> 0 <= r <= 2 ->
x mod 2^(2*m+2) = (2^(2*m) - 1) + r * 2^(2*m) ->
repeats_of x = Ok m.
Proof.
intros Hx Hm Hr Hmod. unfold repeats_of, ctz32.
destruct (repeats_arg_mod x (2*m+2) Hx ltac:(lia)) as [Hlow Hrange].
set (a := Z.lor (not32 x) (2^31)) in *.
rewrite u32_id by lia. destruct (Z.eqb_spec a 0); [lia|]. cbn [bind].
rewrite Hmod in Hlow.
assert (Hlow' : a mod 2^(2*m+2) = (3 - r) * 2^(2*m)).
{ rewrite Hlow. replace (2*m+2) with (2*m + 2) by lia. rewrite (Z.pow_add_r 2 (2*m) 2) by lia. change (2^2) with 4. lia. }
clear Hlow.
assert (P2m : 0 < 2^(2*m)) by (apply pow2_pos; lia).
assert (P2m1 : 2^(2*m+1) = 2 * 2^(2*m)) by (rewrite Z.pow_add_r by lia; change (2^1) with 2; lia).
assert (P2m2 : 2^(2*m+2) = 4 * 2^(2*m)) by (rewrite Z.pow_add_r by lia; change (2^2) with 4; lia).
destruct (Z.eq_dec r 1).
-
subst r. rewrite (ctz_aux_exact (Z.to_nat (2*m+1))).
+ f_equal. rewrite Z2Nat.id by lia. replace (2*m+1) with (1 + m*2) by lia. rewrite Z.div_add by lia. reflexivity.
+ lia.
+ rewrite Z2Nat.id by lia. replace (2*m+1+1) with (2*m+2) by lia. rewrite Hlow'. lia.
-
rewrite (ctz_aux_exact (Z.to_nat (2*m))).
+ f_equal. rewrite Z2Nat.id by lia. replace (2*m) with (m*2) by lia. rewrite Z.div_mul by lia. reflexivity.
+ lia.
+ rewrite Z2Nat.id by lia.
rewrite <- (mod_pow2_mod_pow2 a (2*m+2) (2*m+1)) by lia. rewrite Hlow'.
assert (r = 0 \/ r = 2) as [-> | ->] by lia.
* replace ((3 - 0) * 2^(2*m)) with (2^(2*m) + 1 * 2^(2*m+1)) by lia.
rewrite mod_add_mul_pow2 by lia. apply Z.mod_small. lia.
* replace ((3 - 2) * 2^(2*m)) with (2^(2*m)) by lia. apply Z.mod_small. lia.
Qed.
Lemma repeats_of_ge12 x :
0 <= x < 2^32 -> x mod 2^24 = 2^24 - 1 ->
exists q, repeats_of x = Ok q /\ 12 <= q <= 16.
Proof.
intros Hx Hmod. unfold repeats_of, ctz32.
destruct (repeats_arg_mod x 24 Hx ltac:(lia)) as [Hlow Hrange].
set (a := Z.lor (not32 x) (2^31)) in *.
rewrite u32_id by lia. destruct (Z.eqb_spec a 0); [lia|]. cbn [bind].
eexists; split; [reflexivity|].
pose proof (ctz_aux_lower 24%nat 32%nat a ltac:(lia)) as L.
pose proof (ctz_aux_le 32%nat a) as U.
assert (a mod 2^24 = 0) by (change (Z.of_nat 24) with 24 in L; lia).
specialize (L H). change (Z.of_nat 24) with 24 in L. change (Z.of_nat 32) with 32 in U.
split. { apply Z.div_le_lower_bound; lia. } { apply Z.div_le_upper_bound; lia. }
Qed.
