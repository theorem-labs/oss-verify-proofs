(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Btauto.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkXt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).


Lemma forallb_seq_nth : forall (f : nat -> bool) s n i,
  forallb f (seq s n) = true -> (s <= i < s + n)%nat -> f i = true.
Proof.
  intros f s n. revert s. induction n as [|n IH]; intros s i Hf Hi; [lia|].
  cbn [seq forallb] in Hf. apply andb_prop in Hf as [H1 H2].
  destruct (Nat.eq_dec i s) as [->|Hne]; [exact H1|].
  apply (IH (S s)); [exact H2 | lia].
Qed.

Lemma forallb_nth : forall (f : Z -> bool) (l : list Z) d i,
  forallb f l = true -> f d = true -> f (nth i l d) = true.
Proof.
  intros f l d. induction l as [|x l IH]; intros i Hl Hd.
  - destruct i; exact Hd.
  - cbn in Hl. apply andb_prop in Hl as [H1 H2]. destruct i as [|i]; [exact H1 | apply IH; assumption].
Qed.

Ltac xor_ac :=
  cbn [xorb andb orb negb];
  rewrite ?Z.lxor_0_l, ?Z.lxor_0_r, ?Z.lxor_nilpotent;
  first [ reflexivity
        | apply Z.bits_inj'; intros ?n ?Hn; rewrite ?Z.lxor_spec, ?Z.bits_0;
          repeat match goal with |- context [Z.testbit ?x ?m] => generalize (Z.testbit x m); intro end;
          btauto ].

Definition xlin (f : Z -> Z) : Prop := forall a b, f (Z.lxor a b) = Z.lxor (f a) (f b).

Lemma xlin_0 : forall f, xlin f -> f 0 = 0.
Proof.
  intros f Hf. pose proof (Hf 0 0) as H. rewrite Z.lxor_0_l in H.
  rewrite Z.lxor_nilpotent in H. exact H.
Qed.

Lemma pow2_split : forall a n, 0 <= n -> 0 <= a < 2 ^ (n + 1) -> 2 ^ n <= a ->
  a = Z.lxor (a - 2 ^ n) (2 ^ n).
Proof.
  intros a n Hn Ha Hge.
  rewrite <- Z.add_nocarry_lxor.
  - lia.
  - replace (2 ^ n) with (Z.shiftl 1 n) at 2 by (rewrite Z.shiftl_1_l; reflexivity).
    apply land_shiftl_disj; [| lia | lia]. rewrite Z.pow_add_r in Ha by lia. change (2 ^ 1) with 2 in Ha. lia.
Qed.

Lemma xlin_ext : forall f g n, xlin f -> xlin g ->
  (forall j, (j < n)%nat -> f (2 ^ Z.of_nat j) = g (2 ^ Z.of_nat j)) ->
  forall a, 0 <= a < 2 ^ Z.of_nat n -> f a = g a.
Proof.
  intros f g n Hf Hg Hb. induction n as [|n IH]; intros a Ha.
  - assert (a = 0) by (cbn in Ha; lia). subst a. rewrite (xlin_0 f Hf), (xlin_0 g Hg). reflexivity.
  - destruct (Z.lt_ge_cases a (2 ^ Z.of_nat n)) as [Hlt|Hge].
    + apply IH; [intros j Hj; apply Hb; lia | lia].
    + rewrite (pow2_split a (Z.of_nat n)) by (rewrite <- ?Nat2Z.inj_succ; lia).
      rewrite Hf, Hg. f_equal.
      * apply IH; [intros j Hj; apply Hb; lia |].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in Ha by lia. lia.
      * apply Hb. lia.
Qed.


Lemma xt_nonneg : forall c, 0 <= c -> 0 <= xt c.
Proof.
  intros c Hc. unfold xt. apply Z.lxor_nonneg. rewrite Z.shiftr_nonneg.
  destruct (Z.odd c); unfold POLY; lia.
Qed.

Lemma xtn_nonneg : forall n c, 0 <= c -> 0 <= xtn n c.
Proof. induction n as [|n IH]; intros c Hc; [exact Hc | cbn [xtn]; apply IH, xt_nonneg, Hc]. Qed.

Lemma xt_nz : forall c, 0 <= c < 2 ^ 32 -> xt c = 0 -> c = 0.
Proof.
  intros c Hc H. unfold xt in H.
  assert (Hs : 0 <= Z.shiftr c 1 < 2 ^ 31).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. change (2 ^ 31) with 2147483648. lia. }
  destruct (Z.odd c) eqn:Ho.
  - exfalso.
    assert (Ht : Z.testbit (Z.lxor (Z.shiftr c 1) POLY) 31 = true).
    { rewrite Z.lxor_spec. rewrite (testbit_high (Z.shiftr c 1) 31 31) by lia. reflexivity. }
    rewrite H, Z.bits_0 in Ht. discriminate.
  - rewrite Z.lxor_0_r in H. rewrite Z.shiftr_div_pow2 in H by lia. change (2 ^ 1) with 2 in H.
    pose proof (Zmod_odd c) as Hm. rewrite Ho in Hm. lia.
Qed.

Lemma xtn_nz : forall n c, 0 <= c < 2 ^ 32 -> xtn n c = 0 -> c = 0.
Proof.
  induction n as [|n IH]; intros c Hc H; [exact H|].
  cbn [xtn] in H. apply xt_nz; [exact Hc|]. apply (IH (xt c)); [|exact H].
  apply xt_range. exact Hc.
Qed.

Definition xp (e : nat) : Z := xtn e X0.
Definition xpZ (e : Z) : Z := xp (Z.to_nat e).

Lemma X0_range : 0 <= X0 < 2 ^ 32. Proof. unfold X0. lia. Qed.
Lemma xp_range : forall e, 0 <= xp e < 2 ^ 32.
Proof. intros e. unfold xp. apply (xtn_range e X0 X0_range). Qed.
Lemma xp_nz : forall e, xp e <> 0.
Proof. intros e H. pose proof (xtn_nz e X0 X0_range H). unfold X0 in *. lia. Qed.
Lemma xpZ_range : forall e, 0 <= xpZ e < 2 ^ 32. Proof. intros; apply xp_range. Qed.
Lemma xpZ_nz : forall e, xpZ e <> 0. Proof. intros; apply xp_nz. Qed.

Lemma xp_add : forall e j, xtn j (xp e) = xp (e + j).
Proof. intros. unfold xp. rewrite xtn_add. reflexivity. Qed.

Lemma xtn_xlin : forall n, xlin (xtn n).
Proof. intros n a b. apply xtn_xor. Qed.


Lemma mm_loop_0 : forall a b p,
  mm_loop 0 a b p = if Z.testbit a 0 then Z.lxor p b else p.
Proof.
  intros a b p. cbn [mm_loop Z.of_nat]. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
  cbn [Z.eqb andb]. destruct (Z.testbit a 0); reflexivity.
Qed.

Lemma mm_loop_nohit : forall i a b p, Z.testbit a (Z.of_nat (S i)) = false ->
  mm_loop (S i) a b p = mm_loop i a (bstep b) p.
Proof. intros i a b p H. cbn [mm_loop]. rewrite H. reflexivity. Qed.

Lemma mm_loop_hit : forall i a b p, Z.testbit a (Z.of_nat (S i)) = true ->
  a mod 2 ^ Z.of_nat (S i) <> 0 ->
  mm_loop (S i) a b p = mm_loop i a (bstep b) (Z.lxor p b).
Proof.
  intros i a b p H Hm. cbn [mm_loop]. rewrite H. cbn [andb].
  destruct (Z.eqb_spec (a mod 2 ^ Z.of_nat (S i)) 0); [lia | reflexivity].
Qed.

Lemma mm_loop_exit : forall i a b p, Z.testbit a (Z.of_nat i) = true ->
  a mod 2 ^ Z.of_nat i = 0 ->
  mm_loop i a b p = Z.lxor p b.
Proof.
  intros i a b p H Hm. destruct i as [|i]; cbn [mm_loop]; rewrite H, Hm; reflexivity.
Qed.

Definition mm_inv (i : nat) (a : Z) : Prop := a mod 2 ^ (Z.of_nat i + 1) <> 0.

Lemma mm_inv_start : forall a, a mod 2 ^ 32 <> 0 -> mm_inv 31 a.
Proof. intros a H. exact H. Qed.

Lemma testbit_false_mod : forall a i, 0 <= i ->
  Z.testbit a i = false -> a mod 2 ^ (i + 1) = a mod 2 ^ i.
Proof.
  intros a i Hi Hb. apply Z.bits_inj'. intros m Hm.
  destruct (Z.lt_ge_cases m i) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite (Z.mod_pow2_bits_high a i m) by lia.
    destruct (Z.eq_dec m i) as [->|Hne].
    + rewrite Z.mod_pow2_bits_low by lia. exact Hb.
    + rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma mm_inv_nohit : forall i a, mm_inv (S i) a ->
  Z.testbit a (Z.of_nat (S i)) = false -> mm_inv i a.
Proof.
  intros i a H Hb. unfold mm_inv in *.
  replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
  rewrite <- (testbit_false_mod a (Z.of_nat (S i))) by (lia || exact Hb). exact H.
Qed.

Lemma mm_inv_hit : forall i a, a mod 2 ^ Z.of_nat (S i) <> 0 -> mm_inv i a.
Proof. intros i a H. unfold mm_inv. rewrite Nat2Z.inj_succ in H. rewrite Z.add_1_r. exact H. Qed.

Lemma mm_inv_0 : forall a, mm_inv 0 a -> Z.testbit a 0 = true.
Proof.
  intros a H. unfold mm_inv in H. change (2 ^ (Z.of_nat 0 + 1)) with 2 in H.
  rewrite Z.bit0_odd. pose proof (Zmod_odd a) as Hm. destruct (Z.odd a); [reflexivity | lia].
Qed.

Lemma mm_loop_0_inv : forall a b p, mm_inv 0 a -> mm_loop 0 a b p = Z.lxor p b.
Proof. intros a b p H. rewrite mm_loop_0, (mm_inv_0 a H). reflexivity. Qed.

Lemma bstep_range : forall b, 0 <= b < 2 ^ 32 -> 0 <= bstep b < 2 ^ 32.
Proof. intros b Hb. rewrite bstep_xt. apply (xt_range b Hb). Qed.

Lemma mm_loop_range : forall i a b p, 0 <= b < 2 ^ 32 -> 0 <= p < 2 ^ 32 ->
  0 <= mm_loop i a b p < 2 ^ 32.
Proof.
  induction i as [|i IH]; intros a b p Hb Hp.
  - rewrite mm_loop_0. destruct (Z.testbit a 0); [apply (lxor_bound32 p b Hp Hb) | exact Hp].
  - cbn [mm_loop]. destruct (Z.testbit a (Z.of_nat (S i))); cbn [andb].
    + destruct (a mod 2 ^ Z.of_nat (S i) =? 0).
      * apply (lxor_bound32 p b Hp Hb).
      * apply IH; [apply bstep_range, Hb | apply (lxor_bound32 p b Hp Hb)].
    + apply IH; [apply bstep_range, Hb | exact Hp].
Qed.

Lemma multmodp_range : forall a b, 0 <= b < 2 ^ 32 -> 0 <= multmodp a b < 2 ^ 32.
Proof. intros a b Hb. unfold multmodp. apply mm_loop_range; [exact Hb | lia]. Qed.


Fixpoint msum (i : nat) (a b : Z) : Z :=
  Z.lxor (if Z.testbit a (Z.of_nat i) then b else 0)
         (match i with O => 0 | S i' => msum i' a (xt b) end).

Lemma msum_S : forall i a b,
  msum (S i) a b = Z.lxor (if Z.testbit a (Z.of_nat (S i)) then b else 0) (msum i a (xt b)).
Proof. reflexivity. Qed.

Lemma msum_bits_zero : forall i a b,
  (forall j, (j <= i)%nat -> Z.testbit a (Z.of_nat j) = false) -> msum i a b = 0.
Proof.
  induction i as [|i IH]; intros a b H.
  - cbn [msum]. rewrite (H 0%nat) by lia. reflexivity.
  - rewrite msum_S, (H (S i)) by lia. rewrite IH by (intros; apply H; lia). reflexivity.
Qed.

Lemma mod_pow2_zero_bits : forall a i j, 0 <= j < i -> a mod 2 ^ i = 0 -> Z.testbit a j = false.
Proof.
  intros a i j Hj H. rewrite <- (Z.mod_pow2_bits_low a i j) by lia. rewrite H. apply Z.bits_0.
Qed.

Theorem mm_loop_msum : forall i a b p, mm_loop i a b p = Z.lxor p (msum i a b).
Proof.
  induction i as [|i IH]; intros a b p.
  - rewrite mm_loop_0. cbn [msum Z.of_nat]. destruct (Z.testbit a 0); xor_ac.
  - cbn [mm_loop]. rewrite msum_S, bstep_xt.
    destruct (Z.testbit a (Z.of_nat (S i))) eqn:Hb; cbn [andb].
    + destruct (Z.eqb_spec (a mod 2 ^ Z.of_nat (S i)) 0) as [Hm|Hm].
      * rewrite (msum_bits_zero i) by (intros j Hj; apply (mod_pow2_zero_bits a (Z.of_nat (S i))); [lia | exact Hm]).
        xor_ac.
      * rewrite IH. xor_ac.
    + rewrite IH. xor_ac.
Qed.

Corollary multmodp_msum : forall a b, multmodp a b = msum 31 a b.
Proof. intros. unfold multmodp. rewrite mm_loop_msum. apply Z.lxor_0_l. Qed.

Lemma msum_xor_b : forall i a b1 b2,
  msum i a (Z.lxor b1 b2) = Z.lxor (msum i a b1) (msum i a b2).
Proof.
  induction i as [|i IH]; intros a b1 b2.
  - cbn [msum Z.of_nat]. destruct (Z.testbit a 0); xor_ac.
  - rewrite !msum_S, xt_xor, IH. destruct (Z.testbit a (Z.of_nat (S i))); xor_ac.
Qed.

Lemma msum_xor_a : forall i a1 a2 b,
  msum i (Z.lxor a1 a2) b = Z.lxor (msum i a1 b) (msum i a2 b).
Proof.
  induction i as [|i IH]; intros a1 a2 b.
  - cbn [msum Z.of_nat]. rewrite Z.lxor_spec. destruct (Z.testbit a1 0), (Z.testbit a2 0); xor_ac.
  - rewrite !msum_S, IH, Z.lxor_spec.
    destruct (Z.testbit a1 (Z.of_nat (S i))), (Z.testbit a2 (Z.of_nat (S i))); xor_ac.
Qed.

Lemma msum_0_b : forall i a, msum i a 0 = 0.
Proof.
  induction i as [|i IH]; intros a.
  - cbn [msum Z.of_nat]. destruct (Z.testbit a 0); reflexivity.
  - rewrite msum_S, xt_0, IH. destruct (Z.testbit a (Z.of_nat (S i))); reflexivity.
Qed.

Lemma msum_xt : forall i a b, msum i a (xt b) = xt (msum i a b).
Proof.
  induction i as [|i IH]; intros a b.
  - cbn [msum Z.of_nat]. destruct (Z.testbit a 0); rewrite ?Z.lxor_0_r; [reflexivity | symmetry; apply xt_0].
  - rewrite !msum_S. rewrite xt_xor, <- IH. destruct (Z.testbit a (Z.of_nat (S i))); reflexivity.
Qed.

Lemma msum_xtn : forall e i a b, msum i a (xtn e b) = xtn e (msum i a b).
Proof.
  induction e as [|e IH]; intros i a b; [reflexivity|].
  cbn [xtn]. rewrite IH, msum_xt. reflexivity.
Qed.

Lemma msum_xlin_a : forall i b, xlin (fun a => msum i a b).
Proof. intros i b a1 a2. apply msum_xor_a. Qed.
Lemma msum_xlin_b : forall i a, xlin (msum i a).
Proof. intros i a b1 b2. apply msum_xor_b. Qed.

Lemma msum31_X0_basis : forall j, (j < 32)%nat -> msum 31 (2 ^ Z.of_nat j) X0 = 2 ^ Z.of_nat j.
Proof.
  intros j Hj.
  apply Z.eqb_eq.
  apply (forallb_seq_nth (fun j => msum 31 (2 ^ Z.of_nat j) X0 =? 2 ^ Z.of_nat j) 0 32 j); [| lia].
  vm_compute. reflexivity.
Qed.

Lemma pow2_xp : forall j, (j < 32)%nat -> 2 ^ Z.of_nat j = xp (31 - j).
Proof.
  intros j Hj. apply Z.eqb_eq.
  apply (forallb_seq_nth (fun j => 2 ^ Z.of_nat j =? xp (31 - j)) 0 32 j); [| lia].
  vm_compute. reflexivity.
Qed.

Theorem msum31_X0 : forall a, 0 <= a < 2 ^ 32 -> msum 31 a X0 = a.
Proof.
  intros a Ha.
  apply (xlin_ext (fun a => msum 31 a X0) (fun a => a) 32 (msum_xlin_a 31 X0) (fun _ _ => eq_refl)).
  - intros j Hj. apply msum31_X0_basis. exact Hj.
  - exact Ha.
Qed.

Theorem multmodp_xp_xp : forall e j, multmodp (xp e) (xp j) = xp (e + j).
Proof.
  intros e j. rewrite multmodp_msum. unfold xp at 2. rewrite msum_xtn.
  rewrite (msum31_X0 (xp e) (xp_range e)). apply xp_add.
Qed.

Theorem multmodp_xp : forall e b, 0 <= b < 2 ^ 32 -> multmodp (xp e) b = xtn e b.
Proof.
  intros e b Hb. rewrite multmodp_msum.
  apply (xlin_ext (msum 31 (xp e)) (xtn e) 32 (msum_xlin_b 31 (xp e)) (xtn_xlin e)); [|exact Hb].
  intros j Hj. rewrite (pow2_xp j Hj). rewrite <- multmodp_msum, multmodp_xp_xp.
  rewrite xp_add. f_equal. lia.
Qed.

Corollary multmodp_xpZ : forall e b, 0 <= b < 2 ^ 32 -> multmodp (xpZ e) b = xtn (Z.to_nat e) b.
Proof. intros. apply multmodp_xp. assumption. Qed.

Corollary multmodp_xpZ_xpZ : forall e j, 0 <= e -> 0 <= j ->
  multmodp (xpZ e) (xpZ j) = xpZ (e + j).
Proof.
  intros e j He Hj. unfold xpZ. rewrite multmodp_xp_xp. f_equal. lia.
Qed.


Lemma x2n_range : forall k, 0 <= x2n k < 2 ^ 32.
Proof.
  intros k. unfold x2n.
  pose proof (forallb_nth (fun v => (0 <=? v) && (v <? 2 ^ 32)) x2n_table 0 (Z.to_nat k)
                ltac:(vm_compute; reflexivity) eq_refl) as H.
  cbn beta in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma x2n_nz : forall k, 0 <= k < 32 -> x2n k <> 0.
Proof.
  intros k Hk. apply Z.eqb_neq.
  replace k with (Z.of_nat (Z.to_nat k)) by lia.
  apply negb_true_iff.
  apply (forallb_seq_nth (fun j => negb (x2n (Z.of_nat j) =? 0)) 0 32 (Z.to_nat k)); [| lia].
  vm_compute. reflexivity.
Qed.

Lemma x2n_nz_mod : forall k, 0 <= k < 32 -> x2n k mod 2 ^ 32 <> 0.
Proof. intros k Hk. rewrite Z.mod_small by apply x2n_range. apply x2n_nz, Hk. Qed.

Lemma x2n_mod32_nz : forall k, x2n (k mod 32) mod 2 ^ 32 <> 0.
Proof. intros k. apply x2n_nz_mod. apply Z.mod_pos_bound. lia. Qed.

Lemma x2n_0 : x2n 0 = xp 1.
Proof. vm_compute. reflexivity. Qed.

Lemma x2n_sq : forall k, (k < 31)%nat ->
  multmodp (x2n (Z.of_nat k)) (x2n (Z.of_nat k)) = x2n (Z.of_nat (S k)).
Proof.
  intros k Hk. apply Z.eqb_eq.
  apply (forallb_seq_nth (fun k => multmodp (x2n (Z.of_nat k)) (x2n (Z.of_nat k)) =? x2n (Z.of_nat (S k))) 0 31 k); [| lia].
  vm_compute. reflexivity.
Qed.

Theorem x2n_xp : forall k, (k < 32)%nat -> x2n (Z.of_nat k) = xp (2 ^ k).
Proof.
  induction k as [|k IH]; intros Hk.
  - exact x2n_0.
  - rewrite <- x2n_sq by lia. rewrite IH by lia. rewrite multmodp_xp_xp. f_equal.
    rewrite Nat.pow_succ_r'. lia.
Qed.

Corollary x2n_xpZ : forall k, 0 <= k < 32 -> x2n k = xpZ (2 ^ k).
Proof.
  intros k Hk. replace k with (Z.of_nat (Z.to_nat k)) by lia.
  rewrite x2n_xp by lia. unfold xpZ. f_equal. rewrite Z2Nat.inj_pow, Nat2Z.id by lia.
  f_equal.
Qed.


Lemma shiftr1_bound : forall n b, 0 <= n < 2 ^ (b + 1) -> 0 <= b -> 0 <= Z.shiftr n 1 < 2 ^ b.
Proof.
  intros n b Hn Hb. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  rewrite Z.pow_add_r in Hn by lia. change (2 ^ 1) with 2 in Hn.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma x2n_loop_xpZ : forall f (b : nat) n k E,
  0 <= n < 2 ^ Z.of_nat b -> 0 <= k -> k + Z.of_nat b <= 32 -> (b <= f)%nat -> 0 <= E ->
  x2n_loop f n k (xpZ E) = xpZ (E + n * 2 ^ k).
Proof.
  induction f as [|f IH]; intros b n k E Hn Hk Hkb Hbf HE.
  - assert (b = 0%nat) by lia. subst b. cbn in Hn. cbn [x2n_loop]. f_equal. lia.
  - cbn [x2n_loop]. destruct (Z.eqb_spec n 0) as [->|Hn0].
    + f_equal. lia.
    + destruct b as [|b]; [cbn in Hn; lia|].
      rewrite Nat2Z.inj_succ in *.
      assert (Hs : 0 <= Z.shiftr n 1 < 2 ^ Z.of_nat b) by (apply shiftr1_bound; lia).
      rewrite (Z.mod_small k 32) by lia.
      rewrite (x2n_xpZ k) by lia.
      assert (Hodd : n = 2 * Z.shiftr n 1 + (if Z.odd n then 1 else 0)).
      { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
        pose proof (Zmod_odd n) as Hm. destruct (Z.odd n); lia. }
      destruct (Z.odd n).
      * rewrite multmodp_xpZ_xpZ by lia.
        rewrite (IH b) by (lia || nia). f_equal.
        rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. rewrite Hodd at 2. lia.
      * rewrite (IH b) by lia. f_equal.
        rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. rewrite Hodd at 2. lia.
Qed.

Theorem x2nmodp_xpZ : forall n k, 0 <= k <= 32 -> 0 <= n < 2 ^ (32 - k) ->
  x2nmodp n k = xpZ (n * 2 ^ k).
Proof.
  intros n k Hk Hn. unfold x2nmodp.
  change X0 with (xpZ 0).
  rewrite (x2n_loop_xpZ 64 (Z.to_nat (32 - k))); try lia.
  - f_equal.
  - rewrite Z2Nat.id by lia. exact Hn.
Qed.

Corollary x2nmodp_3 : forall n, 0 <= n < 2 ^ 29 -> x2nmodp n 3 = xpZ (8 * n).
Proof.
  intros n Hn. rewrite x2nmodp_xpZ by (lia || (change (2 ^ (32 - 3)) with (2 ^ 29); lia)).
  f_equal. change (2 ^ 3) with 8. lia.
Qed.

Corollary crc32_combine_gen_xpZ : forall n, 0 <= n < 2 ^ 29 -> crc32_combine_gen n = xpZ (8 * n).
Proof.
  (* 1.4: crc32_combine_gen64 is 0 at a negative length *)
  intros n Hn. unfold crc32_combine_gen, crc32_combine_gen64. rewrite (proj2 (Z.ltb_ge n 0)) by lia.
  apply x2nmodp_3. assumption.
Qed.

Corollary x2nmodp_range : forall n k, 0 <= k <= 32 -> 0 <= n < 2 ^ (32 - k) ->
  0 <= x2nmodp n k < 2 ^ 32.
Proof. intros. rewrite x2nmodp_xpZ by assumption. apply xpZ_range. Qed.

Corollary x2nmodp_nz : forall n k, 0 <= k <= 32 -> 0 <= n < 2 ^ (32 - k) ->
  x2nmodp n k <> 0.
Proof. intros. rewrite x2nmodp_xpZ by assumption. apply xpZ_nz. Qed.

Corollary x2nmodp_nz_mod : forall n k, 0 <= k <= 32 -> 0 <= n < 2 ^ (32 - k) ->
  x2nmodp n k mod 2 ^ 32 <> 0.
Proof.
  intros. rewrite Z.mod_small by (apply x2nmodp_range; assumption). apply x2nmodp_nz; assumption.
Qed.

Theorem multmodp_x2nmodp_3 : forall n c, 0 <= n < 2 ^ 29 -> 0 <= c < 2 ^ 32 ->
  multmodp (x2nmodp n 3) c = xtn (Z.to_nat (8 * n)) c.
Proof. intros n c Hn Hc. rewrite x2nmodp_3 by exact Hn. apply multmodp_xpZ. exact Hc. Qed.

Lemma x2n_loop_range : forall f n k p, 0 <= p < 2 ^ 32 -> 0 <= x2n_loop f n k p < 2 ^ 32.
Proof.
  induction f as [|f IH]; intros n k p Hp; cbn [x2n_loop]; [exact Hp|].
  destruct (n =? 0); [exact Hp|]. apply IH. destruct (Z.odd n); [apply multmodp_range|]; exact Hp.
Qed.

Lemma x2nmodp_range_any : forall n k, 0 <= x2nmodp n k < 2 ^ 32.
Proof. intros. unfold x2nmodp. apply x2n_loop_range. unfold X0. lia. Qed.
