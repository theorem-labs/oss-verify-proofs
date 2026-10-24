(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition POLY : Z := 0xedb88320.

Definition cstep (b : Z) : Z := Z.lxor (Z.shiftr b 1) (if Z.odd b then POLY else 0).

(* [comment removed for export] *)
Fixpoint mm_loop (f : nat) (m a b p : Z) : Z :=
  match f with
  | O => p
  | S f' =>
      if Z.land m a =? 0 then mm_loop f' (Z.shiftr m 1) a (cstep b) p
      else if Z.land (m - 1) a =? 0 then Z.lxor p b
      else mm_loop f' (Z.shiftr m 1) a (cstep b) (Z.lxor p b)
  end.

(* [comment removed for export] *)
Abbreviation mm a b := (mm_loop 32 (2 ^ Z.of_nat 31) a b 0) (only parsing).

Definition x2n_tab : list Z :=
  [0x40000000; 0x20000000; 0x08000000; 0x00800000; 0x00008000; 0xedb88320; 0xb1e6b092; 0xa06a2517;
   0xed627dae; 0x88d14467; 0xd7bbfe6a; 0xec447f11; 0x8e7ea170; 0x6427800e; 0x4d47bae0; 0x09fe548f;
   0x83852d0f; 0x30362f1a; 0x7b5a9cc3; 0x31fec169; 0x9fec022a; 0x6c8dedc4; 0x15d6874d; 0x5fde7a4e;
   0xbad90e37; 0x2e4e5eef; 0x4eaba214; 0xa8a472c0; 0x429a969e; 0x148d302a; 0xc40ba6d0; 0xc4e22c3c].

(* [comment removed for export] *)
Definition x2n_inv : list Z :=
  [0xdb710641; 0x6d930ac3; 0x6d3d2d4d; 0x6567cb95; 0xd7125358; 0x5b358fd3; 0x2e9bb40b; 0x12a59a49;
   0x8df9403d; 0x5139de12; 0xba340226; 0x29c45641; 0x12fbc105; 0xecd30c55; 0x3755ebd8; 0x24ee460c;
   0x23783fcf; 0x479933fc; 0xa39442a5; 0x9ea0056d; 0xf42608f6; 0x20cacf04; 0x2a0cf83d; 0xeffd8645;
   0x2a39a67d; 0x640ebd82; 0x9dfd8792; 0x277402ab; 0xad31bc4f; 0x31536354; 0x5ea35fca; 0x52b55e39].

Definition tabz (i : nat) : Z := nth i x2n_tab 0.
Definition invz (i : nat) : Z := nth i x2n_inv 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma testbit_small : forall a k n, 0 <= a < 2^k -> 0 <= k <= n -> Z.testbit a n = false.
Proof.
  intros a k n Ha Hk. rewrite <- (Z.mod_small a (2^k)) by lia.
  apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma lxor_bound : forall k a b, 0 <= k -> 0 <= a < 2^k -> 0 <= b < 2^k -> 0 <= Z.lxor a b < 2^k.
Proof.
  intros k a b Hk Ha Hb.
  assert (H0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; [exact H0|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NZ]; [lia|].
  destruct (Z.eq_dec k 0) as [->|Kp].
  { exfalso. cbn in Ha, Hb. apply NZ. replace a with 0 by lia. replace b with 0 by lia. reflexivity. }
  apply Z.log2_lt_pow2; [lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma land_bound_l : forall k a b, 0 <= a < 2^k -> 0 <= b -> 0 <= Z.land a b < 2^k.
Proof.
  intros k a b Ha Hb.
  assert (H0 : 0 <= Z.land a b) by (apply Z.land_nonneg; lia).
  split; [exact H0|].
  destruct (Z.eq_dec (Z.land a b) 0) as [->|NZ]; [lia|].
  assert (Hk : 0 <= k). { destruct (Z.lt_ge_cases k 0); [|lia]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  destruct (Z.eq_dec k 0) as [->|Kp].
  { exfalso. cbn in Ha. apply NZ. replace a with 0 by lia. apply Z.land_0_l. }
  apply Z.log2_lt_pow2; [lia|].
  eapply Z.le_lt_trans; [apply Z.log2_land; lia|].
  destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|].
  eapply Z.le_lt_trans; [apply Z.le_min_l|]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma shiftr1_bound : forall k b, 0 <= b < 2^(k+1) -> 0 <= k -> 0 <= Z.shiftr b 1 < 2^k.
Proof.
  intros k b Hb Hk. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.pow_add_r in Hb by lia. change (2^1) with 2 in *.
  set (t := 2^k) in *. clearbody t. Z.div_mod_to_equations. lia.
Qed.

Lemma POLY_range : 2^31 <= POLY < 2^32.
Proof. unfold POLY. lia. Qed.

Lemma cstep_range : forall b, 0 <= b < 2^32 -> 0 <= cstep b < 2^32.
Proof.
  intros b Hb. unfold cstep.
  pose proof (shiftr1_bound 31 b ltac:(change (31+1) with 32; lia) ltac:(lia)).
  destruct (Z.odd b); apply lxor_bound; try lia. pose proof POLY_range. lia.
Qed.

Lemma odd_lxor : forall a b, Z.odd (Z.lxor a b) = xorb (Z.odd a) (Z.odd b).
Proof. intros. rewrite <- !Z.bit0_odd. apply Z.lxor_spec. Qed.

Lemma lxor4 : forall a b c d, Z.lxor (Z.lxor a b) (Z.lxor c d) = Z.lxor (Z.lxor a c) (Z.lxor b d).
Proof. intros. rewrite !Z.lxor_assoc. f_equal. rewrite <- !Z.lxor_assoc. f_equal. apply Z.lxor_comm. Qed.

Lemma cstep_lxor : forall a b, cstep (Z.lxor a b) = Z.lxor (cstep a) (cstep b).
Proof.
  intros a b. unfold cstep. rewrite Z.shiftr_lxor, odd_lxor.
  destruct (Z.odd a), (Z.odd b); cbn [xorb]; rewrite lxor4; f_equal.
Qed.

Lemma cstep_0 : cstep 0 = 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mm_loop_lxor : forall f m a b1 b2 p1 p2,
  mm_loop f m a (Z.lxor b1 b2) (Z.lxor p1 p2) = Z.lxor (mm_loop f m a b1 p1) (mm_loop f m a b2 p2).
Proof.
  induction f as [|f IH]; intros; cbn [mm_loop]; [reflexivity|].
  destruct (Z.land m a =? 0).
  - rewrite cstep_lxor. apply IH.
  - pose proof (lxor4 p1 p2 b1 b2) as E.
    destruct (Z.land (m - 1) a =? 0).
    + exact E.
    + rewrite cstep_lxor, E. apply IH.
Qed.

Lemma mm_lxor : forall a p q, mm a (Z.lxor p q) = Z.lxor (mm a p) (mm a q).
Proof. intros. rewrite <- mm_loop_lxor. f_equal. Qed.

Lemma mm_loop_range : forall f m a b p, 0 <= b < 2^32 -> 0 <= p < 2^32 -> 0 <= mm_loop f m a b p < 2^32.
Proof.
  induction f as [|f IH]; intros; cbn [mm_loop]; [lia|].
  pose proof (cstep_range b H).
  destruct (Z.land m a =? 0); [apply IH; lia|].
  pose proof (lxor_bound 32 p b ltac:(lia) H0 H).
  destruct (Z.land (m - 1) a =? 0); [lia|]. apply IH; lia.
Qed.

Lemma mm_range : forall a b, 0 <= b < 2^32 -> 0 <= mm a b < 2^32.
Proof. intros. apply mm_loop_range; lia. Qed.

Lemma mm_loop_b0 : forall f m a, mm_loop f m a 0 0 = 0.
Proof.
  induction f as [|f IH]; intros; cbn [mm_loop]; [reflexivity|].
  rewrite cstep_0. destruct (Z.land m a =? 0); [apply IH|]. cbn. destruct (Z.land (m - 1) a =? 0); [reflexivity|apply IH].
Qed.

Lemma mm_0 : forall a, mm a 0 = 0.
Proof. intros. apply mm_loop_b0. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition inv_checkb : bool :=
  forallb (fun i => forallb (fun j => mm (invz i) (mm (tabz i) (2 ^ Z.of_nat j)) =? 2 ^ Z.of_nat j) (seq 0 32)) (seq 0 32).

(* [comment removed for export] *)

Lemma inv_checkb_unf :
  forallb (fun i => forallb (fun j => mm (invz i) (mm (tabz i) (2 ^ Z.of_nat j)) =? 2 ^ Z.of_nat j) (seq 0 32)) (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma forallb_seq : forall (g : nat -> bool) s n i, forallb g (seq s n) = true -> (s <= i < s + n)%nat -> g i = true.
Proof.
  intros g s n. revert s. induction n as [|n IH]; intros s i H Hi; [lia|].
  cbn [seq forallb] in H. apply andb_prop in H as [H1 H2].
  destruct (Nat.eq_dec i s) as [->|NE]; [exact H1|]. apply (IH (S s)); [exact H2|lia].
Qed.

Lemma inv_check : forall i j, (i < 32)%nat -> (j < 32)%nat ->
  mm (invz i) (mm (tabz i) (2 ^ Z.of_nat j)) = 2 ^ Z.of_nat j.
Proof.
  intros i j Hi Hj. apply Z.eqb_eq.
  (* [comment removed for export] *)
  exact (forallb_seq (fun j => mm (invz i) (mm (tabz i) (2 ^ Z.of_nat j)) =? 2 ^ Z.of_nat j) 0 32 j
           (forallb_seq (fun i => forallb (fun j => mm (invz i) (mm (tabz i) (2 ^ Z.of_nat j)) =? 2 ^ Z.of_nat j) (seq 0 32)) 0 32 i inv_checkb_unf ltac:(lia))
           ltac:(lia)).
Qed.

Lemma tabz_range : forall i, (i < 32)%nat -> 0 < tabz i < 2^32.
Proof.
  intros i Hi. unfold tabz.
  do 32 (destruct i as [|i]; [cbn; lia|]). lia.
Qed.

Lemma lxor_pow2_split : forall p n, 0 <= n -> 2^n <= p < 2^(n+1) -> p = Z.lxor (p - 2^n) (2^n).
Proof.
  intros p n Hn Hp. rewrite Z.pow_add_r in Hp by lia. change (2^1) with 2 in Hp.
  rewrite Z.lxor_comm. rewrite <- Z.add_nocarry_lxor.
  - lia.
  - apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec n k); [|reflexivity]. subst k. cbn [andb].
    rewrite Z.testbit_false by lia. rewrite Z.div_small; [reflexivity|lia].
Qed.

Lemma GL_id : forall i (n : nat) p, (i < 32)%nat -> (n <= 32)%nat -> 0 <= p < 2 ^ Z.of_nat n ->
  mm (invz i) (mm (tabz i) p) = p.
Proof.
  intros i n. induction n as [|n IH]; intros p Hi Hn Hp.
  - assert (p = 0) by (cbn in Hp; lia). subst p. rewrite !mm_0. reflexivity.
  - destruct (Z.lt_ge_cases p (2 ^ Z.of_nat n)) as [LT|GE].
    + apply IH; lia.
    + rewrite Nat2Z.inj_succ in Hp. rewrite <- Z.add_1_r in Hp.
      pose proof (lxor_pow2_split p (Z.of_nat n) ltac:(lia) ltac:(lia)) as Hp'.
      set (q := p - 2 ^ Z.of_nat n) in Hp'.
      assert (Hq : 0 <= q < 2 ^ Z.of_nat n) by (subst q; rewrite Z.pow_add_r in Hp by lia; change (2^1) with 2 in Hp; lia).
      clearbody q.
      (* [comment removed for export] *)
      enough (E : mm (invz i) (mm (tabz i) (Z.lxor q (2 ^ Z.of_nat n))) = Z.lxor q (2 ^ Z.of_nat n)) by (rewrite <- Hp' in E; exact E).
      rewrite !mm_lxor. rewrite inv_check by lia. rewrite IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mm_tab_pos : forall i p, (i < 32)%nat -> 0 < p < 2^32 -> 0 < mm (tabz i) p < 2^32.
Proof.
  intros i p Hi Hp.
  pose proof (mm_range (tabz i) p ltac:(lia)) as R.
  destruct (Z.eq_dec (mm (tabz i) p) 0) as [E|NE]; [|lia].
  exfalso. pose proof (GL_id i 32 p Hi ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as G.
  rewrite E, mm_0 in G. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_pow2_testbit : forall a k, 0 <= k -> (Z.land (2^k) a =? 0) = negb (Z.testbit a k).
Proof.
  intros a k Hk.
  destruct (Z.testbit a k) eqn:T; cbn [negb].
  - apply Z.eqb_neq. intros E.
    assert (Z.testbit (Z.land (2^k) a) k = false) by (rewrite E; apply Z.bits_0).
    rewrite Z.land_spec, Z.pow2_bits_true, T in H by lia. discriminate.
  - apply Z.eqb_eq. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec k n); [subst; rewrite T|]; reflexivity.
Qed.

(* [comment removed for export] *)
Definition lowbits_nz (a k : Z) : Prop := Z.land (2^(k+1) - 1) a <> 0.

Lemma lowbits_nz_mod : forall a k, 0 <= k -> lowbits_nz a k <-> a mod 2^(k+1) <> 0.
Proof.
  intros a k Hk. unfold lowbits_nz. rewrite <- (Z.land_ones a (k+1)) by lia. unfold Z.ones.
  rewrite Z.shiftl_1_l, Z.land_comm. change (Z.pred (2^(k+1))) with (Z.pred (2^(k+1))). rewrite <- Z.sub_1_r. reflexivity.
Qed.

Lemma land_m1 : forall a k, 0 <= k -> Z.land (2^k - 1) a = a mod 2^k.
Proof.
  intros a k Hk. rewrite <- (Z.land_ones a k) by lia. unfold Z.ones. rewrite Z.shiftl_1_l, Z.land_comm, <- Z.sub_1_r. reflexivity.
Qed.

Lemma lowbits_step : forall a k, 0 <= a -> 1 <= k -> lowbits_nz a k ->
  Z.testbit a k = false \/ Z.land (2^k - 1) a <> 0 -> lowbits_nz a (k - 1).
Proof.
  intros a k Ha Hk L H. unfold lowbits_nz in *. replace (k - 1 + 1) with k by lia.
  destruct H as [T|NZ]; [|exact NZ].
  rewrite land_m1 in * by lia. intros E. apply L.
  (* [comment removed for export] *)
  rewrite <- (Z.mod_small (a mod 2^(k+1)) (2^(k+1))) by (apply Z.mod_pos_bound; lia).
  apply Z.bits_inj'. intros n Hn. rewrite Z.bits_0.
  rewrite Z.testbit_mod_pow2 by lia. rewrite Z.testbit_mod_pow2 by lia.
  destruct (Z.ltb_spec n (k+1)); [|reflexivity]. cbn [andb].
  destruct (Z.eq_dec n k) as [->|NE]; [exact T|].
  assert (Hb : Z.testbit (a mod 2^k) n = false) by (rewrite E; apply Z.bits_0).
  rewrite Z.testbit_mod_pow2 in Hb by lia. destruct (Z.ltb_spec n k); [exact Hb|lia].
Qed.

Lemma lowbits_0 : forall a, 0 <= a -> lowbits_nz a 0 -> Z.testbit a 0 = true /\ Z.land (2^0 - 1) a = 0.
Proof.
  intros a Ha L. unfold lowbits_nz in L. change (2^(0+1) - 1) with 1 in L. change (2^0 - 1) with 0. rewrite Z.land_0_l.
  split; [|reflexivity]. rewrite Z.bit0_odd.
  rewrite Z.land_comm in L. change 1 with (Z.ones 1) in L. rewrite Z.land_ones in L by lia. change (2^1) with 2 in L.
  destruct (Z.odd a) eqn:O; [reflexivity|]. exfalso. apply L.
  rewrite <- Z.negb_even in O. apply negb_false_iff in O. apply Z.even_spec in O. destruct O as [c ->].
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma lowbits_nz_init : forall a, 0 < a < 2^32 -> lowbits_nz a 31.
Proof. intros a Ha. rewrite lowbits_nz_mod by lia. change (2^(31+1)) with (2^32). rewrite Z.mod_small; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition HI32 : Z := 0xFFFFFFFF00000000.
(* [comment removed for export] *)
Definition SX (c : Z) : Z := if c <? 2^31 then c else c + HI32.

Lemma SX_range : forall c, 0 <= c < 2^32 -> 0 <= SX c < 2^64.
Proof. intros c Hc. unfold SX, HI32. destruct (Z.ltb_spec c (2^31)); lia. Qed.

Lemma SX_small : forall c, 0 <= c < 2^31 -> SX c = c.
Proof. intros c Hc. unfold SX. destruct (Z.ltb_spec c (2^31)); lia. Qed.

Lemma SX_nz : forall c, 0 <= c < 2^32 -> (SX c = 0 <-> c = 0).
Proof. intros c Hc. unfold SX, HI32. destruct (Z.ltb_spec c (2^31)); lia. Qed.

Lemma SX_mod32 : forall c, 0 <= c < 2^32 -> SX c mod 2^32 = c.
Proof.
  intros c Hc. unfold SX, HI32. destruct (Z.ltb_spec c (2^31)). { apply Z.mod_small. lia. }
  replace (c + 18446744069414584320) with (c + 4294967295 * 2^32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma HI32_testbit : forall n, 0 <= n -> Z.testbit HI32 n = (32 <=? n) && (n <? 64).
Proof.
  intros n Hn. unfold HI32. change 18446744069414584320 with (Z.shiftl (Z.ones 32) 32).
  rewrite Z.shiftl_spec by lia. destruct (Z.leb_spec 32 n).
  - rewrite Z.testbit_ones_nonneg by lia. cbn [andb]. destruct (Z.ltb_spec (n - 32) 32), (Z.ltb_spec n 64); try reflexivity; lia.
  - rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma SX_testbit : forall c n, 0 <= c < 2^32 -> 0 <= n ->
  Z.testbit (SX c) n = if n <? 32 then Z.testbit c n else if n <? 64 then Z.testbit c 31 else false.
Proof.
  intros c n Hc Hn. unfold SX. destruct (Z.ltb_spec c (2^31)).
  - destruct (Z.ltb_spec n 32); [reflexivity|].
    rewrite (testbit_small c 31 n), (testbit_small c 31 31) by lia. destruct (n <? 64); reflexivity.
  - rewrite Z.add_nocarry_lxor.
    2:{ apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, HI32_testbit, Z.bits_0 by lia.
        destruct (Z.leb_spec 32 k). 2:{ cbn [andb]. apply andb_false_r. } rewrite (testbit_small c 32 k) by lia. reflexivity. }
    rewrite Z.lxor_spec, HI32_testbit by lia.
    assert (B31 : Z.testbit c 31 = true).
    { rewrite Z.testbit_true by lia. change (2^31) with 2147483648 in *.
      assert (E : c / 2147483648 = 1) by (Z.div_mod_to_equations; nia). rewrite E. reflexivity. }
    destruct (Z.ltb_spec n 32).
    + destruct (Z.leb_spec 32 n); [lia|]. cbn [andb]. apply xorb_false_r.
    + destruct (Z.leb_spec 32 n); [|lia]. cbn [andb]. rewrite (testbit_small c 32 n) by lia.
      rewrite B31. destruct (n <? 64); reflexivity.
Qed.
Ltac bit_ext :=
  apply Z.bits_inj'; intros ?n ?Hn;
  repeat first [ rewrite Z.land_spec | rewrite Z.lxor_spec | rewrite Z.lor_spec
               | rewrite SX_testbit by lia | rewrite Z.bits_0 ].

Lemma lxor_SX : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 -> Z.lxor (SX a) (SX b) = SX (Z.lxor a b).
Proof.
  intros a b Ha Hb. pose proof (lxor_bound 32 a b ltac:(lia) Ha Hb).
  bit_ext. destruct (n <? 32); [reflexivity|]. destruct (n <? 64); reflexivity.
Qed.

Lemma land_SX : forall a b, 0 <= a < 2^32 -> 0 <= b < 2^32 -> Z.land (SX a) (SX b) = SX (Z.land a b).
Proof.
  intros a b Ha Hb. pose proof (land_bound_l 32 a b Ha ltac:(lia)).
  bit_ext. destruct (n <? 32); [reflexivity|]. destruct (n <? 64); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lxor_small_SX : forall a b, 0 <= a < 2^31 -> 0 <= b < 2^32 -> Z.lxor a (SX b) = SX (Z.lxor a b).
Proof.
  intros a b Ha Hb. rewrite <- (SX_small a Ha) at 1. apply lxor_SX; lia.
Qed.


(* [comment removed for export] *)
Lemma mm_loop_skip : forall f m a b p, Z.land m a = 0 ->
  mm_loop (S f) m a b p = mm_loop f (Z.shiftr m 1) a (cstep b) p.
Proof. intros. cbn [mm_loop]. rewrite (proj2 (Z.eqb_eq _ _) H). reflexivity. Qed.

Lemma mm_loop_exit : forall f m a b p, Z.land m a <> 0 -> Z.land (m - 1) a = 0 ->
  mm_loop (S f) m a b p = Z.lxor p b.
Proof. intros. cbn [mm_loop]. rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.eqb_eq _ _) H0). reflexivity. Qed.

Lemma mm_loop_cont : forall f m a b p, Z.land m a <> 0 -> Z.land (m - 1) a <> 0 ->
  mm_loop (S f) m a b p = mm_loop f (Z.shiftr m 1) a (cstep b) (Z.lxor p b).
Proof. intros. cbn [mm_loop]. rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.eqb_neq _ _) H0). reflexivity. Qed.
