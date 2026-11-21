(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkXt CkMathCrc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).


Definition adler_stepm (ab : Z * Z) (x : Z) : Z * Z :=
  let a := (fst ab + x) mod BASE in (a, (snd ab + a) mod BASE).

Definition adler_sums (ab : Z * Z) (bs : list Z) : Z * Z := fold_left adler_stepm bs ab.

Lemma adler_sums_nil : forall ab, adler_sums ab [] = ab.
Proof. reflexivity. Qed.
Lemma adler_sums_cons : forall ab x r, adler_sums ab (x :: r) = adler_sums (adler_stepm ab x) r.
Proof. reflexivity. Qed.
Lemma adler_sums_app : forall ab xs ys, adler_sums ab (xs ++ ys) = adler_sums (adler_sums ab xs) ys.
Proof. intros. unfold adler_sums. apply fold_left_app. Qed.

Definition adler_ok (adler : Z) : Prop :=
  0 <= adler < 2 ^ 32 /\ lo16 adler < BASE /\ hi16 adler < BASE.

Definition adler_spec (adler : Z) (bs : list Z) : Z :=
  let ab := adler_sums (lo16 adler, hi16 adler) bs in adler_comb (fst ab) (snd ab).


Lemma BASE_pos : 0 < BASE. Proof. unfold BASE. lia. Qed.

Lemma lo16_range : forall x, 0 <= lo16 x < 65536.
Proof.
  intros x. unfold lo16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  change (2 ^ 16) with 65536. apply Z.mod_pos_bound. lia.
Qed.

Lemma hi16_range : forall x, 0 <= hi16 x < 65536.
Proof.
  intros x. unfold hi16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  change (2 ^ 16) with 65536. apply Z.mod_pos_bound. lia.
Qed.

Lemma lo16_mod : forall x, lo16 x = x mod 65536.
Proof. intros x. unfold lo16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma hi16_div_mod : forall x, hi16 x = (x / 65536) mod 65536.
Proof.
  intros x. unfold hi16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma adler_comb_add : forall a b, 0 <= a < 65536 -> 0 <= b -> adler_comb a b = a + 65536 * b.
Proof.
  intros a b Ha Hb. unfold adler_comb.
  rewrite <- Z.lxor_lor by (apply land_shiftl_disj; [change (2 ^ 16) with 65536; lia | lia | lia]).
  rewrite (lxor_shiftl_add a b 16) by (change (2 ^ 16) with 65536; lia).
  change (2 ^ 16) with 65536. reflexivity.
Qed.

Lemma adler_comb_range : forall a b, 0 <= a < 65536 -> 0 <= b < 65536 -> 0 <= adler_comb a b < 2 ^ 32.
Proof. intros a b Ha Hb. rewrite adler_comb_add by lia. lia. Qed.

Lemma lo16_comb : forall a b, 0 <= a < 65536 -> 0 <= b -> lo16 (adler_comb a b) = a.
Proof.
  intros a b Ha Hb. rewrite adler_comb_add, lo16_mod by lia.
  replace (a + 65536 * b) with (a + b * 65536) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi16_comb : forall a b, 0 <= a < 65536 -> 0 <= b < 65536 -> hi16 (adler_comb a b) = b.
Proof.
  intros a b Ha Hb. rewrite adler_comb_add, hi16_div_mod by lia.
  replace (a + 65536 * b) with (a + b * 65536) by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small a) by lia.
  apply Z.mod_small. lia.
Qed.

Lemma csub_mod : forall x, 0 <= x < 2 * BASE -> csub x = x mod BASE.
Proof.
  intros x Hx. unfold csub. destruct (Z.leb_spec BASE x).
  - apply (Z.mod_unique_pos x BASE 1); unfold BASE in *; lia.
  - symmetry. apply Z.mod_small. lia.
Qed.

Lemma csub_id : forall x, x < BASE -> csub x = x.
Proof. intros x Hx. unfold csub. destruct (Z.leb_spec BASE x); lia. Qed.

Lemma mod_BASE_sub : forall x, x - x / BASE * BASE = x mod BASE.
Proof. intros x. rewrite (Z.mod_eq x BASE) by (unfold BASE; lia). lia. Qed.

Lemma mod_BASE_range : forall x, 0 <= x mod BASE < BASE.
Proof. intros. apply Z.mod_pos_bound. apply BASE_pos. Qed.


Lemma adler_stepm_mod : forall a b x,
  adler_stepm (a mod BASE, b mod BASE) x = adler_stepm (a, b) x.
Proof.
  intros a b x. unfold adler_stepm. cbn [fst snd]. pose proof BASE_pos.
  f_equal.
  - rewrite Z.add_mod_idemp_l by lia. reflexivity.
  - rewrite Z.add_mod_idemp_l by lia. rewrite (Z.add_mod_idemp_l a x) by lia.
    rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

Theorem adler_fold_sums : forall bs a b,
  adler_sums (a mod BASE, b mod BASE) bs
  = (fst (adler_fold (a, b) bs) mod BASE, snd (adler_fold (a, b) bs) mod BASE).
Proof.
  induction bs as [|x r IH]; intros a b; [reflexivity|].
  rewrite adler_sums_cons, adler_fold_cons, adler_stepm_mod.
  unfold adler_stepm. cbn [fst snd].
  rewrite Z.add_mod_idemp_r by (unfold BASE; lia). apply IH.
Qed.

Corollary adler_fold_sums_small : forall bs a b, 0 <= a < BASE -> 0 <= b < BASE ->
  adler_sums (a, b) bs
  = (fst (adler_fold (a, b) bs) mod BASE, snd (adler_fold (a, b) bs) mod BASE).
Proof.
  intros bs a b Ha Hb. rewrite <- adler_fold_sums.
  rewrite (Z.mod_small a BASE Ha), (Z.mod_small b BASE Hb). reflexivity.
Qed.

Lemma adler_sums_range : forall bs a b, 0 <= a < BASE -> 0 <= b < BASE ->
  0 <= fst (adler_sums (a, b) bs) < BASE /\ 0 <= snd (adler_sums (a, b) bs) < BASE.
Proof.
  intros bs a b Ha Hb. rewrite adler_fold_sums_small by assumption. cbn [fst snd].
  split; apply mod_BASE_range.
Qed.


Lemma adler_fold_pair : forall bs ab, adler_fold ab bs = adler_fold (fst ab, snd ab) bs.
Proof. intros bs [a b]. reflexivity. Qed.

Lemma adler_fold_fst_bound : forall bs a b, 0 <= a -> bytes bs ->
  a <= fst (adler_fold (a, b) bs) <= a + 255 * Zlen bs.
Proof.
  unfold Zlen. induction bs as [|x r IH]; intros a b Ha Hbs.
  - cbn. lia.
  - inversion Hbs as [|x' r' Hx Hr]; subst. rewrite adler_fold_cons.
    specialize (IH (a + x) (b + (a + x)) ltac:(lia) Hr). cbn [length]. lia.
Qed.

Lemma adler_fold_snd_bound : forall bs a b, 0 <= a -> 0 <= b -> bytes bs ->
  b <= snd (adler_fold (a, b) bs) /\
  2 * snd (adler_fold (a, b) bs) <= 2 * b + 2 * Zlen bs * a + 255 * Zlen bs * (Zlen bs + 1).
Proof.
  unfold Zlen. induction bs as [|x r IH]; intros a b Ha Hb Hbs.
  - cbn. lia.
  - inversion Hbs as [|x' r' Hx Hr]; subst. rewrite adler_fold_cons.
    specialize (IH (a + x) (b + (a + x)) ltac:(lia) ltac:(lia) Hr). cbn [length].
    rewrite Nat2Z.inj_succ. nia.
Qed.

Lemma adler_fold_nonneg : forall bs a b, 0 <= a -> 0 <= b -> bytes bs ->
  0 <= fst (adler_fold (a, b) bs) /\ 0 <= snd (adler_fold (a, b) bs).
Proof.
  intros bs a b Ha Hb Hbs.
  pose proof (adler_fold_fst_bound bs a b Ha Hbs).
  pose proof (adler_fold_snd_bound bs a b Ha Hb Hbs). lia.
Qed.

Theorem adler_fold_bound_nmax : forall bs a b,
  0 <= a <= 2 ^ 17 -> 0 <= b <= 2 ^ 17 -> bytes bs -> Zlen bs <= NMAX ->
  0 <= fst (adler_fold (a, b) bs) < 2 ^ 21 /\ 0 <= snd (adler_fold (a, b) bs) < 2 ^ 34.
Proof.
  intros bs a b Ha Hb Hbs Hlen. unfold NMAX in Hlen.
  pose proof (adler_fold_fst_bound bs a b ltac:(lia) Hbs) as H1.
  pose proof (adler_fold_snd_bound bs a b ltac:(lia) ltac:(lia) Hbs) as H2.
  assert (0 <= Zlen bs) by (unfold Zlen; lia).
  set (n := Zlen bs) in *. set (a' := fst (adler_fold (a, b) bs)) in *.
  set (b' := snd (adler_fold (a, b) bs)) in *. clearbody n a' b'. clear Hbs bs.
  nia.
Qed.

Lemma Zlen_firstn_le : forall {A} n (l : list A), Zlen (firstn n l) <= Z.of_nat n.
Proof. intros. unfold Zlen. rewrite length_firstn. lia. Qed.

Lemma Zlen_firstn : forall {A} n (l : list A), (n <= length l)%nat -> Zlen (firstn n l) = Z.of_nat n.
Proof. intros. unfold Zlen. rewrite length_firstn. lia. Qed.

Lemma Zlen_skipn : forall {A} n (l : list A), Zlen (skipn n l) = Zlen l - Z.of_nat (Nat.min n (length l)).
Proof. intros. unfold Zlen. rewrite length_skipn. lia. Qed.

Lemma Zlen_app : forall {A} (xs ys : list A), Zlen (xs ++ ys) = Zlen xs + Zlen ys.
Proof. intros. unfold Zlen. rewrite length_app. lia. Qed.

Lemma Zlen_nonneg : forall {A} (l : list A), 0 <= Zlen l.
Proof. intros. unfold Zlen. lia. Qed.

Lemma adler_fold_snoc : forall bs ab x,
  adler_fold ab (bs ++ [x])
  = (fst (adler_fold ab bs) + x, snd (adler_fold ab bs) + (fst (adler_fold ab bs) + x)).
Proof. intros. rewrite adler_fold_app. destruct (adler_fold ab bs) as [a b]. reflexivity. Qed.


Lemma adler_blocks_0 : forall ab bs, adler_blocks 0 ab bs = ab.
Proof. reflexivity. Qed.

Lemma adler_blocks_S_front : forall n ab bs,
  adler_blocks (S n) ab bs
  = adler_blocks n (let ab1 := adler_fold ab (firstn (Z.to_nat NMAX) bs) in
                    (fst ab1 mod BASE, snd ab1 mod BASE)) (skipn (Z.to_nat NMAX) bs).
Proof. reflexivity. Qed.

Lemma adler_blocks_S : forall n ab bs,
  adler_blocks (S n) ab bs
  = let ab1 := adler_blocks n ab bs in
    let ab2 := adler_fold ab1 (firstn (Z.to_nat NMAX) (skipn (n * Z.to_nat NMAX) bs)) in
    (fst ab2 mod BASE, snd ab2 mod BASE).
Proof.
  induction n as [|n IH]; intros ab bs.
  - reflexivity.
  - rewrite adler_blocks_S_front. rewrite (IH _ (skipn (Z.to_nat NMAX) bs)).
    rewrite <- adler_blocks_S_front. cbv zeta.
    rewrite skipn_skipn. replace (n * Z.to_nat NMAX + Z.to_nat NMAX)%nat with (S n * Z.to_nat NMAX)%nat by lia.
    reflexivity.
Qed.

Lemma adler_blocks_sums : forall n a b bs, 0 <= a < BASE -> 0 <= b < BASE ->
  adler_blocks n (a, b) bs = adler_sums (a, b) (firstn (n * Z.to_nat NMAX) bs).
Proof.
  induction n as [|n IH]; intros a b bs Ha Hb.
  - reflexivity.
  - rewrite adler_blocks_S_front. cbv zeta.
    pose proof (mod_BASE_range (fst (adler_fold (a, b) (firstn (Z.to_nat NMAX) bs)))) as H1.
    pose proof (mod_BASE_range (snd (adler_fold (a, b) (firstn (Z.to_nat NMAX) bs)))) as H2.
    rewrite (IH _ _ _ (conj (proj1 H1) (proj2 H1)) (conj (proj1 H2) (proj2 H2))).
    rewrite <- adler_fold_sums_small by assumption.
    rewrite <- adler_sums_app. f_equal.
    change (S n * Z.to_nat NMAX)%nat with (Z.to_nat NMAX + n * Z.to_nat NMAX)%nat.
    rewrite <- firstn_add_skipn. reflexivity.
Qed.

Corollary adler_blocks_ok : forall n a b bs, 0 <= a < BASE -> 0 <= b < BASE ->
  0 <= fst (adler_blocks n (a, b) bs) < BASE /\ 0 <= snd (adler_blocks n (a, b) bs) < BASE.
Proof. intros. rewrite adler_blocks_sums by assumption. apply adler_sums_range; assumption. Qed.


Lemma bytes_hd : forall bs, bytes bs -> 0 <= hd 0 bs < 256.
Proof. intros [|x r] H; [cbn; lia|]. inversion H; subst. cbn. assumption. Qed.

Theorem adler32_z_model_spec : forall adler bs, adler_ok adler -> bytes bs ->
  adler32_z_model adler bs = adler_spec adler bs.
Proof.
  intros adler bs (Hr & Ha & Hb) Hbs. unfold adler32_z_model, adler_spec.
  pose proof (lo16_range adler) as Ha0. pose proof (hi16_range adler) as Hb0.
  set (a := lo16 adler) in *. set (b := hi16 adler) in *.
  pose proof BASE_pos as HB.
  destruct (Z.eqb_spec (Zlen bs) 1) as [H1|H1].
  -
    destruct bs as [|x [|y r]]; unfold Zlen in H1; cbn [length] in H1; try lia.
    cbn [hd adler_sums fold_left]. unfold adler_stepm. cbn [fst snd].
    pose proof (bytes_hd [x] Hbs) as Hx. cbn [hd] in Hx.
    rewrite (csub_mod (a + x)) by (unfold BASE in *; lia).
    pose proof (mod_BASE_range (a + x)).
    rewrite csub_mod by (unfold BASE in *; lia). reflexivity.
  - destruct (Z.ltb_spec (Zlen bs) 16) as [H16|H16].
    +
      rewrite adler_fold_sums_small by lia.
      pose proof (adler_fold_fst_bound bs a b ltac:(lia) Hbs) as Hf. cbn [fst snd].
      rewrite csub_mod by (unfold BASE in *; lia). reflexivity.
    +
      set (nblk := Zlen bs / NMAX).
      assert (Hn : 0 <= nblk) by (subst nblk; apply Z.div_pos; unfold NMAX; lia).
      rewrite adler_blocks_sums by lia.
      replace (Z.to_nat (NMAX * nblk)) with (Z.to_nat nblk * Z.to_nat NMAX)%nat by (unfold NMAX in *; lia).
      set (k := (Z.to_nat nblk * Z.to_nat NMAX)%nat).
      destruct (skipn k bs) as [|y r] eqn:Hrest.
      *
        assert (Hall : firstn k bs = bs).
        { rewrite <- (firstn_skipn k bs) at 2. rewrite Hrest, app_nil_r. reflexivity. }
        rewrite Hall. reflexivity.
      * rewrite <- Hrest.
        pose proof (adler_sums_range (firstn k bs) a b ltac:(lia) ltac:(lia)) as [Hs1 Hs2].
        destruct (adler_sums (a, b) (firstn k bs)) as [a1 b1] eqn:E1. cbn [fst snd] in Hs1, Hs2.
        replace (adler_sums (a, b) bs) with (adler_sums (a1, b1) (skipn k bs)).
        2:{ rewrite <- E1, <- adler_sums_app, firstn_skipn. reflexivity. }
        rewrite (adler_fold_sums_small (skipn k bs) a1 b1 Hs1 Hs2). reflexivity.
Qed.

Theorem adler32_z_model_range : forall adler bs, bytes bs ->
  0 <= adler32_z_model adler bs < 2 ^ 32.
Proof.
  intros adler bs Hbs. unfold adler32_z_model.
  pose proof (lo16_range adler) as Ha0. pose proof (hi16_range adler) as Hb0.
  set (a := lo16 adler) in *. set (b := hi16 adler) in *.
  pose proof BASE_pos as HB.
  destruct (Z.eqb_spec (Zlen bs) 1) as [H1|H1].
  - destruct bs as [|x [|y r]]; unfold Zlen in H1; cbn [length] in H1; try lia.
    cbn [hd]. pose proof (bytes_hd [x] Hbs) as Hx. cbn [hd] in Hx.
    apply adler_comb_range; unfold csub, BASE in *;
      repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end;
      repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H
                            | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end; lia.
  - destruct (Z.ltb_spec (Zlen bs) 16) as [H16|H16].
    + pose proof (adler_fold_fst_bound bs a b ltac:(lia) Hbs) as Hf.
      pose proof (mod_BASE_range (snd (adler_fold (a, b) bs))).
      apply adler_comb_range; unfold csub, BASE in *;
        repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end;
        repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H
                              | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end; lia.
    + set (n := Z.to_nat (Zlen bs / NMAX)).
      destruct (skipn (Z.to_nat (NMAX * (Zlen bs / NMAX))) bs) as [|y r] eqn:Hrest.
      * assert (Hn : (0 < n)%nat).
        { apply (f_equal (@length Z)) in Hrest. rewrite length_skipn in Hrest. cbn [length] in Hrest.
          unfold Zlen, NMAX in *. subst n.
          assert (0 <= Z.of_nat (length bs) / 5552) by (apply Z.div_pos; lia). nia. }
        destruct n as [|m] eqn:En; [lia|].
        rewrite adler_blocks_S. cbv zeta.
        pose proof (mod_BASE_range (fst (adler_fold (adler_blocks m (a, b) bs)
                      (firstn (Z.to_nat NMAX) (skipn (m * Z.to_nat NMAX) bs))))).
        pose proof (mod_BASE_range (snd (adler_fold (adler_blocks m (a, b) bs)
                      (firstn (Z.to_nat NMAX) (skipn (m * Z.to_nat NMAX) bs))))).
        cbn [fst snd]. apply adler_comb_range; unfold BASE in *; lia.
      * cbv zeta.
        pose proof (mod_BASE_range (fst (adler_fold (adler_blocks n (a, b) bs) (y :: r)))).
        pose proof (mod_BASE_range (snd (adler_fold (adler_blocks n (a, b) bs) (y :: r)))).
        apply adler_comb_range; unfold BASE in *; lia.
Qed.


Lemma adler_ok_1 : adler_ok 1.
Proof. unfold adler_ok, lo16, hi16, BASE. cbn. lia. Qed.

Lemma adler_ok_halves : forall adler, adler_ok adler ->
  0 <= lo16 adler < BASE /\ 0 <= hi16 adler < BASE.
Proof.
  intros adler (Hr & Ha & Hb). pose proof (lo16_range adler). pose proof (hi16_range adler). lia.
Qed.

Theorem adler_spec_ok : forall adler bs, adler_ok adler -> adler_ok (adler_spec adler bs).
Proof.
  intros adler bs Hok. pose proof (adler_ok_halves adler Hok) as [Ha Hb].
  unfold adler_spec.
  pose proof (adler_sums_range bs (lo16 adler) (hi16 adler) Ha Hb) as [H1 H2].
  set (ab := adler_sums (lo16 adler, hi16 adler) bs) in *.
  unfold adler_ok. rewrite lo16_comb, hi16_comb by (unfold BASE in *; lia).
  split; [apply adler_comb_range; unfold BASE in *; lia | lia].
Qed.

Theorem adler_spec_range : forall adler bs, adler_ok adler -> 0 <= adler_spec adler bs < 2 ^ 32.
Proof. intros adler bs H. exact (proj1 (adler_spec_ok adler bs H)). Qed.

Theorem adler_spec_nil : forall adler, adler_ok adler -> adler_spec adler [] = adler.
Proof.
  intros adler (Hr & Ha & Hb). unfold adler_spec. cbn [adler_sums fold_left fst snd].
  pose proof (lo16_range adler). pose proof (hi16_range adler).
  rewrite adler_comb_add by lia. rewrite lo16_mod, hi16_div_mod.
  rewrite (Z.mod_small (adler / 65536)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  pose proof (Z.div_mod adler 65536 ltac:(lia)). lia.
Qed.

Theorem adler_spec_app : forall adler xs ys, adler_ok adler ->
  adler_spec (adler_spec adler xs) ys = adler_spec adler (xs ++ ys).
Proof.
  intros adler xs ys Hok. pose proof (adler_ok_halves adler Hok) as [Ha Hb].
  unfold adler_spec. rewrite adler_sums_app.
  pose proof (adler_sums_range xs (lo16 adler) (hi16 adler) Ha Hb) as [H1 H2].
  set (ab := adler_sums (lo16 adler, hi16 adler) xs) in *.
  rewrite lo16_comb, hi16_comb by (unfold BASE in *; lia).
  rewrite <- (surjective_pairing ab). reflexivity.
Qed.

Corollary adler32_z_model_app : forall adler xs ys, adler_ok adler -> bytes xs -> bytes ys ->
  adler32_z_model (adler32_z_model adler xs) ys = adler_spec adler (xs ++ ys).
Proof.
  intros adler xs ys Hok Hxs Hys.
  rewrite (adler32_z_model_spec adler xs Hok Hxs).
  rewrite (adler32_z_model_spec _ ys (adler_spec_ok adler xs Hok) Hys).
  apply adler_spec_app. exact Hok.
Qed.

Corollary adler32_z_model_ok : forall adler bs, adler_ok adler -> bytes bs ->
  adler_ok (adler32_z_model adler bs).
Proof. intros. rewrite adler32_z_model_spec by assumption. apply adler_spec_ok. assumption. Qed.



Lemma AMAGIC_val : AMAGIC = 4223091239536077.
Proof. reflexivity. Qed.

Lemma adler_magic_t_le : forall x, 0 <= x -> 0 <= x * AMAGIC / 2 ^ 64 <= x.
Proof.
  intros x Hx. rewrite AMAGIC_val. split; [apply Z.div_pos; lia|].
  apply Z.div_le_upper_bound; lia.
Qed.

Lemma half_sum_trick : forall x t, 0 <= t <= x -> (x - t) / 2 + t = (x + t) / 2.
Proof. intros x t Ht. rewrite <- (Z.div_add (x - t) t 2) by lia. f_equal. lia. Qed.

Theorem adler_magic_div_Z : forall x, 0 <= x < 2 ^ 64 ->
  ((x - x * AMAGIC / 2 ^ 64) / 2 + x * AMAGIC / 2 ^ 64) / 2 ^ 15 = x / BASE.
Proof.
  intros x Hx. pose proof (adler_magic_t_le x ltac:(lia)) as Ht.
  rewrite half_sum_trick by exact Ht.
  rewrite AMAGIC_val in *. unfold BASE.
  replace (x + x * 4223091239536077 / 2 ^ 64) with ((x * (2 ^ 64 + 4223091239536077)) / 2 ^ 64).
  2:{ rewrite Z.mul_add_distr_l, Z.div_add_l by lia. reflexivity. }
  rewrite !Z.div_div by lia.
  change (2 ^ 64 * 2 * 2 ^ 15) with (2 ^ 80).
  set (K := 2 ^ 64 + 4223091239536077).
  assert (HK : K * 65521 = 2 ^ 80 + 26877) by reflexivity.
  pose proof (Z.div_mod x 65521 ltac:(lia)) as Hx1.
  pose proof (Z.mod_pos_bound x 65521 ltac:(lia)) as Hx2.
  set (q := x / 65521) in *. set (r := x mod 65521) in *.
  symmetry. apply (Z.div_unique_pos (x * K) (2 ^ 80) q (q * 26877 + r * K)); subst K; lia.
Qed.

Theorem adler_magic_div : forall x, 0 <= x < 2 ^ 64 ->
  Z.shiftr (Z.shiftr (x - x * AMAGIC / 2 ^ 64) 1 + x * AMAGIC / 2 ^ 64) 15 = x / BASE.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  apply adler_magic_div_Z. exact Hx.
Qed.

Lemma adler_magic_ranges : forall x, 0 <= x < 2 ^ 64 ->
  let t := x * AMAGIC / 2 ^ 64 in
  0 <= t <= x /\ 0 <= x - t < 2 ^ 64 /\ 0 <= Z.shiftr (x - t) 1 + t < 2 ^ 64 /\
  0 <= x / BASE <= x /\ 0 <= x / BASE * BASE <= x /\ 0 <= x - x / BASE * BASE < BASE.
Proof.
  intros x Hx t. pose proof (adler_magic_t_le x ltac:(lia)) as Ht. subst t.
  set (t := x * AMAGIC / 2 ^ 64) in *.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  pose proof (Z.div_mod x BASE ltac:(unfold BASE; lia)).
  pose proof (mod_BASE_range x).
  assert (0 <= x / BASE) by (apply Z.div_pos; unfold BASE; lia).
  unfold BASE in *. lia.
Qed.

Definition AMAGIC2 : Z := 2147975281.

Theorem adler_magic2_div_Z : forall x, 0 <= x < 2 ^ 32 -> x * AMAGIC2 / 2 ^ 47 = x / BASE.
Proof.
  intros x Hx. unfold AMAGIC2, BASE.
  pose proof (Z.div_mod x 65521 ltac:(lia)) as Hx1.
  pose proof (Z.mod_pos_bound x 65521 ltac:(lia)) as Hx2.
  set (q := x / 65521) in *. set (r := x mod 65521) in *.
  assert (HK : 2147975281 * 65521 = 2 ^ 47 + 31073) by reflexivity.
  symmetry. apply (Z.div_unique_pos (x * 2147975281) (2 ^ 47) q (q * 31073 + r * 2147975281)); lia.
Qed.

Theorem adler_magic2_div : forall x, 0 <= x < 2 ^ 32 -> Z.shiftr (x * AMAGIC2) 47 = x / BASE.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. apply adler_magic2_div_Z. exact Hx. Qed.

Lemma adler_magic2_ranges : forall x, 0 <= x < 2 ^ 32 ->
  0 <= x * AMAGIC2 < 2 ^ 64 /\ 0 <= x / BASE <= x /\ 0 <= x - x / BASE * BASE < BASE.
Proof.
  intros x Hx. unfold AMAGIC2.
  pose proof (Z.div_mod x BASE ltac:(unfold BASE; lia)).
  pose proof (mod_BASE_range x).
  assert (0 <= x / BASE) by (apply Z.div_pos; unfold BASE; lia).
  unfold BASE in *. lia.
Qed.


Lemma land_65535_range : forall x, 0 <= Z.land x 65535 < 65536.
Proof.
  intros x. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
  change (2 ^ 16) with 65536. apply Z.mod_pos_bound. lia.
Qed.

Lemma adler32_combine_model_range : forall a1 a2 len, adler_ok a1 -> adler_ok a2 ->
  0 <= adler32_combine_model a1 a2 len < 2 ^ 32.
Proof.
  intros a1 a2 len (_ & A1 & B1) (_ & A2 & B2). unfold lo16, hi16 in *. unfold adler32_combine_model.
  destruct (Z.ltb_spec len 0); [unfold M32; lia|].
  pose proof (land_65535_range a1). pose proof (land_65535_range a2).
  pose proof (land_65535_range (Z.shiftr a1 16)). pose proof (land_65535_range (Z.shiftr a2 16)).
  pose proof (mod_BASE_range len). pose proof (mod_BASE_range (len mod BASE * Z.land a1 65535)).
  cbv zeta. apply adler_comb_range; unfold csub, BASE in *;
    repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end;
    repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H
                          | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H end; lia.
Qed.
