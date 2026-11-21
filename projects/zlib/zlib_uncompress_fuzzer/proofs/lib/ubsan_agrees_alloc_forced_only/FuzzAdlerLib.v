(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec SeqExec FuzzZ FuzzMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma lo16_machine : forall a, 0 <= a -> Z.shiftr ((a * 2 ^ 48) mod two64) 48 = lo16 a.
Proof.
  intros a Ha. rewrite lo16_mod. rewrite Z.shiftr_div_pow2 by lia.
  change two64 with (2 ^ 16 * 2 ^ 48).
  rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma hi16_machine : forall a, 0 <= a -> Z.shiftr (a mod two32) 16 = hi16 a.
Proof.
  intros a Ha. rewrite hi16_div_mod. rewrite Z.shiftr_div_pow2 by lia.
  change two32 with (65536 * 2 ^ 16). change (2 ^ 16) with 65536.
  rewrite Z.rem_mul_r by lia.
  rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia.
  rewrite (Z.div_small (a mod 65536)) by (apply Z.mod_pos_bound; lia). lia.
Qed.



Lemma land_negflag : forall (c : bool) K, Z.land (0 - (if c then 1 else 0)) K = (if c then K else 0).
Proof. intros [|] K; [apply Z.land_m1_l | apply Z.land_0_l]. Qed.

Lemma csub_machine : forall x K, 0 <= x -> K mod two64 = two64 - 65521 ->
  Z_to_bv 64 (x + (if 65520 <? x then K else 0)) = Z_to_bv 64 (csub x).
Proof.
  intros x K Hx HK. rewrite csub_sltu. apply zv_eq.
  destruct (65520 <? x).
  - rewrite <- Z.add_mod_idemp_r, HK by lia.
    replace (x + (two64 - 65521)) with ((x - 65521) + 1 * two64) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - rewrite Z.add_0_r, Z.sub_0_r. reflexivity.
Qed.

Lemma csub16_machine : forall s K, 0 <= s -> K mod two64 = two64 - 65521 * 2 ^ 16 ->
  Z_to_bv 64 (s * 2 ^ 16 + (if 65520 <? s then K else 0)) = Z_to_bv 64 (csub s * 2 ^ 16).
Proof.
  intros s K Hs HK. rewrite csub_sltu_shift16. apply zv_eq.
  destruct (65520 <? s).
  - rewrite <- Z.add_mod_idemp_r, HK by lia.
    replace (s * 2 ^ 16 + (two64 - 65521 * 2 ^ 16)) with ((s * 2 ^ 16 - 65521 * 2 ^ 16) + 1 * two64) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - rewrite Z.add_0_r, Z.sub_0_r. reflexivity.
Qed.


Lemma csub_nonneg : forall x, 0 <= x -> 0 <= csub x <= x.
Proof. intros x Hx. unfold csub, BASE. destruct (Z.leb_spec 65521 x); lia. Qed.


Definition amag_t (x : Z) : Z := x * AMAGIC / two64.
Definition amag_q (x : Z) : Z := Z.shiftr (Z.shiftr (x - amag_t x) 1 + amag_t x) 15.

Lemma amag_q_div : forall x, 0 <= x < two64 -> amag_q x = x / BASE.
Proof. intros x Hx. unfold amag_q, amag_t. change two64 with (2 ^ 64). apply adler_magic_div. lia. Qed.

Lemma amag_t_range : forall x, 0 <= x < two64 -> 0 <= amag_t x <= x.
Proof. intros x Hx. unfold amag_t. change two64 with (2 ^ 64). apply adler_magic_t_le. lia. Qed.

Lemma amag_u_range : forall x, 0 <= x < two64 -> 0 <= x - amag_t x < two64.
Proof. intros x Hx. pose proof (amag_t_range x Hx). lia. Qed.

Lemma amag_v_range : forall x, 0 <= x < two64 -> 0 <= Z.shiftr (x - amag_t x) 1 + amag_t x < two64.
Proof.
  intros x Hx. pose proof (amag_t_range x Hx). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  assert (0 <= (x - amag_t x) / 2) by (apply Z.div_pos; lia).
  assert ((x - amag_t x) / 2 <= x - amag_t x) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

Lemma amag_q_range : forall x, 0 <= x < two64 -> 0 <= amag_q x <= x /\ 0 <= amag_q x * 65521 <= x.
Proof.
  intros x Hx. rewrite amag_q_div by exact Hx. unfold BASE.
  pose proof (Z.div_mod x 65521 ltac:(lia)). pose proof (Z.mod_pos_bound x 65521 ltac:(lia)).
  assert (0 <= x / 65521) by (apply Z.div_pos; lia). lia.
Qed.

Lemma amag_mod : forall x, 0 <= x < two64 -> x - amag_q x * 65521 = x mod BASE.
Proof. intros x Hx. rewrite amag_q_div by exact Hx. apply mod_BASE_sub. Qed.





Section MEM.
  Variable segs : list Segment.
  #[local] Notation "'BA' m" := (byte_at segs m) (at level 10, m at level 9).



  Lemma adler_fold_bytes_S : forall m ab a n,
    adler_fold ab (bytes_at segs m a (S n))
    = (fst (adler_fold ab (bytes_at segs m a n)) + BA m (a + Z.of_nat n),
       snd (adler_fold ab (bytes_at segs m a n)) + (fst (adler_fold ab (bytes_at segs m a n)) + BA m (a + Z.of_nat n))).
  Proof. intros. rewrite bytes_at_snoc. apply adler_fold_snoc. Qed.

  Lemma adler_fold_bytes_add : forall m ab a n k,
    adler_fold ab (bytes_at segs m a (n + k))
    = adler_fold (adler_fold ab (bytes_at segs m a n)) (bytes_at segs m (a + Z.of_nat n) k).
  Proof. intros. rewrite bytes_at_app. apply adler_fold_app. Qed.

  Lemma bytes_at_bytes : forall m a n, bytes (bytes_at segs m a n).
  Proof. intros. apply bytes_at_range. Qed.

  Lemma Zlen_bytes_at : forall m a n, Zlen (bytes_at segs m a n) = Z.of_nat n.
  Proof. intros. unfold Zlen. rewrite bytes_at_length. reflexivity. Qed.
End MEM.


Lemma sums_range64 : forall a b bs,
  0 <= a <= 65535 -> 0 <= b <= 65535 -> bytes bs -> Zlen bs <= NMAX ->
  0 <= fst (adler_fold (a, b) bs) < two64 /\ 0 <= snd (adler_fold (a, b) bs) < two64.
Proof.
  intros a b bs Ha Hb Hbs Hn.
  pose proof (adler_fold_bound_nmax bs a b ltac:(lia) ltac:(lia) Hbs Hn). lia.
Qed.

Lemma sums_range64' : forall ab bs,
  0 <= fst ab <= 65535 -> 0 <= snd ab <= 65535 -> bytes bs -> Zlen bs <= NMAX ->
  0 <= fst (adler_fold ab bs) < two64 /\ 0 <= snd (adler_fold ab bs) < two64.
Proof. intros [a b] bs; cbn [fst snd]. apply sums_range64. Qed.

Lemma short_a_range : forall a b bs,
  0 <= a <= 65535 -> bytes bs -> Zlen bs < 16 ->
  0 <= fst (adler_fold (a, b) bs) < 65536 + 16 * 255.
Proof.
  intros a b bs Ha Hbs Hn. pose proof (adler_fold_fst_bound bs a b ltac:(lia) Hbs). lia.
Qed.

Lemma adler_fold_4 : forall A B c0 c1 c2 c3,
  adler_fold (A, B) [c0; c1; c2; c3]
  = (A + c0 + c1 + c2 + c3,
     B + (A + c0) + (A + c0 + c1) + (A + c0 + c1 + c2) + (A + c0 + c1 + c2 + c3)).
Proof. intros. reflexivity. Qed.

Lemma adler_fold_pair_eta : forall ab l, adler_fold ab l = adler_fold (fst ab, snd ab) l.
Proof. intros [a b] l. reflexivity. Qed.

Section MEM16.
  Variable segs : list Segment.


End MEM16.

Lemma adler_fold_16_groups : forall ab b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15,
  adler_fold ab [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15]
  = adler_fold (adler_fold (adler_fold (adler_fold ab
      [b0; b1; b2; b3]) [b4; b5; b6; b7]) [b8; b9; b10; b11]) [b12; b13; b14; b15].
Proof.
  intros.
  change [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15]
    with ([b0; b1; b2; b3] ++ ([b4; b5; b6; b7] ++ ([b8; b9; b10; b11] ++ [b12; b13; b14; b15]))).
  rewrite !adler_fold_app. reflexivity.
Qed.

Section MEM16B.
  Variable segs : list Segment.
  Lemma bytes_at_16_list : forall m a,
    bytes_at segs m a 16
    = [byte_at segs m a; byte_at segs m (a + 1); byte_at segs m (a + 2); byte_at segs m (a + 3);
       byte_at segs m (a + 4); byte_at segs m (a + 5); byte_at segs m (a + 6); byte_at segs m (a + 7);
       byte_at segs m (a + 8); byte_at segs m (a + 9); byte_at segs m (a + 10); byte_at segs m (a + 11);
       byte_at segs m (a + 12); byte_at segs m (a + 13); byte_at segs m (a + 14); byte_at segs m (a + 15)].
  Proof.
    intros m a. cbn [bytes_at].
    replace (a + 1 + 1) with (a + 2) by lia. replace (a + 2 + 1) with (a + 3) by lia.
    replace (a + 3 + 1) with (a + 4) by lia. replace (a + 4 + 1) with (a + 5) by lia.
    replace (a + 5 + 1) with (a + 6) by lia. replace (a + 6 + 1) with (a + 7) by lia.
    replace (a + 7 + 1) with (a + 8) by lia. replace (a + 8 + 1) with (a + 9) by lia.
    replace (a + 9 + 1) with (a + 10) by lia. replace (a + 10 + 1) with (a + 11) by lia.
    replace (a + 11 + 1) with (a + 12) by lia. replace (a + 12 + 1) with (a + 13) by lia.
    replace (a + 13 + 1) with (a + 14) by lia. replace (a + 14 + 1) with (a + 15) by lia.
    reflexivity.
  Qed.
End MEM16B.


Section SLICE.
  Variable segs : list Segment.
  #[local] Notation "'BS' m" := (bytes_at segs m) (at level 10, m at level 9).

  Lemma bytes_at_nil : forall m a, bytes_at segs m a 0 = [].
  Proof. reflexivity. Qed.

  Lemma adler_fold_bytes_0 : forall m ab a, adler_fold ab (bytes_at segs m a 0) = ab.
  Proof. intros m [x y] a. reflexivity. Qed.

  Lemma bytes_at_skipn : forall m a n j, (j <= n)%nat ->
    skipn j (BS m a n) = BS m (a + Z.of_nat j) (n - j).
  Proof.
    intros m a n j Hj. replace n with (j + (n - j))%nat at 1 by lia.
    rewrite bytes_at_app, skipn_app, bytes_at_length, Nat.sub_diag, skipn_all2 by (rewrite bytes_at_length; lia).
    reflexivity.
  Qed.

  Lemma bytes_at_firstn : forall m a n k, (k <= n)%nat -> firstn k (BS m a n) = BS m a k.
  Proof.
    intros m a n k Hk. replace n with (k + (n - k))%nat by lia.
    rewrite bytes_at_app, firstn_app, bytes_at_length, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite firstn_all2 by (rewrite bytes_at_length; lia). reflexivity.
  Qed.

  Lemma bytes_at_slice : forall m a n j k, (j + k <= n)%nat ->
    firstn k (skipn j (BS m a n)) = BS m (a + Z.of_nat j) k.
  Proof. intros. rewrite bytes_at_skipn by lia. apply bytes_at_firstn. lia. Qed.

  Lemma adler_blocks_bytes_S : forall m i ab a n, 5552 * Z.of_nat (S i) <= Z.of_nat n ->
    adler_blocks (S i) ab (BS m a n)
    = (fst (adler_fold (adler_blocks i ab (BS m a n)) (BS m (a + 5552 * Z.of_nat i) (Z.to_nat NMAX))) mod BASE,
       snd (adler_fold (adler_blocks i ab (BS m a n)) (BS m (a + 5552 * Z.of_nat i) (Z.to_nat NMAX))) mod BASE).
  Proof.
    intros m i ab a n Hn. rewrite adler_blocks_S. cbv zeta.
    rewrite bytes_at_slice by (unfold NMAX in *; lia).
    replace (a + Z.of_nat (i * Z.to_nat NMAX)) with (a + 5552 * Z.of_nat i) by (unfold NMAX; lia). reflexivity.
  Qed.

  Lemma adler_rest_bytes : forall m a n (nb : nat), 5552 * Z.of_nat nb <= Z.of_nat n ->
    skipn (Z.to_nat (NMAX * Z.of_nat nb)) (BS m a n) = BS m (a + 5552 * Z.of_nat nb) (n - nb * Z.to_nat NMAX).
  Proof.
    intros m a n nb H. replace (Z.to_nat (NMAX * Z.of_nat nb)) with (nb * Z.to_nat NMAX)%nat by (unfold NMAX; lia).
    rewrite bytes_at_skipn by (unfold NMAX in *; lia). f_equal. unfold NMAX; lia.
  Qed.
End SLICE.


Lemma adler_short_exit : forall adler bs, Zlen bs <> 1 -> Zlen bs < 16 ->
  let ab := adler_fold (lo16 adler, hi16 adler) bs in
  Z.lor ((snd ab mod BASE) * 2 ^ 16) (csub (fst ab)) = adler32_z_model adler bs.
Proof.
  intros adler bs H1 H16. cbv zeta. rewrite <- adler_short_path by assumption.
  rewrite csub_sltu, mod_BASE_sub. reflexivity.
Qed.

Lemma adler_long_exit_nil : forall adler bs, 16 <= Zlen bs ->
  let nblk := Zlen bs / NMAX in
  let ab1 := adler_blocks (Z.to_nat nblk) (lo16 adler, hi16 adler) bs in
  skipn (Z.to_nat (NMAX * nblk)) bs = [] ->
  Z.lor (snd ab1 * 2 ^ 16) (fst ab1) = adler32_z_model adler bs.
Proof.
  intros adler bs H16 nblk ab1 Hrest. rewrite (adler_long_path adler bs H16). cbv zeta.
  fold nblk. rewrite Hrest. reflexivity.
Qed.

Lemma adler_long_exit_cons : forall adler bs rest, 16 <= Zlen bs ->
  let nblk := Zlen bs / NMAX in
  let ab1 := adler_blocks (Z.to_nat nblk) (lo16 adler, hi16 adler) bs in
  skipn (Z.to_nat (NMAX * nblk)) bs = rest -> rest <> [] ->
  let ab2 := adler_fold ab1 rest in
  Z.lor ((snd ab2 mod BASE) * 2 ^ 16) (fst ab2 mod BASE) = adler32_z_model adler bs.
Proof.
  intros adler bs rest H16 nblk ab1 Hrest Hne ab2. rewrite (adler_long_path adler bs H16). cbv zeta.
  fold nblk. rewrite Hrest. destruct rest as [|x r]; [congruence|].
  subst ab2. rewrite !mod_BASE_sub. reflexivity.
Qed.
