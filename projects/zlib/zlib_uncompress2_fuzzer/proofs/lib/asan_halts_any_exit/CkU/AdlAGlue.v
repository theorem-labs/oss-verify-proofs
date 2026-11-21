(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.cks Require Import CkTables CkModel CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Lemma lo16_mach : forall a, a mod 65536 = lo16 a.
Proof. intros a. symmetry. apply lo16_mod. Qed.

Lemma hi16_mach : forall a, 0 <= a -> bv_swrap 32 (bv_wrap 32 a ≫ 16) = hi16 a.
Proof.
  intros a Ha. rewrite hi16_div_mod. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
  Z.div_mod_to_equations. lia.
Qed.


Lemma land_negflag : forall (c : bool) K, 0 <= K < 2^64 ->
  Z.land ((0 - Z.b2z c) mod 18446744073709551616) K = (if c then K else 0).
Proof.
  intros [|] K HK; cbn [Z.b2z].
  - change ((0 - 1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    apply Z.mod_small. lia.
  - reflexivity.
Qed.

Lemma csub_mach : forall x, 0 <= x < 2^63 ->
  Z_to_bv 64 (x + Z.land ((0 - Z.b2z (65520 <? x)) mod 18446744073709551616) 18446744073709486095) = Z_to_bv 64 (csub x).
Proof.
  intros x Hx. rewrite land_negflag by lia. rewrite csub_sltu.
  destruct (65520 <? x).
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    replace (x + 18446744073709486095) with (x - 65521 + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - rewrite Z.add_0_r, Z.sub_0_r. reflexivity.
Qed.

Lemma csub16_mach : forall s, 0 <= s < 2^40 ->
  Z_to_bv 64 (s ≪ 16 + Z.land ((0 - Z.b2z (65520 <? s)) mod 18446744073709551616) 18446744069415567360) = Z_to_bv 64 (csub s * 2^16).
Proof.
  intros s Hs. rewrite land_negflag by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite csub_sltu_shift16.
  destruct (65520 <? s).
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    replace (s * 2^16 + 18446744069415567360) with (s * 2^16 - 65521 * 2^16 + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - rewrite Z.add_0_r, Z.sub_0_r. reflexivity.
Qed.

Lemma csub_range : forall x, 0 <= x < 2 * BASE -> 0 <= csub x < BASE.
Proof. intros x Hx. unfold csub, BASE in *. destruct (Z.leb_spec 65521 x); lia. Qed.

Lemma csub_le : forall x, 0 <= x -> 0 <= csub x <= x.
Proof. intros x Hx. unfold csub, BASE. destruct (Z.leb_spec 65521 x); lia. Qed.


Definition amag_t (x : Z) : Z := x * AMAGIC / 2^64.
Definition amag_q (x : Z) : Z := Z.shiftr (Z.shiftr (x - amag_t x) 1 + amag_t x) 15.

Lemma amag_t_mach : forall x, 0 <= x -> (x * 4223091239536077) ≫ 64 = amag_t x.
Proof. intros x Hx. unfold amag_t, AMAGIC. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma amag_q_div : forall x, 0 <= x < 2^64 -> amag_q x = x / BASE.
Proof. intros x Hx. unfold amag_q, amag_t. apply adler_magic_div. lia. Qed.

Lemma amag_t_range : forall x, 0 <= x < 2^64 -> 0 <= amag_t x <= x.
Proof. intros x Hx. unfold amag_t. apply adler_magic_t_le. lia. Qed.

Lemma amag_v_range : forall x, 0 <= x < 2^64 -> 0 <= Z.shiftr (x - amag_t x) 1 + amag_t x <= x.
Proof.
  intros x Hx. pose proof (amag_t_range x Hx). rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  Z.div_mod_to_equations. lia.
Qed.

Lemma amag_q_range : forall x, 0 <= x < 2^64 -> 0 <= amag_q x <= x /\ 0 <= amag_q x * 65521 <= x.
Proof.
  intros x Hx. rewrite amag_q_div by exact Hx. unfold BASE. Z.div_mod_to_equations. lia.
Qed.

Lemma amag_mod : forall x, 0 <= x < 2^64 -> x - amag_q x * 65521 = x mod BASE.
Proof. intros x Hx. rewrite amag_q_div by exact Hx. apply mod_BASE_sub. Qed.


Lemma adler_len1_exit : forall adler x, 0 <= x < 256 ->
  let a1 := csub (lo16 adler + x) in
  Z.lor (csub (a1 + hi16 adler) * 2^16) a1 = adler32_z_model adler [x].
Proof.
  intros adler x Hx. cbv zeta. rewrite <- (adler_len1_path adler x Hx). cbv zeta.
  rewrite <- !csub_sltu. rewrite <- csub_sltu_shift16. reflexivity.
Qed.

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


Definition adl_resm (ab : Z * Z) : Z := Z.lor ((snd ab mod 65521) * 65536) (fst ab mod 65521).
Definition adl_resc (ab : Z * Z) : Z := Z.lor (snd ab * 65536) (fst ab).

Lemma adl_resm_eq : forall res a1 b1 a2 b2 l, a2 = a1 -> b2 = b1 ->
  res = adl_resm (adler_fold (a1, b1) l) -> res = adl_resm (adler_fold (a2, b2) l).
Proof. intros res a1 b1 a2 b2 l -> ->. exact (fun H => H). Qed.

Lemma adl_resm_resc : forall ab, adl_resm ab = adl_resc (fst ab mod 65521, snd ab mod 65521).
Proof. intros [a b]. reflexivity. Qed.

Lemma shl16_small : forall x, 0 <= x < 2^40 -> (x ≪ 16) mod 18446744073709551616 = x * 65536.
Proof. intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. change (2^16) with 65536. apply Z.mod_small. lia. Qed.

Lemma shiftr3_add16 : forall x, Z.shiftr (x + 16) 3 = Z.shiftr x 3 + 2.
Proof. intros x. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. Qed.

Lemma skipn16 : forall (l : list Z) k, (k + 16 <= length l)%nat ->
  skipn k l = nth k l 0 :: nth (k+1) l 0 :: nth (k+2) l 0 :: nth (k+3) l 0 :: nth (k+4) l 0 :: nth (k+5) l 0 :: nth (k+6) l 0 :: nth (k+7) l 0
           :: nth (k+8) l 0 :: nth (k+9) l 0 :: nth (k+10) l 0 :: nth (k+11) l 0 :: nth (k+12) l 0 :: nth (k+13) l 0 :: nth (k+14) l 0 :: nth (k+15) l 0
           :: skipn (k + 16) l.
Proof.
  assert (S1 : forall (l : list Z) k, (k < length l)%nat -> skipn k l = nth k l 0 :: skipn (S k) l).
  { induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|]. destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia. }
  intros l k Hk.
  rewrite (S1 l k) by lia. f_equal.
  replace (S k) with (k + 1)%nat by lia. rewrite (S1 l (k + 1)%nat) by lia. f_equal.
  replace (S (k + 1)) with (k + 2)%nat by lia. rewrite (S1 l (k + 2)%nat) by lia. f_equal.
  replace (S (k + 2)) with (k + 3)%nat by lia. rewrite (S1 l (k + 3)%nat) by lia. f_equal.
  replace (S (k + 3)) with (k + 4)%nat by lia. rewrite (S1 l (k + 4)%nat) by lia. f_equal.
  replace (S (k + 4)) with (k + 5)%nat by lia. rewrite (S1 l (k + 5)%nat) by lia. f_equal.
  replace (S (k + 5)) with (k + 6)%nat by lia. rewrite (S1 l (k + 6)%nat) by lia. f_equal.
  replace (S (k + 6)) with (k + 7)%nat by lia. rewrite (S1 l (k + 7)%nat) by lia. f_equal.
  replace (S (k + 7)) with (k + 8)%nat by lia. rewrite (S1 l (k + 8)%nat) by lia. f_equal.
  replace (S (k + 8)) with (k + 9)%nat by lia. rewrite (S1 l (k + 9)%nat) by lia. f_equal.
  replace (S (k + 9)) with (k + 10)%nat by lia. rewrite (S1 l (k + 10)%nat) by lia. f_equal.
  replace (S (k + 10)) with (k + 11)%nat by lia. rewrite (S1 l (k + 11)%nat) by lia. f_equal.
  replace (S (k + 11)) with (k + 12)%nat by lia. rewrite (S1 l (k + 12)%nat) by lia. f_equal.
  replace (S (k + 12)) with (k + 13)%nat by lia. rewrite (S1 l (k + 13)%nat) by lia. f_equal.
  replace (S (k + 13)) with (k + 14)%nat by lia. rewrite (S1 l (k + 14)%nat) by lia. f_equal.
  replace (S (k + 14)) with (k + 15)%nat by lia. rewrite (S1 l (k + 15)%nat) by lia. f_equal.
  f_equal. lia.
Qed.

Lemma adler_fold_16 : forall sa sb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 l,
  adler_fold (sa, sb) (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: l)
  = adler_fold (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13 + b14 + b15,
                sb + (sa + b0) + (sa + b0 + b1) + (sa + b0 + b1 + b2) + (sa + b0 + b1 + b2 + b3) + (sa + b0 + b1 + b2 + b3 + b4) + (sa + b0 + b1 + b2 + b3 + b4 + b5) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13 + b14) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13 + b14 + b15)) l.
Proof. intros. reflexivity. Qed.


Lemma adl_resm_eq0 : forall res a1 b1 a2 b2, a2 = a1 -> b2 = b1 -> res = adl_resm (a1, b1) -> res = adl_resm (a2, b2).
Proof. intros res a1 b1 a2 b2 -> ->. exact (fun H => H). Qed.

Definition adl_blocks_res (k : nat) (ab : Z * Z) (l : list Z) : Z :=
  match skipn (k * Z.to_nat NMAX) l with
  | [] => adl_resc (adler_blocks k ab l)
  | rest => adl_resm (adler_fold (adler_blocks k ab l) rest)
  end.

Definition adl_red (ab : Z * Z) : Z * Z := (fst ab mod 65521, snd ab mod 65521).

Definition adl_inner_res (k : nat) (r : Z) (ab : Z * Z) (l : list Z) : Z :=
  adl_blocks_res k (adl_red (adler_fold ab (firstn (Z.to_nat r) l))) (skipn (Z.to_nat r) l).

Lemma adl_blocks_res_S : forall k ab l, adl_blocks_res (S k) ab l = adl_inner_res k NMAX ab l.
Proof.
  intros k ab l. unfold adl_inner_res, adl_blocks_res, adl_red. rewrite adler_blocks_S_front. cbv zeta.
  change BASE with 65521. generalize (Z.to_nat NMAX). intros N.
  rewrite skipn_skipn. replace (k * N + N)%nat with (S k * N)%nat by lia. reflexivity.
Qed.

Lemma adl_inner_res_0 : forall k ab l, adl_inner_res k 0 ab l = adl_blocks_res k (adl_red ab) l.
Proof. intros. reflexivity. Qed.

Lemma adl_blocks_res_red_eq : forall res k a1 b1 a2 b2 l, a2 = a1 -> b2 = b1 ->
  res = adl_blocks_res k (adl_red (a1, b1)) l -> res = adl_blocks_res k (adl_red (a2, b2)) l.
Proof. intros res k a1 b1 a2 b2 l -> ->. exact (fun H => H). Qed.

Lemma adl_inner_res_16 : forall k r sa sb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 l, 0 <= r ->
  adl_inner_res k (r + 16) (sa, sb) (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: l)
  = adl_inner_res k r (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13 + b14 + b15,
                       sb + (sa + b0) + (sa + b0 + b1) + (sa + b0 + b1 + b2) + (sa + b0 + b1 + b2 + b3) + (sa + b0 + b1 + b2 + b3 + b4) + (sa + b0 + b1 + b2 + b3 + b4 + b5) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13 + b14) + (sa + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13 + b14 + b15)) l.
Proof.
  intros. unfold adl_inner_res. replace (Z.to_nat (r + 16)) with (16 + Z.to_nat r)%nat by lia. reflexivity.
Qed.

Lemma adl_blocks_res_0_nil : forall ab, adl_blocks_res 0 ab [] = adl_resc ab.
Proof. intros. reflexivity. Qed.

Lemma adl_blocks_res_0_cons : forall ab l, l <> [] -> adl_blocks_res 0 ab l = adl_resm (adler_fold ab l).
Proof. intros ab [|x l] H; [congruence| reflexivity]. Qed.

Lemma adl_inner_res_eq : forall res k r a1 b1 a2 b2 l, a2 = a1 -> b2 = b1 ->
  res = adl_inner_res k r (a1, b1) l -> res = adl_inner_res k r (a2, b2) l.
Proof. intros res k r a1 b1 a2 b2 l -> ->. exact (fun H => H). Qed.

Lemma adl_model_blocks : forall adler bs, 16 <= Zlen bs ->
  adler32_z_model adler bs = adl_blocks_res (Z.to_nat (Zlen bs / NMAX)) (lo16 adler, hi16 adler) bs.
Proof.
  intros adler bs H16. rewrite (adler_long_path adler bs H16). cbv zeta. unfold adl_blocks_res.
  assert (N0 : 0 <= Zlen bs / NMAX) by (apply Z.div_pos; unfold NMAX, Zlen in *; lia).
  replace (Z.to_nat (NMAX * (Zlen bs / NMAX))) with (Z.to_nat (Zlen bs / NMAX) * Z.to_nat NMAX)%nat
    by (rewrite <- Z2Nat.inj_mul by (unfold NMAX; lia); f_equal; lia).
  destruct (skipn (Z.to_nat (Zlen bs / NMAX) * Z.to_nat NMAX) bs) as [|x r].
  - unfold adl_resc. reflexivity.
  - cbv zeta. rewrite !mod_BASE_sub. unfold adl_resm, BASE. reflexivity.
Qed.

Lemma cnt347 : forall q, 0 <= q < 347 -> bv_swrap 32 ((q - 347) mod 18446744073709551616 + 1) = q + 1 - 347.
Proof.
  intros q Hq. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

Lemma sub5552_mach : forall x, Z_to_bv 64 (x + 18446744073709546064) = Z_to_bv 64 (x - 5552).
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  replace (x + 18446744073709546064) with (x - 5552 + 1 * 18446744073709551616) by lia. apply Z.mod_add. lia.
Qed.
