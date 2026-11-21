(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.U2A Require Import InfPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma pow2_le_40 : forall b, 0 <= b <= 40 -> 2 ^ b <= 2 ^ 40.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.

Lemma hold_u64 : forall h b, 0 <= b <= 40 -> 0 <= h < 2 ^ b -> 0 <= h < 18446744073709551616.
Proof. intros h b Hb Hh. pose proof (pow2_le_40 b Hb). change (2 ^ 40) with 1099511627776 in *. lia. Qed.

Lemma shiftr_lt_pow2 : forall h b k, 0 <= k <= b -> 0 <= h < 2 ^ b -> 0 <= Z.shiftr h k < 2 ^ (b - k).
Proof.
  intros h b k Hk Hh. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (b - k)) with b by lia. lia.
Qed.

Lemma pullbyte_bound : forall h b c, 0 <= b -> 0 <= h < 2 ^ b -> 0 <= c < 256 ->
  0 <= h + c * 2 ^ b < 2 ^ (b + 8).
Proof.
  intros h b c Hb Hh Hc. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  assert (0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

Lemma bits2_of_shift : forall h, 0 <= h < 18446744073709551616 ->
  Z.shiftr (Z.shiftl h 61 mod 18446744073709551616) 62 = (h / 2) mod 4.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 61) with 2305843009213693952. change (2 ^ 62) with 4611686018427387904. lia.
Qed.

Lemma smod64_nz : forall x, -9223372036854775808 <= x < 9223372036854775808 -> x <> 0 ->
  x mod 18446744073709551616 <> 0.
Proof. intros x Hx Hnz. lia. Qed.

Lemma land7_mod : forall b, 0 <= b -> Z.land b 7 = b mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma landm8 : forall b, 0 <= b -> Z.land b (-8) = b - b mod 8.
Proof.
  intros b Hb. change (-8) with (Z.lnot 7). rewrite <- Z.ldiff_land.
  change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia.
Qed.
Lemma land1_mod : forall h, 0 <= h -> Z.land h 1 = h mod 2.
Proof. intros. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma lor8_small : forall b, 0 <= b < 8 -> Z.lor b 8 = b + 8.
Proof.
  intros b Hb.
  assert (C : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7) by lia.
  decompose [or] C; subst; reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition bytebits_st (st : ist) : ist :=
  IST CHECK (t_last st) (t_flags st) (t_cin st) (t_cout st)
      (Z.shiftr (t_hold st) (t_bits st mod 8)) (t_bits st - t_bits st mod 8) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Definition typedo_st (st : ist) (m cin1 hold1 bits1 : Z) (fx : bool) : ist :=
  IST m (Z.land hold1 1) (t_flags st) cin1 (t_cout st) (Z.shiftr hold1 3) (bits1 - 3) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st)
      (if fx then CLenfix else t_lc st) (if fx then CDistfix else t_dc st)
      (if fx then 9 else t_lb st) (if fx then 5 else t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_bytebits : forall cx st lf cf,
  sinv cx st lf cf -> (t_mode st = TYPE \/ t_mode st = TYPEDO) ->
  sinv cx (bytebits_st st) lf cf /\ meas cx (bytebits_st st) < meas cx st.
Proof.
  intros cx st lf cf (R & W & P & Mo) Hm.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode] in Hm.
  unfold RNG in R. icx_cbn. destr_conj R.
  assert (Hk : 0 <= bits mod 8 <= bits) by (Z.to_euclidean_division_equations; lia_std).
  pose proof (shiftr_lt_pow2 hold bits (bits mod 8) ltac:(lia_std) ltac:(lia_std)) as Hsh.
  assert (Hmono : 2 ^ (bits - bits mod 8) <= 2 ^ bits) by (apply Z.pow_le_mono_r; lia_std).
  split.
  - split; [| split; [exact W | split]].
    + unfold RNG, bytebits_st; icx_cbn. split_conj; try assumption; try lia_std.
    + unfold PROG, bytebits_st, Wm in *; icx_cbn. mode_consts. lia_std.
    + pose proof (proj1 (proj2 Mo)) as Mf. clear Mo W P. unfold MODE, bytebits_st; icx_cbn. mode_consts.
      mode_solve Mf fail.
  - apply meas_dec_rank; [unfold Wm, bytebits_st; icx_cbn; lia_std|].
    unfold bytebits_st; cbn [t_mode]. unfold rank. mode_consts.
    destruct Hm as [-> | ->]; cbn; lia_std.
Qed.

Lemma sinv_typedo : forall cx st lf cf m cin1 hold1 bits1 fx,
  sinv cx st lf cf -> (t_mode st = TYPE \/ t_mode st = TYPEDO) ->
  t_cin st <= cin1 <= c_n cx -> 3 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
  8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  (m = STORED \/ m = TABLE \/ m = BAD \/ m = LEN_) -> (fx = true <-> m = LEN_) ->
  sinv cx (typedo_st st m cin1 hold1 bits1 fx) lf cf /\ meas cx (typedo_st st m cin1 hold1 bits1 fx) < meas cx st.
Proof.
  intros cx st lf cf m cin1 hold1 bits1 fx (R & W & P & Mo) Hm Hc Hb Hh Hbc HW Hm' Hfx.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_cin t_bits] in Hm, Hc, HW. icx_cbn.
  unfold RNG in R. icx_cbn. destr_conj R.
  pose proof (shiftr_lt_pow2 hold1 bits1 3 ltac:(lia_std) Hh) as Hsh.
  assert (Hl1 : 0 <= Z.land hold1 1 < 2) by (rewrite land1_mod by lia_std; Z.to_euclidean_division_equations; lia_std).
  split.
  - split; [| split; [exact W | split]].
    + unfold RNG, typedo_st; icx_cbn. split_conj; try assumption; try lia_std.
      * destruct fx; [lia_std | assumption].
      * destruct fx; [lia_std | assumption].
      * destruct fx; [lia_std | assumption].
      * destruct fx; [lia_std | assumption].
      * destruct fx; [exact I | assumption].
      * destruct fx; [exact I | assumption].
    + unfold PROG, typedo_st, Wm in *; icx_cbn. mode_consts. lia_std.
    + pose proof (proj1 (proj2 Mo)) as Mf. clear Mo W P. unfold MODE, typedo_st; icx_cbn. mode_consts.
      mode_solve Mf ltac:(intros Hlv; assert (m = 16199) by lia_std; assert (Efx : fx = true) by (apply Hfx; assumption); subst fx;
                          unfold tables_live; cbn; split; reflexivity).
  - apply meas_dec_W. unfold Wm, typedo_st; icx_cbn. lia_std.
Qed.

