(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import InfPure InfPure_type.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma land24 : forall b, 0 <= b < 32 -> Z.land b 24 = b - b mod 8.
Proof.
  intros b Hb. rewrite <- landm8 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z_lt_le_dec i 5) as [L|L].
  - f_equal. destruct (Z.eq_dec i 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec i 1) as [->|]; [reflexivity|].
    destruct (Z.eq_dec i 2) as [->|]; [reflexivity|]. destruct (Z.eq_dec i 3) as [->|]; [reflexivity|].
    replace i with 4 by lia. reflexivity.
  - replace (Z.testbit b i) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|].
    apply Z.lt_le_trans with 5; [| lia]. apply Z.log2_lt_pow2; [lia|]. change (2 ^ 5) with 32. lia.
Qed.
Lemma low16_of_shift : forall h, 0 <= h < 18446744073709551616 ->
  Z.shiftr (Z.shiftl h 48 mod 18446744073709551616) 48 = h mod 65536.
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 48) with 281474976710656. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition set_st (st : ist) (m cin cout hold bits len : Z) : ist :=
  IST m (t_last st) (t_flags st) cin cout hold bits (t_out st) (t_ret st)
      len (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma flags_not_m1 : forall cx st lf cf, sinv cx st lf cf -> t_mode st <> HEAD -> t_mode st <> BAD -> t_flags st <> -1.
Proof. intros cx st lf cf (_ & _ & _ & Mo) H1 H2 Hf. destruct (proj1 (proj2 Mo) Hf) as [[E|E] _]; congruence. Qed.

Lemma sinv_set : forall cx st lf cf m cin cout hold bits len,
  sinv cx st lf cf -> t_flags st <> -1 -> (t_mode st <? CHECK) = true ->
  (m = TYPE \/ m = STORED \/ m = COPY_ \/ m = COPY \/ m = BAD) ->
  ((m = COPY_ \/ m = COPY) -> len < 65536) ->
  t_cin st <= cin <= c_n cx -> t_cout st <= cout <= c_osz cx ->
  0 <= bits <= 40 -> 0 <= hold < 2 ^ bits -> bits <= 8 * cin -> 0 <= len < 4294967296 ->
  8 * (c_n cx - cin) + bits + (c_osz cx - cout) + (cout - t_cout st) <= Wm cx st ->
  sinv cx (set_st st m cin cout hold bits len) lf cf.
Proof.
  intros cx st lf cf m cin cout hold bits len (R & W & P & Mo) Hfl Hlt Hm Hlen Hc Ho Hb Hh Hbc Hl HW. apply Z.ltb_lt in Hlt.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin' cout' hold' bits' out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_cin t_cout t_flags] in *. icx_cbn. unfold Wm in HW. icx_cbn.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [| split; [exact W | split]].
  - unfold RNG, set_st; icx_cbn. split_conj; try assumption; try lia_std.
  - unfold PROG, set_st, Wm in *; icx_cbn. cbn [t_mode] in Hlt. mode_consts. lia_std.
  - pose proof (proj1 (proj2 Mo)) as Mf. clear Mo W P. unfold MODE, set_st; icx_cbn. mode_consts.
    mode_solve Mf ltac:(intros X; split_conj; lia_std).
Qed.

Lemma meas_set : forall cx st m cin cout hold bits len,
  8 * (c_n cx - cin) + bits + (c_osz cx - cout) < Wm cx st \/
  (8 * (c_n cx - cin) + bits + (c_osz cx - cout) <= Wm cx st /\ rank m < rank (t_mode st)) ->
  meas cx (set_st st m cin cout hold bits len) < meas cx st.
Proof.
  intros cx st m cin cout hold bits len H.
  destruct H as [H | [H1 H2]].
  - apply meas_dec_W. unfold Wm, set_st in *. destruct cx, st; icx_cbn. cbn in *. lia_std.
  - apply meas_dec_rank; [| unfold set_st; cbn; exact H2]. unfold Wm, set_st in *. destruct cx, st; icx_cbn. cbn in *. lia_std.
Qed.

Lemma copy_len_bound : forall cx st lf cf, sinv cx st lf cf -> (t_mode st = COPY_ \/ t_mode st = COPY) -> t_length st < 65536.
Proof.
  intros cx st lf cf (_ & _ & _ & Mo) Hm. unfold MODE in Mo. destr_conj Mo.
  match goal with H : t_mode st = COPY_ \/ t_mode st = COPY -> _ |- _ => exact (H Hm) end.
Qed.
