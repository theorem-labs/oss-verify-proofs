(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_dview Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_updwin_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface ZChkAdl ZChecksum AdlerModel DeflateLz InflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma bZ_av8 : forall a n, 0 <= n -> (forall i, 0 <= i < n -> 0 <= arr_get a i < 256) -> bZ (av8 a n) = arr_slice a 0 n.
Proof.
  intros a n Hn Hb. unfold bZ, arr_slice.
  apply (nth_ext _ _ 0 0).
  - rewrite length_map, av8_length, arr_slice_nat_length. reflexivity.
  - intros k Hk. rewrite length_map, av8_length in Hk.
    rewrite arr_slice_nat_nth by exact Hk. rewrite Z.add_0_l.
    assert (E : nth_error (map bv_unsigned (av8 a n)) k = Some (arr_get a (Z.of_nat k))).
    { rewrite nth_error_map. replace k with (Z.to_nat (Z.of_nat k)) at 1 by lia. rewrite (av8_nth a n (Z.of_nat k)) by lia. cbn [option_map].
      f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
      apply Z.mod_small. apply Hb. lia. }
    apply nth_error_nth. exact E.
Qed.

Lemma adler32_z_spec_any : forall a P d, adler_canon a -> P <> 0 -> adler32_z_spec a P d = adler32_model a (bZ d).
Proof.
  intros a P d Ha HP.
  destruct (Z.eq_dec (Z.of_nat (length d)) 1) as [E1|NE1].
  - destruct d as [|b [|b' d']]; cbn [length] in E1; try lia.
    change (bZ [b]) with [bv_unsigned b].
    pose proof (bv_unsigned_in_range _ b) as Rb. unfold bv_modulus in Rb. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul two_power_nat shift_nat nat_rect] in Rb.
    assert (Rb' : 0 <= bv_unsigned b < 256) by (cbn in Rb; lia).
    rewrite (adler32_model_len1 a (bv_unsigned b) Ha Rb').
    unfold adler32_z_spec, adler32_len1, lo16, hi16, csub, adler_csub, bnth. cbn [length Z.of_nat Pos.of_succ_nat Z.eqb Pos.eqb nth].
    reflexivity.
  - apply adler32_z_spec_model; [destruct Ha as [[H _] _]; exact H| exact NE1| exact HP].
Qed.

#[local] Transparent iout_bytes.
Lemma iout_prefix_bytes : forall m L rest0 c put, iout m L rest0 c put -> 0 <= put <= Z.of_nat (length rest0) ->
  bytes_at psegs m (il_NO L) (av8 (ic_outbuf c) put).
Proof.
  intros m L rest0 c put H Hp. unfold iout in H.
  pose proof (u8arr_sub_bytes m _ _ 0 (Z.to_nat put) H) as HB.
  rewrite Nat2Z.inj_0, Z.add_0_r in HB. cbn [skipn] in HB.
  unfold iout_bytes in HB. rewrite firstn_app, av8_length, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in HB by (rewrite av8_length; lia).
  apply HB. rewrite length_app, av8_length, length_skipn. lia.
Qed.
#[local] Opaque iout_bytes.


Lemma av8_sub : forall a N so n, 0 <= so -> 0 <= n -> so + n <= N ->
  firstn (Z.to_nat n) (skipn (Z.to_nat so) (av8 a N)) = map (Z_to_bv 8) (arr_slice a so n).
Proof.
  intros a N so n Hso Hn Hle. unfold arr_slice.
  apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)).
  - rewrite length_firstn, length_skipn, av8_length, length_map, arr_slice_nat_length. lia.
  - intros k Hk. rewrite length_firstn, length_skipn, av8_length in Hk.
    rewrite (map_nth (Z_to_bv 8)). rewrite arr_slice_nat_nth by lia.
    rewrite nth_firstn. replace ((k <? Z.to_nat n)%nat) with true by (symmetry; apply Nat.ltb_lt; lia). cbv iota. rewrite nth_skipn.
    apply nth_error_nth. replace (Z.to_nat so + k)%nat with (Z.to_nat (so + Z.of_nat k)) by lia. rewrite av8_nth by lia. reflexivity.
Qed.

Lemma av8_prefix : forall a p N, 0 <= p <= N -> firstn (Z.to_nat p) (av8 a N) = av8 a p.
Proof.
  intros a p N Hp. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)).
  - rewrite length_firstn, !av8_length. lia.
  - intros k Hk. rewrite length_firstn, av8_length in Hk. rewrite nth_firstn. replace ((k <? Z.to_nat p)%nat) with true by (symmetry; apply Nat.ltb_lt; lia). cbv iota.
    pose proof (av8_nth a N (Z.of_nat k) ltac:(lia)) as E1. pose proof (av8_nth a p (Z.of_nat k) ltac:(lia)) as E2.
    rewrite Nat2Z.id in E1, E2.
    rewrite (nth_error_nth _ _ _ E1), (nth_error_nth _ _ _ E2). reflexivity.
Qed.

#[local] Transparent iout_bytes.
Lemma iout_bytes_blit : forall rest0 c (src : arr) so put n,
  0 <= put -> 0 <= n -> put + n <= Z.of_nat (length rest0) -> put + n <= arr_len (ic_outbuf c) ->
  iout_bytes rest0 (icset_outbuf c (arr_blit (ic_outbuf c) put src so n)) (put + n)
  = firstn (Z.to_nat put) (iout_bytes rest0 c put) ++ map (Z_to_bv 8) (arr_slice src so n)
    ++ skipn (Z.to_nat put + Z.to_nat n) (iout_bytes rest0 c put).
Proof.
  intros rest0 c src so put n Hp Hn HR HA. unfold iout_bytes. cbn [ic_outbuf icset_outbuf].
  rewrite <- (av8_blit (ic_outbuf c) src put so n (put + n)) by lia.
  rewrite firstn_app, av8_length, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite (av8_prefix (ic_outbuf c) put (put + n)) by lia.
  rewrite firstn_all2 by (rewrite av8_length; lia).
  rewrite (skipn_all2 (av8 (ic_outbuf c) (put + n))) by (rewrite av8_length; lia).
  rewrite (skipn_app (Z.to_nat put + Z.to_nat n)), av8_length.
  rewrite (skipn_all2 (av8 (ic_outbuf c) put)) by (rewrite av8_length; lia).
  cbn [app]. rewrite <- !app_assoc. f_equal. f_equal.
  cbn [app]. rewrite skipn_skipn. f_equal. lia.
Qed.
#[local] Opaque iout_bytes.
