(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_dview.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface InflateState RefUpdWin1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition uw_set (s : inflate_state) (win : arr) (wsize wnext whave : Z) : inflate_state :=
  iset_whave (iset_wnext (iset_wsize (iset_window s win) wsize) wnext) whave.

Lemma updw_core_shape : forall s src e copy,
  let s' := updw_core s src e copy in
  s' = uw_set s (is_window s') (is_wsize s') (is_wnext s') (is_whave s').
Proof.
  intros s src e copy. cbv zeta. unfold updw_core, sA, uw_set. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] =>
           lazymatch c with context [if _ then _ else _] => fail | _ => destruct c end end;
  destruct s; reflexivity.
Qed.

Definition uw_wsize (s : inflate_state) : Z := if is_wsize s =? 0 then 32768 else is_wsize s.
Definition uw_wnext0 (s : inflate_state) : Z := if is_wsize s =? 0 then 0 else is_wnext s.
Definition uw_whave0 (s : inflate_state) : Z := if is_wsize s =? 0 then 0 else is_whave s.

Lemma updw_small : forall s src e copy,
  is_wbits s = 15 -> 0 <= copy <= 1 ->
  (is_wsize s <> 0 -> is_wsize s = 32768) -> 0 <= uw_wnext0 s < 32768 -> 0 <= uw_whave0 s <= 32768 ->
  updw_core s src e copy
  = uw_set s (arr_blit (is_window s) (uw_wnext0 s) src (e - copy) copy) 32768
           (if uw_wnext0 s + copy =? 32768 then 0 else uw_wnext0 s + copy)
           (if uw_whave0 s <? 32768 then uw_whave0 s + copy else uw_whave0 s).
Proof.
  intros s src e copy Hb Hc Hws Hwn Hwh. unfold updw_core, sA, uw_set, uw_wnext0, uw_whave0 in *. cbv zeta.
  destruct (Z.eqb_spec (is_wsize s) 0) as [E0|NE0].
  -
    rewrite Hb. change (shl32 1 15) with 32768.
    cbn [is_wsize is_wnext is_whave is_window iset_whave iset_wnext iset_wsize iset_window].
    replace (32768 <=? copy) with false by (symmetry; apply Z.leb_gt; lia).
    change (wrap32 (32768 - 0)) with 32768. replace (copy <? 32768) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite Z.sub_diag. change (wrap32 0) with 0. change (negb (0 =? 0)) with false. cbv iota.
    cbn [is_wsize is_wnext is_whave is_window iset_whave iset_wnext iset_wsize iset_window].
    rewrite !wrap32_id by lia. rewrite !Z.add_0_l.
    replace (copy =? 32768) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [is_wsize is_wnext is_whave is_window iset_whave iset_wnext iset_wsize iset_window].
    change (0 <? 32768) with true. cbv iota. rewrite Z.add_0_l. rewrite !wrap32_id by lia. destruct s; reflexivity.
  - specialize (Hws NE0). rewrite Hws in *.
    replace (32768 <=? copy) with false by (symmetry; apply Z.leb_gt; lia).
    rewrite (wrap32_id (32768 - is_wnext s)) by lia.
    assert (ED : (if copy <? 32768 - is_wnext s then copy else 32768 - is_wnext s) = copy).
    { destruct (Z.ltb_spec copy (32768 - is_wnext s)); lia. }
    rewrite ED. rewrite Z.sub_diag. change (wrap32 0) with 0. change (negb (0 =? 0)) with false. cbv iota.
    cbn [is_wsize is_wnext is_whave is_window iset_whave iset_wnext iset_wsize iset_window].
    rewrite ?Hws. rewrite (wrap32_id (is_wnext s + copy)) by lia.
    destruct (is_wnext s + copy =? 32768);
      cbn [is_wsize is_wnext is_whave is_window iset_whave iset_wnext iset_wsize iset_window]; rewrite ?Hws;
      (destruct (Z.ltb_spec (is_whave s) 32768); [rewrite (wrap32_id (is_whave s + copy)) by lia|]);
      destruct s; cbn in *; subst; reflexivity.
Qed.

Lemma sA_idem : forall s, is_wbits s = 15 -> sA (sA s) = sA s.
Proof.
  intros s Hb. unfold sA at 1. destruct (Z.eqb_spec (is_wsize (sA s)) 0) as [E|NE]; [|reflexivity].
  exfalso. unfold sA in E. destruct (Z.eqb_spec (is_wsize s) 0) as [E0|NE0]; [|contradiction].
  cbn in E. rewrite Hb in E. discriminate E.
Qed.
Lemma updw_core_sA : forall s src e copy, is_wbits s = 15 -> updw_core s src e copy = updw_core (sA s) src e copy.
Proof. intros s src e copy Hb. unfold updw_core. rewrite (sA_idem s Hb). reflexivity. Qed.

Lemma av8_blit : forall (w src : arr) k so n N, 0 <= k -> 0 <= n -> k + n <= N -> N <= arr_len w ->
  firstn (Z.to_nat k) (av8 w N) ++ map (Z_to_bv 8) (arr_slice src so n) ++ skipn (Z.to_nat k + Z.to_nat n) (av8 w N)
  = av8 (arr_blit w k src so n) N.
Proof.
  intros w src k so n N Hk Hn HN HL.
  assert (LS : length (arr_slice src so n) = Z.to_nat n) by (unfold arr_slice; apply arr_slice_nat_length).
  apply list_ext_nth.
  - rewrite !length_app, length_firstn, length_skipn, length_map, !av8_length, LS. lia.
  - intros i Hi. rewrite !length_app, length_firstn, length_skipn, length_map, !av8_length, LS in Hi.
    assert (Ri : 0 <= Z.of_nat i < N) by lia.
    replace i with (Z.to_nat (Z.of_nat i)) at 2 by lia. rewrite (av8_nth _ N (Z.of_nat i)) by lia.
    rewrite arr_get_blit. unfold arr_inb.
    destruct (Nat.lt_ge_cases i (Z.to_nat k)) as [H1|H1].
    + rewrite nth_error_app1 by (rewrite length_firstn, av8_length; lia).
      rewrite nth_error_firstn. replace (i <? Z.to_nat k)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
      replace i with (Z.to_nat (Z.of_nat i)) at 1 by lia. rewrite (av8_nth _ N (Z.of_nat i)) by lia.
      replace (k <=? Z.of_nat i) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    + rewrite nth_error_app2 by (rewrite length_firstn, av8_length; lia). rewrite length_firstn, av8_length.
      replace (Nat.min (Z.to_nat k) (Z.to_nat N)) with (Z.to_nat k) by lia.
      destruct (Nat.lt_ge_cases (i - Z.to_nat k) (Z.to_nat n)) as [H2|H2].
      * rewrite nth_error_app1 by (rewrite length_map, LS; lia). rewrite nth_error_map.
        unfold arr_slice. rewrite arr_slice_nat_nth_error by lia. cbn [option_map].
        replace (k <=? Z.of_nat i) with true by (symmetry; apply Z.leb_le; lia).
        replace (Z.of_nat i <? k + Z.max 0 n) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (0 <=? Z.of_nat i) with true by (symmetry; apply Z.leb_le; lia).
        replace (Z.of_nat i <? arr_len w) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
        do 3 f_equal. lia.
      * rewrite nth_error_app2 by (rewrite length_map, LS; lia). rewrite length_map, LS, nth_error_skipn.
        replace (Z.to_nat k + Z.to_nat n + (i - Z.to_nat k - Z.to_nat n))%nat with (Z.to_nat (Z.of_nat i)) by lia.
        rewrite (av8_nth _ N (Z.of_nat i)) by lia.
        replace (Z.of_nat i <? k + Z.max 0 n) with false by (symmetry; apply Z.ltb_ge; lia).
        rewrite andb_false_r. cbn [andb]. reflexivity.
Qed.

Lemma arr_len_blit : forall (w src : arr) k so n, arr_len (arr_blit w k src so n) = arr_len w.
Proof.
  intros w src k so n. unfold arr_blit. generalize (Z.to_nat n) as j. intros j. revert w k so.
  induction j as [|j IH]; intros w k so; cbn [arr_blit_nat]; [reflexivity|]. rewrite IH. apply arr_len_set.
Qed.

Definition gwb (junk : list byte) : Z -> Z := fun i => bv_unsigned (nth (Z.to_nat i) junk (Z_to_bv 8 0)).

Lemma av8_junk : forall (junk : list byte) n, Z.of_nat (length junk) = n ->
  av8 (iarr_u8_of (gwb junk) 0 n) n = junk.
Proof.
  intros junk n Hn. apply list_ext_nth.
  - rewrite av8_length. lia.
  - intros i Hi. rewrite av8_length in Hi.
    replace i with (Z.to_nat (Z.of_nat i)) at 1 by lia. rewrite (av8_nth _ n (Z.of_nat i)) by lia.
    unfold iarr_u8_of. rewrite arr_get_init. unfold init_u8, gwb. rewrite Z.add_0_l, Nat2Z.id.
    rewrite (nth_error_nth' junk (Z_to_bv 8 0)) by lia. f_equal.
    pose proof (bv_unsigned_in_range 8 (nth i junk (Z_to_bv 8 0))) as R. change (bv_modulus 8) with 256 in R.
    rewrite wrap8_mod. change (2 ^ 8) with 256. rewrite Z.mod_small by lia.
    apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma junk_bytes : forall (junk : list byte) i, 0 <= init_u8 (gwb junk) 0 i < 256.
Proof. intros junk i. unfold init_u8. pose proof (wrap8_range (gwb junk (0 + i))) as H. change (2 ^ 8) with 256 in H. exact H. Qed.
