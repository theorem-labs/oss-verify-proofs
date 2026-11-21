(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition wb (w : arr) (i : Z) : Z := (arr_get w i) mod 256.
Definition pb (p : arr) (i : Z) : Z := (arr_get p i) mod 65536.

Lemma wb_range : forall w i, 0 <= wb w i < 256.
Proof. intros. unfold wb. apply Z.mod_pos_bound. lia. Qed.
Lemma pb_range : forall p i, 0 <= pb p i < 65536.
Proof. intros. unfold pb. apply Z.mod_pos_bound. lia. Qed.

Lemma wb_eqI : forall w i j, arr_get w i = arr_get w j -> wb w i = wb w j.
Proof. intros w i j E. unfold wb. rewrite E. reflexivity. Qed.

Section ArrFacts.
  Variable w : arr.
Variable pv : arr.
  Hypothesis Hwb : forall i, 0 <= i < arr_len w -> 0 <= arr_get w i < 256.
  Hypothesis Hpb : forall i, 0 <= i < arr_len pv -> 0 <= arr_get pv i < 65536.

  Lemma wb_neI : forall i j, 0 <= i < arr_len w -> 0 <= j < arr_len w ->
    arr_get w i <> arr_get w j -> wb w i <> wb w j.
  Proof. intros i j Hi Hj N. unfold wb. rewrite !Z.mod_small by (apply Hwb; lia). exact N. Qed.

  Lemma wb_get : forall i, 0 <= i < arr_len w -> wb w i = arr_get w i.
  Proof. intros i Hi. unfold wb. apply Z.mod_small. apply Hwb. exact Hi. Qed.

  Lemma pb_get : forall i, 0 <= i < arr_len pv -> pb pv i = arr_get pv i.
  Proof. intros i Hi. unfold pb. apply Z.mod_small. apply Hpb. exact Hi. Qed.
End ArrFacts.

Fixpoint lm_curs (fuel : nat) (s : deflate_state)
  (cur_match chain_length best_len nice_match limit scan_end1 scan_end : Z) : list Z :=
  cur_match ::
  match fuel with
  | O => []
  | S f =>
      let '(s', b', se1', se', cur', ch', cont) :=
        longest_match_body s cur_match chain_length best_len nice_match limit scan_end1 scan_end in
      if cont then lm_curs f s' cur' ch' b' nice_match limit se1' se' else []
  end.

Definition lm_visited (ds : deflate_state) (cur : Z) : list Z :=
  let pl := ds_prev_length ds in
  let mc := ds_max_chain_length ds in
  let chain := if ds_good_match ds <=? pl then Z.shiftr mc 2 else mc in
  let nice := if ds_lookahead ds <? ds_nice_match ds then ds_lookahead ds else ds_nice_match ds in
  let limit := if ds_w_size ds - MIN_LOOKAHEAD <? ds_strstart ds
               then ds_strstart ds - (ds_w_size ds - MIN_LOOKAHEAD) else NIL in
  lm_curs (Z.to_nat chain) ds cur chain pl nice limit
          (arr_get (ds_window ds) (ds_strstart ds + pl - 1))
          (arr_get (ds_window ds) (ds_strstart ds + pl)).

Lemma lm_cmpk_true : forall k wa sc mt sc' mt',
  lm_cmpk k wa sc mt = (sc', mt', true) -> sc' = sc + Z.of_nat k /\ mt' = mt + Z.of_nat k.
Proof.
  induction k as [|k IH]; intros wa sc mt sc' mt' H; cbn [lm_cmpk] in H.
  - injection H as <- <-. lia.
  - destruct (arr_get wa (sc + 1) =? arr_get wa (mt + 1)); [|discriminate].
    apply IH in H. lia.
Qed.

Lemma lm_cmpk_bound : forall k wa sc mt sc' mt' ok,
  lm_cmpk k wa sc mt = (sc', mt', ok) -> sc <= sc' <= sc + Z.of_nat k /\ mt' - mt = sc' - sc.
Proof.
  induction k as [|k IH]; intros wa sc mt sc' mt' ok H; cbn [lm_cmpk] in H.
  - injection H as <- <- <-. lia.
  - destruct (arr_get wa (sc + 1) =? arr_get wa (mt + 1)).
    + apply IH in H. lia.
    + injection H as <- <- <-. lia.
Qed.

Lemma lm_cmp_loop_bound : forall n wa sc mt se,
  sc + 8 <= se -> (se - sc) mod 8 = 0 -> sc <= lm_cmp_loop n wa sc mt se <= se.
Proof.
  induction n as [|n IH]; intros wa sc mt se H1 H2; cbn [lm_cmp_loop]; [lia|].
  destruct (lm_cmpk 8 wa sc mt) as [[sc' mt'] ok] eqn:Hk.
  pose proof (lm_cmpk_bound _ _ _ _ _ _ _ Hk) as Hb. change (Z.of_nat 8) with 8 in Hb.
  destruct ok; cbn [andb]; [|lia].
  destruct (lm_cmpk_true _ _ _ _ _ _ Hk) as [-> ->]. change (Z.of_nat 8) with 8 in *.
  destruct (Z.ltb_spec (sc + 8) se); [|lia].
  assert (Hm8 : (se - (sc + 8)) mod 8 = 0).
  { replace (se - (sc + 8)) with (se - sc - 8) by lia. rewrite Zminus_mod, H2. reflexivity. }
  assert (sc + 8 + 8 <= se).
  { assert (E : se - sc - 8 = 8 * ((se - sc - 8) / 8)).
    { pose proof (Z.div_mod (se - sc - 8) 8 ltac:(lia)). replace (se - (sc + 8)) with (se - sc - 8) in Hm8 by lia. lia. }
    assert (0 < (se - sc - 8) / 8) by lia. lia. }
  specialize (IH wa (sc + 8) (mt + 8) se ltac:(lia) Hm8). lia.
Qed.

Lemma set_ms_twice : forall s a b, set_match_start (set_match_start s a) b = set_match_start s b.
Proof. intros. reflexivity. Qed.
Lemma set_ms_self : forall s, set_match_start s (ds_match_start s) = s.
Proof. intros s. destruct s; reflexivity. Qed.
Lemma sms_window : forall s v, ds_window (set_match_start s v) = ds_window s. Proof. reflexivity. Qed.
Lemma sms_prev : forall s v, ds_prev (set_match_start s v) = ds_prev s. Proof. reflexivity. Qed.
Lemma sms_w_mask : forall s v, ds_w_mask (set_match_start s v) = ds_w_mask s. Proof. reflexivity. Qed.
Lemma sms_strstart : forall s v, ds_strstart (set_match_start s v) = ds_strstart s. Proof. reflexivity. Qed.
Lemma sms_lookahead : forall s v, ds_lookahead (set_match_start s v) = ds_lookahead s. Proof. reflexivity. Qed.

Lemma land_upper_both : forall a b, 0 <= a -> 0 <= b -> 0 <= Z.land a b <= b.
Proof.
  intros a b Ha Hb. split; [apply Z.land_nonneg; lia|].
  rewrite Z.land_comm.
  apply Z.ldiff_le; [lia|]. apply Z.bits_inj'. intros n Hn.
  rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
  destruct (Z.testbit b n), (Z.testbit a n); reflexivity.
Qed.
