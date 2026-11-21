(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz LmatchModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma swrap32_mod64 : forall x c, - 2^31 <= x + c < 2^31 -> bv_swrap 32 (x mod 18446744073709551616 + c) = x + c.
Proof.
  intros x c H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (2 ^ 31) with 2147483648 in H. change (4294967296 / 2) with 2147483648. Z.div_mod_to_equations. lia.
Qed.

Lemma limit_mask : forall ss ws, 0 <= ss < 2^31 -> 262 < ws < 2^31 ->
  Z.land (bv_swrap 32 (Z.b2z (ss <? bv_swrap 32 ((ss - ws) mod 18446744073709551616 + 262) mod 18446744073709551616) + -1) mod 18446744073709551616)
         (bv_swrap 32 ((ss - ws) mod 18446744073709551616 + 262) mod 18446744073709551616)
  = (if ws - 262 <? ss then ss - (ws - 262) else 0).
Proof.
  intros ss ws Hs Hw. change (2^31) with 2147483648 in *.
  rewrite swrap32_mod64 by (change (2^31) with 2147483648; lia).
  destruct (Z.ltb_spec (ws - 262) ss) as [H|H].
  - rewrite (Z.mod_small (ss - ws + 262)) by lia.
    replace (ss <? ss - ws + 262) with false by (symmetry; apply Z.ltb_ge; lia).
    change (bv_swrap 32 (Z.b2z false + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    rewrite Z.mod_small; lia.
  - destruct (Z.eq_dec (ss - ws + 262) 0) as [E|NE].
    + rewrite E. change (0 mod 18446744073709551616) with 0. rewrite Z.land_0_r. lia.
    + assert (E : (ss - ws + 262) mod 18446744073709551616 = ss - ws + 262 + 18446744073709551616) by (Z.div_mod_to_equations; lia).
      rewrite E.
      replace (ss <? ss - ws + 262 + 18446744073709551616) with true by (symmetry; apply Z.ltb_lt; lia).
      change (bv_swrap 32 (Z.b2z true + -1) mod 18446744073709551616) with 0. apply Z.land_0_l.
Qed.

Definition lm_next (P : arr) (wmask limit : Z) (s : deflate_state) (cur chain best se1 se : Z)
  : deflate_state * Z * Z * Z * Z * Z * bool :=
  let cur' := arr_get P (Z.land cur wmask) in
  if limit <? cur' then
    let ch' := wrap32 (chain - 1) in
    if negb (ch' =? 0) then (s, best, se1, se, cur', ch', true) else (s, best, se1, se, cur', ch', false)
  else (s, best, se1, se, cur', chain, false).

Definition lm_early (W : arr) (ss cur best se1 se : Z) : bool :=
  negb (arr_get W (cur + best) =? se) || negb (arr_get W (cur + best - 1) =? se1)
  || negb (arr_get W cur =? arr_get W ss) || negb (arr_get W (cur + 1) =? arr_get W (ss + 1)).

Definition lm_len (W : arr) (ss cur : Z) : Z := lm_cmp_loop 33%nat W (ss + 2) (cur + 2) (ss + 258) - ss.

Lemma lm_body_eq : forall s cur chain best nice limit se1 se,
  longest_match_body s cur chain best nice limit se1 se =
  (let W := ds_window s in let ss := ds_strstart s in
   if lm_early W ss cur best se1 se then lm_next (ds_prev s) (ds_w_mask s) limit s cur chain best se1 se
   else let len := lm_len W ss cur in
        if best <? len then
          if nice <=? len then (set_match_start s cur, len, se1, se, cur, chain, false)
          else lm_next (ds_prev s) (ds_w_mask s) limit (set_match_start s cur) cur chain len (arr_get W (ss + len - 1)) (arr_get W (ss + len))
        else lm_next (ds_prev s) (ds_w_mask s) limit s cur chain best se1 se).
Proof.
  intros. unfold longest_match_body, lm_early, lm_len, lm_next, MAX_MATCH. cbv zeta.
  destruct (_ || _); [reflexivity|].
  replace (258 - (ds_strstart s + 258 - lm_cmp_loop 33 (ds_window s) (ds_strstart s + 2) (cur + 2) (ds_strstart s + 258)))
    with (lm_cmp_loop 33 (ds_window s) (ds_strstart s + 2) (cur + 2) (ds_strstart s + 258) - ds_strstart s) by lia.
  destruct (_ <? _); [|reflexivity].
  destruct (_ <=? _); reflexivity.
Qed.

Definition lm_restG {A} (K : deflate_state -> Z -> Z -> Z -> Z -> Z -> A) (stop : deflate_state -> Z -> A)
    (P : arr) (wm limit : Z) (s : deflate_state) (cur chain b e1 e : Z) : A :=
  let cur' := arr_get P (Z.land cur wm) in
  if limit <? cur' then
    let ch' := wrap32 (chain - 1) in
    if negb (ch' =? 0) then K s cur' ch' b e1 e else stop s b
  else stop s b.

Definition lm_tripG {A} (K : deflate_state -> Z -> Z -> Z -> Z -> Z -> A) (stop : deflate_state -> Z -> A)
    (s : deflate_state) (cur chain best nice limit se1 se : Z) : A :=
  let W := ds_window s in let ss := ds_strstart s in
  if lm_early W ss cur best se1 se then lm_restG K stop (ds_prev s) (ds_w_mask s) limit s cur chain best se1 se
  else let len := lm_len W ss cur in
       if best <? len then
         if nice <=? len then stop (set_match_start s cur) len
         else lm_restG K stop (ds_prev s) (ds_w_mask s) limit (set_match_start s cur) cur chain len (arr_get W (ss + len - 1)) (arr_get W (ss + len))
       else lm_restG K stop (ds_prev s) (ds_w_mask s) limit s cur chain best se1 se.

Lemma lm_loop_S : forall f s cur chain best nice limit se1 se,
  longest_match_loop (S f) s cur chain best nice limit se1 se
  = lm_tripG (fun s' c ch b e1 e => longest_match_loop f s' c ch b nice limit e1 e) (fun s' b => (s', b)) s cur chain best nice limit se1 se.
Proof.
  intros. cbn [longest_match_loop]. rewrite lm_body_eq. unfold lm_tripG, lm_restG, lm_next. cbv zeta.
  destruct (lm_early _ _ _ _ _ _).
  - destruct (_ <? _); [destruct (negb _)|]; reflexivity.
  - destruct (best <? _); [destruct (nice <=? _); [reflexivity|]|]; (destruct (_ <? _); [destruct (negb _)|]; reflexivity).
Qed.

Lemma lm_curs_S : forall f s cur chain best nice limit se1 se,
  lm_curs (S f) s cur chain best nice limit se1 se
  = cur :: lm_tripG (fun s' c ch b e1 e => lm_curs f s' c ch b nice limit e1 e) (fun _ _ => []) s cur chain best nice limit se1 se.
Proof.
  intros. cbn [lm_curs]. rewrite lm_body_eq. unfold lm_tripG, lm_restG, lm_next. cbv zeta. f_equal.
  destruct (lm_early _ _ _ _ _ _).
  - destruct (_ <? _); [destruct (negb _)|]; reflexivity.
  - destruct (best <? _); [destruct (nice <=? _); [reflexivity|]|]; (destruct (_ <? _); [destruct (negb _)|]; reflexivity).
Qed.

Lemma lm_len_bound : forall W ss cur, 3 <= lm_len W ss cur + 1 /\ lm_len W ss cur <= 258.
Proof.
  intros W ss cur. unfold lm_len.
  pose proof (lm_cmp_loop_bound 33 W (ss + 2) (cur + 2) (ss + 258) ltac:(lia)) as B.
  replace (ss + 258 - (ss + 2)) with 256 in B by lia. specialize (B eq_refl). lia.
Qed.

Lemma cmpk_mis : forall k W sc mt j, (1 <= j <= k)%nat ->
  (forall t, 1 <= t < Z.of_nat j -> arr_get W (sc + t) = arr_get W (mt + t)) ->
  arr_get W (sc + Z.of_nat j) <> arr_get W (mt + Z.of_nat j) ->
  lm_cmpk k W sc mt = (sc + Z.of_nat j, mt + Z.of_nat j, false).
Proof.
  induction k as [|k IH]; intros W sc mt j Hj HE HN; [lia|]. cbn [lm_cmpk].
  destruct (Nat.eq_dec j 1) as [->|NJ].
  - change (Z.of_nat 1) with 1 in *. destruct (Z.eqb_spec (arr_get W (sc + 1)) (arr_get W (mt + 1))); [contradiction|reflexivity].
  - rewrite (proj2 (Z.eqb_eq _ _) (HE 1 ltac:(lia))).
    rewrite (IH W (sc + 1) (mt + 1) (j - 1)%nat ltac:(lia)).
    + f_equal; f_equal; lia.
    + intros t Ht. replace (sc + 1 + t) with (sc + (t + 1)) by lia. replace (mt + 1 + t) with (mt + (t + 1)) by lia. apply HE. lia.
    + replace (sc + 1 + Z.of_nat (j - 1)) with (sc + Z.of_nat j) by lia. replace (mt + 1 + Z.of_nat (j - 1)) with (mt + Z.of_nat j) by lia. exact HN.
Qed.

Lemma cmpk_all : forall k W sc mt,
  (forall t, 1 <= t <= Z.of_nat k -> arr_get W (sc + t) = arr_get W (mt + t)) ->
  lm_cmpk k W sc mt = (sc + Z.of_nat k, mt + Z.of_nat k, true).
Proof.
  induction k as [|k IH]; intros W sc mt HE; cbn [lm_cmpk]; [f_equal; f_equal; lia|].
  rewrite (proj2 (Z.eqb_eq _ _) (HE 1 ltac:(lia))). rewrite IH.
  - f_equal; f_equal; lia.
  - intros t Ht. replace (sc + 1 + t) with (sc + (t + 1)) by lia. replace (mt + 1 + t) with (mt + (t + 1)) by lia. apply HE. lia.
Qed.

Lemma cmp_round_mis : forall f W ss cur i j, (1 <= j <= 8)%nat ->
  (forall t, 1 <= t < Z.of_nat j -> arr_get W (ss + 2 + i + t) = arr_get W (cur + 2 + i + t)) ->
  arr_get W (ss + 2 + i + Z.of_nat j) <> arr_get W (cur + 2 + i + Z.of_nat j) ->
  lm_cmp_loop (S f) W (ss + 2 + i) (cur + 2 + i) (ss + 258) = ss + 2 + i + Z.of_nat j.
Proof. intros f W ss cur i j Hj HE HN. cbn [lm_cmp_loop]. rewrite (cmpk_mis 8 W _ _ j Hj HE HN). reflexivity. Qed.

Lemma cmp_round_all : forall f W ss cur i,
  (forall t, 1 <= t <= 8 -> arr_get W (ss + 2 + i + t) = arr_get W (cur + 2 + i + t)) ->
  lm_cmp_loop (S f) W (ss + 2 + i) (cur + 2 + i) (ss + 258)
  = if i + 10 <? 258 then lm_cmp_loop f W (ss + 2 + (i + 8)) (cur + 2 + (i + 8)) (ss + 258) else ss + 2 + i + 8.
Proof.
  intros f W ss cur i HE. cbn [lm_cmp_loop]. rewrite (cmpk_all 8 W _ _ HE). change (Z.of_nat 8) with 8. cbn [andb].
  replace (ss + 2 + i + 8 <? ss + 258) with (i + 10 <? 258) by (destruct (Z.ltb_spec (i + 10) 258); destruct (Z.ltb_spec (ss + 2 + i + 8) (ss + 258)); lia).
  destruct (i + 10 <? 258); [|reflexivity]. f_equal; lia.
Qed.
