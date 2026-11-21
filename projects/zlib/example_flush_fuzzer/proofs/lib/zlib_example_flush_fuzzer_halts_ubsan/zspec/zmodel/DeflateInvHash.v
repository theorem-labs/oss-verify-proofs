(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma land_mask_mod : forall p k, 0 <= k -> Z.land p (2 ^ k - 1) = p mod 2 ^ k.
Proof. intros p k Hk. replace (2 ^ k - 1) with (Z.ones k) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia). apply Z.land_ones. exact Hk. Qed.


Definition hc_inv (Ins : Z -> Prop) (str ws : Z) (head prev : arr) (hs : Z) : Prop :=
  (forall p, Ins p -> 0 <= p < str)
  /\ (forall h, 0 <= h < hs -> arr_get head h = 0 \/ Ins (arr_get head h))
  /\ (forall p, Ins p -> str - ws < p -> arr_get prev (p mod ws) = 0 \/ Ins (arr_get prev (p mod ws))).

Lemma hc_inv_empty : forall str ws head prev hs,
  (forall h, 0 <= h < hs -> arr_get head h = 0) -> hc_inv (fun _ => False) str ws head prev hs.
Proof.
  intros str ws head prev hs H. split; [intros p []|]. split; [intros h Hh; left; exact (H h Hh)|]. intros p [].
Qed.

Lemma hc_inv_str_le : forall Ins str str' ws head prev hs,
  hc_inv Ins str ws head prev hs -> str <= str' -> hc_inv Ins str' ws head prev hs.
Proof.
  intros Ins str str' ws head prev hs (H1 & H2 & H3) Hle.
  split; [intros p Hp; pose proof (H1 p Hp); lia|]. split; [exact H2|].
  intros p Hp Hq. apply (H3 p Hp). lia.
Qed.

Lemma hc_inv_insert : forall Ins str str' ws head prev hs h p,
  hc_inv Ins str ws head prev hs -> str <= str' -> 0 <= p < str' -> 0 <= h < hs -> wrap16 p = p ->
  0 <= p mod ws < arr_len prev -> h < arr_len head ->
  hc_inv (fun q => Ins q \/ q = p) str' ws
         (arr_set head h (wrap16 p)) (arr_set prev (p mod ws) (arr_get head h)) hs.
Proof.
  intros Ins str str' ws head prev hs h p (H1 & H2 & H3) Hle Hp Hh Hw16 Hpm Hhl.
  split.
  { intros q [Hq | ->]; [pose proof (H1 q Hq); lia | lia]. }
  split.
  { intros h' Hh'. destruct (Z.eq_dec h h') as [<-|Hne].
    - rewrite arr_get_set_same by lia. rewrite Hw16. right. right. reflexivity.
    - rewrite arr_get_set_other by exact Hne. destruct (H2 h' Hh') as [E|I]; [left; exact E | right; left; exact I]. }
  intros q Hq' Hq.
  destruct (Z.eq_dec (p mod ws) (q mod ws)) as [E|Hne].
  - rewrite <- E. rewrite arr_get_set_same by exact Hpm.
    destruct (H2 h Hh) as [E0 | I]; [left; exact E0 | right; left; exact I].
  - rewrite arr_get_set_other by exact Hne.
    destruct Hq' as [Hq' | ->]; [| exfalso; apply Hne; reflexivity].
    destruct (H3 q Hq' ltac:(lia)) as [E0 | I]; [left; exact E0 | right; left; exact I].
Qed.

Lemma hc_inv_insert_str : forall Ins str ws head prev hs h,
  hc_inv Ins str ws head prev hs -> 0 <= h < hs -> 0 <= str -> wrap16 str = str ->
  0 <= str mod ws < arr_len prev -> h < arr_len head ->
  hc_inv (fun q => Ins q \/ q = str) (str + 1) ws
         (arr_set head h (wrap16 str)) (arr_set prev (str mod ws) (arr_get head h)) hs.
Proof. intros. apply (hc_inv_insert Ins str); try assumption; lia. Qed.


Lemma slide_hash_loop_len : forall f a n ws, arr_len (slide_hash_loop f a n ws) = arr_len a.
Proof.
  induction f as [|f IH]; intros a n ws; cbn [slide_hash_loop]; [reflexivity|].
  destruct (negb (n - 1 =? 0)); [rewrite IH|]; rewrite arr_len_set; reflexivity.
Qed.

Lemma slide_hash_loop_get : forall f a n ws i,
  Z.of_nat f = n -> 0 <= n <= arr_len a -> 0 <= ws ->
  (forall j, 0 <= j < arr_len a -> 0 <= arr_get a j < 65536) ->
  arr_get (slide_hash_loop f a n ws) i
  = if (0 <=? i) && (i <? n) then (if ws <=? arr_get a i then arr_get a i - ws else 0) else arr_get a i.
Proof.
  induction f as [|f IH]; intros a n ws i Hf Hn Hws Hr; cbn [slide_hash_loop].
  - destruct (Z.leb_spec 0 i), (Z.ltb_spec i n); cbn [andb]; try reflexivity. lia.
  - assert (Hset : forall j, arr_get (arr_set a (n - 1) (wrap16 (if ws <=? arr_get a (n - 1) then arr_get a (n - 1) - ws else NIL))) j
                       = if j =? n - 1 then (if ws <=? arr_get a (n - 1) then arr_get a (n - 1) - ws else 0) else arr_get a j).
    { intros j. destruct (Z.eqb_spec j (n - 1)) as [->|Hne].
      - rewrite arr_get_set_same by lia. unfold NIL. pose proof (Hr (n - 1) ltac:(lia)).
        rewrite wrap16_mod. apply Z.mod_small. destruct (Z.leb_spec ws (arr_get a (n - 1))); lia.
      - rewrite arr_get_set_other by lia. reflexivity. }
    assert (Hf' : Z.of_nat f = n - 1) by lia.
    destruct (negb (n - 1 =? 0)) eqn:En.
    + assert (Hn' : 0 <= n - 1 <= arr_len (arr_set a (n - 1) (wrap16 (if ws <=? arr_get a (n - 1) then arr_get a (n - 1) - ws else NIL)))) by (rewrite arr_len_set; lia).
      rewrite (IH _ (n - 1) ws i Hf' Hn' Hws).
      2:{ intros j Hj. rewrite arr_len_set in Hj. rewrite Hset. destruct (Z.eqb_spec j (n - 1)); [| exact (Hr j Hj)].
          pose proof (Hr (n - 1) ltac:(lia)). destruct (Z.leb_spec ws (arr_get a (n - 1))); lia. }
      rewrite !Hset.
      destruct (Z.leb_spec 0 i), (Z.ltb_spec i (n - 1)), (Z.ltb_spec i n), (Z.eqb_spec i (n - 1)); cbn [andb]; try reflexivity; try lia.
      subst i. reflexivity.
    + assert (En1 : n = 1) by (destruct (Z.eqb_spec (n - 1) 0); [lia | discriminate En]).
      rewrite En1 in Hset |- *. rewrite Hset. destruct (Z.leb_spec 0 i), (Z.ltb_spec i 1), (Z.eqb_spec i (1 - 1)); cbn [andb]; try reflexivity; try lia.
      subst i. reflexivity.
Qed.

Lemma hc_inv_slide : forall Ins str ws head prev hs,
  hc_inv Ins str ws head prev hs -> 0 < ws -> ws <= str -> 0 <= hs ->
  hs = arr_len head -> ws = arr_len prev ->
  (forall j, 0 <= j < hs -> 0 <= arr_get head j < 65536) ->
  (forall j, 0 <= j < ws -> 0 <= arr_get prev j < 65536) ->
  hc_inv (fun p => Ins (p + ws) /\ 0 < p) (str - ws) ws
         (slide_hash_loop (Z.to_nat hs) head hs ws) (slide_hash_loop (Z.to_nat ws) prev ws ws) hs.
Proof.
  intros Ins str ws head prev hs (H1 & H2 & H3) Hws Hstr Hhs Ehs Ews Rh Rp.
  assert (Gh : forall i, arr_get (slide_hash_loop (Z.to_nat hs) head hs ws) i
                         = if (0 <=? i) && (i <? hs) then (if ws <=? arr_get head i then arr_get head i - ws else 0) else arr_get head i).
  { intros i. apply slide_hash_loop_get; [lia | lia | lia | intros j Hj; apply Rh; lia]. }
  assert (Gp : forall i, arr_get (slide_hash_loop (Z.to_nat ws) prev ws ws) i
                         = if (0 <=? i) && (i <? ws) then (if ws <=? arr_get prev i then arr_get prev i - ws else 0) else arr_get prev i).
  { intros i. apply slide_hash_loop_get; [lia | lia | lia | intros j Hj; apply Rp; lia]. }
  split.
  { intros p [Hp Hpos]. pose proof (H1 _ Hp). lia. }
  split.
  { intros h Hh. rewrite Gh. destruct (Z.leb_spec 0 h), (Z.ltb_spec h hs); cbn [andb]; try lia.
    destruct (H2 h Hh) as [E | I]; [rewrite E; destruct (Z.leb_spec ws 0); [lia | left; reflexivity]|].
    destruct (Z.leb_spec ws (arr_get head h)) as [L|L]; [| left; reflexivity].
    destruct (Z.eq_dec (arr_get head h) ws) as [E|Hne]; [left; lia | right].
    split; [replace (arr_get head h - ws + ws) with (arr_get head h) by lia; exact I | lia]. }
  intros p [Hp Hpos] Hq. pose proof (H1 _ Hp) as Rp'.
  replace (p mod ws) with ((p + ws) mod ws) by (rewrite <- (Z.mod_add p 1 ws) by lia; f_equal; lia).
  pose proof (Z.mod_pos_bound (p + ws) ws Hws) as Hm.
  rewrite Gp. destruct (Z.leb_spec 0 ((p + ws) mod ws)), (Z.ltb_spec ((p + ws) mod ws) ws); cbn [andb]; try lia.
  destruct (H3 (p + ws) Hp ltac:(lia)) as [E | I]; [rewrite E; destruct (Z.leb_spec ws 0); [lia | left; reflexivity]|].
  destruct (Z.leb_spec ws (arr_get prev ((p + ws) mod ws))) as [Lw|Lw]; [| left; reflexivity].
  destruct (Z.eq_dec (arr_get prev ((p + ws) mod ws)) ws) as [E|Hne]; [left; lia | right].
  pose proof (H1 _ I). split; [replace (arr_get prev ((p + ws) mod ws) - ws + ws) with (arr_get prev ((p + ws) mod ws)) by lia; exact I | lia].
Qed.
