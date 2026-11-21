(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import DeflFastModel DeflSlowModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition rtally_core (s : deflate_state) : deflate_state * bool :=
  tr_tally_dist s 1 (ds_match_length s - MIN_MATCH).




Definition rtally_out (s : deflate_state) : deflate_state :=
  set_match_length (set_strstart (set_lookahead (fst (rtally_core s)) (ds_lookahead s - ds_match_length s))
                                 (ds_strstart s + ds_match_length s)) 0.


Definition rscan (s0 : deflate_state) : deflate_state :=
  if Z.leb MIN_MATCH (ds_lookahead s0) && Z.ltb 0 (ds_strstart s0) then
    let w := ds_window s0 in
    let scan := ds_strstart s0 - 1 in
    let prev := arr_get w scan in
    let '(scan, ok) := rle_cmpk 3%nat w prev scan in
    if ok then
      let strend := ds_strstart s0 + MAX_MATCH in
      let scan := rle_cmp_loop 33%nat w prev scan strend in
      let s := set_match_length s0 (MAX_MATCH - (strend - scan)) in
      if Z.ltb (ds_lookahead s) (ds_match_length s) then set_match_length s (ds_lookahead s) else s
    else s0
  else s0.

Definition rdispatch (s2 : deflate_state) : deflate_state * loop_out :=
  if Z.leb MIN_MATCH (ds_match_length s2) then after_tally (rtally_out s2) (snd (rtally_core s2))
  else after_tally (fst (lit_core s2)) (snd (lit_core s2)).

Definition rbody_spec (s : deflate_state) : deflate_state * loop_out :=
  rdispatch (rscan (set_match_length s 0)).

Lemma td_look : forall s d l, ds_lookahead (fst (tr_tally_dist s d l)) = ds_lookahead s. Proof. intros; destruct s; reflexivity. Qed.
Lemma td_str : forall s d l, ds_strstart (fst (tr_tally_dist s d l)) = ds_strstart s. Proof. intros; destruct s; reflexivity. Qed.
Lemma td_ml : forall s d l, ds_match_length (fst (tr_tally_dist s d l)) = ds_match_length s. Proof. intros; destruct s; reflexivity. Qed.

Lemma deflate_rle_body_eq : forall s flush,
  deflate_rle_body s flush =
  if Z.leb (ds_lookahead s) MAX_MATCH then
    let s1 := fill_window s in
    if Z.leb (ds_lookahead s1) MAX_MATCH && Z.eqb flush Z_NO_FLUSH then (s1, LRet need_more)
    else if Z.eqb (ds_lookahead s1) 0 then (s1, LBreak)
    else rbody_spec s1
  else rbody_spec s.
Proof.
  intros s flush.
  assert (B : forall u, (let s0 := set_match_length u 0 in
     let s2 := (if Z.leb MIN_MATCH (ds_lookahead s0) && Z.ltb 0 (ds_strstart s0) then
      let w := ds_window s0 in
      let scan := ds_strstart s0 - 1 in
      let prev := arr_get w scan in
      let '(scan, ok) := rle_cmpk 3%nat w prev scan in
      if ok then
        let strend := ds_strstart s0 + MAX_MATCH in
        let scan := rle_cmp_loop 33%nat w prev scan strend in
        let s := set_match_length s0 (MAX_MATCH - (strend - scan)) in
        if Z.ltb (ds_lookahead s) (ds_match_length s) then set_match_length s (ds_lookahead s) else s
      else s0
    else s0) in
    let '(s3, bflush) :=
      (if Z.leb MIN_MATCH (ds_match_length s2) then
        let '(s4, bflush) := tr_tally_dist s2 1 (ds_match_length s2 - MIN_MATCH) in
        let s5 := set_lookahead s4 (ds_lookahead s4 - ds_match_length s4) in
        let s6 := set_strstart s5 (ds_strstart s5 + ds_match_length s5) in
        let s7 := set_match_length s6 0 in
        (s7, bflush)
      else
        let '(s4, bflush) := tr_tally_lit s2 (arr_get (ds_window s2) (ds_strstart s2)) in
        let s5 := set_lookahead s4 (ds_lookahead s4 - 1) in
        let s6 := set_strstart s5 (ds_strstart s5 + 1) in
        (s6, bflush)) in
    if bflush then
      let '(s8, r) := flush_block s3 0 in
      match r with Some bs => (s8, LRet bs) | None => (s8, LCont) end
    else (s3, LCont)) = rbody_spec u).
  { intros u. unfold rbody_spec, rdispatch, rscan. cbv zeta.
    set (s2 := if Z.leb MIN_MATCH _ && _ then _ else _). clearbody s2.
    unfold rtally_out, rtally_core, lit_core, after_tally.
    destruct (Z.leb MIN_MATCH (ds_match_length s2)).
    - pose proof (td_look s2 1 (ds_match_length s2 - MIN_MATCH)) as K1.
      pose proof (td_str s2 1 (ds_match_length s2 - MIN_MATCH)) as K2.
      pose proof (td_ml s2 1 (ds_match_length s2 - MIN_MATCH)) as K3.
      destruct (tr_tally_dist s2 1 (ds_match_length s2 - MIN_MATCH)) as [s4 b]. cbn [fst snd] in K1, K2, K3 |- *.
      rewrite !ml_set_look, !str_set_look, K1, K2, K3.
      destruct b; reflexivity.
    - destruct (tr_tally_lit s2 (arr_get (ds_window s2) (ds_strstart s2))) as [s4 b]. cbn [fst snd].
      destruct b; reflexivity. }
  unfold deflate_rle_body. rewrite <- (B s), <- (B (fill_window s)).
  destruct (Z.leb (ds_lookahead s) MAX_MATCH); [| reflexivity].
  destruct (Z.leb (ds_lookahead (fill_window s)) MAX_MATCH && Z.eqb flush Z_NO_FLUSH); [reflexivity|].
  destruct (Z.eqb (ds_lookahead (fill_window s)) 0); reflexivity.
Qed.

Lemma deflate_rle_loop_step : forall f s flush,
  deflate_rle_loop (S f) s flush =
  let '(s', o) := deflate_rle_body s flush in
  match o with LCont => deflate_rle_loop f s' flush | LBreak => (s', None) | LRet bs => (s', Some bs) end.
Proof. reflexivity. Qed.


Lemma rle_cmpk_range : forall k w prev scan,
  scan < fst (rle_cmpk k w prev scan) <= scan + Z.of_nat k \/ (k = 0%nat /\ fst (rle_cmpk k w prev scan) = scan).
Proof.
  induction k as [|k IH]; intros w prev scan; cbn [rle_cmpk fst]; [right; split; reflexivity|].
  destruct (Z.eqb prev (arr_get w (scan + 1))).
  - destruct (IH w prev (scan + 1)) as [H|[-> H]]; [left; lia|]. cbn in H |- *. left. lia.
  - cbn. left. lia.
Qed.

Lemma rle_cmpk_ok_fst : forall k w prev scan,
  snd (rle_cmpk k w prev scan) = true -> fst (rle_cmpk k w prev scan) = scan + Z.of_nat k.
Proof.
  induction k as [|k IH]; intros w prev scan; cbn [rle_cmpk fst snd]; [intros _; lia|].
  destruct (Z.eqb prev (arr_get w (scan + 1))); [| cbn; intros E; discriminate E].
  intros H. rewrite (IH _ _ _ H). lia.
Qed.


Lemma rle_cmp_loop_le : forall fuel w prev scan strend,
  scan < strend -> (strend - scan) mod 8 = 0 ->
  scan <= rle_cmp_loop fuel w prev scan strend <= strend.
Proof.
  induction fuel as [|f IH]; intros w prev scan strend Hlt Hmod; cbn [rle_cmp_loop]; [lia|].
  assert (exists k, strend - scan = 8 * k) as [k Hk]
    by (exists ((strend - scan) / 8); pose proof (Z.div_mod (strend - scan) 8 ltac:(lia)); lia).
  assert (H8 : scan + 8 <= strend) by lia.
  destruct (rle_cmpk 8 w prev scan) as [sc ok] eqn:E.
  pose proof (rle_cmpk_range 8 w prev scan) as Hr. rewrite E in Hr. cbn [fst] in Hr.
  destruct Hr as [Hr|[Hk0 _]]; [| discriminate Hk0]. cbn in Hr.
  destruct ok; cbn [andb]; [| lia].
  pose proof (rle_cmpk_ok_fst 8 w prev scan) as Hf. rewrite E in Hf. cbn [fst snd] in Hf. specialize (Hf eq_refl). cbn in Hf.
  destruct (Z.ltb_spec sc strend) as [L|L]; [| lia].
  assert (A2 : (strend - sc) mod 8 = 0).
  { rewrite Hf. replace (strend - (scan + Z.of_nat 8)) with ((k - 1) * 8) by lia. apply Z_mod_mult. }
  pose proof (IH w prev sc strend L A2). lia.
Qed.




