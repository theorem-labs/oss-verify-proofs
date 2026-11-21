(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import LmatchModel FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.



Record lzw (s : deflate_state) : Prop := LZW {
  lz_lb   : ds_lit_bufsize s * 4 = arr_len (ds_pending_buf s);
  lz_se   : ds_sym_end s = (ds_lit_bufsize s - 1) * 3;
  lz_sn   : 0 <= ds_sym_next s <= ds_sym_end s;
  lz_wm   : ds_w_mask s = ds_w_size s - 1;
  lz_hm   : ds_hash_mask s = ds_hash_size s - 1;
  lz_hsh  : 0 <= ds_hash_shift s < 32;
  lz_ih   : 0 <= ds_ins_h s < 2 ^ 16;
  lz_str  : 0 <= ds_strstart s;
  lz_look : 0 <= ds_lookahead s;
  lz_sl   : ds_strstart s + ds_lookahead s <= arr_len (ds_window s);
  lz_ml   : 0 <= ds_match_length s <= MAX_MATCH;
  lz_ms   : 0 <= ds_match_start s < 2 ^ 32;
  lz_mlz  : 0 <= ds_max_lazy_match s < 2 ^ 31;
  lz_wb   : forall i, 0 <= i < arr_len (ds_window s) -> 0 <= arr_get (ds_window s) i < 256;
  lz_hb   : forall i, 0 <= i < arr_len (ds_head s) -> 0 <= arr_get (ds_head s) i < 65536;
  lz_pb   : forall i, 0 <= i < arr_len (ds_prev s) -> 0 <= arr_get (ds_prev s) i < 65536 }.


Definition lit_core (s : deflate_state) : deflate_state * bool :=
  let '(s1, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s)) in
  (set_strstart (set_lookahead s1 (ds_lookahead s1 - 1)) (ds_strstart s1 + 1), bflush).







Lemma wrap8_mod256 : forall z, wrap8 z = z mod 256.
Proof. intros z. unfold wrap8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma wrap16_mod65536 : forall z, wrap16 z = z mod 65536.
Proof. intros z. unfold wrap16. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma wrap8_idem : forall x, wrap8 (wrap8 x) = wrap8 x.
Proof. intros x. rewrite !wrap8_mod256. apply Z.mod_mod. lia. Qed.
Lemma wrap16_wrap32 : forall x, wrap16 (wrap32 x) = x mod 65536.
Proof.
  intros x. rewrite <- wrap16_mod65536. unfold wrap16, wrap32. rewrite <- Z.land_assoc. reflexivity.
Qed.
Lemma wrap16_pred_mod : forall x, wrap16 (x mod 65536 - 1) = (x - 1) mod 65536.
Proof. intros x. rewrite wrap16_mod65536. rewrite Zminus_mod_idemp_l. reflexivity. Qed.
Lemma shiftr8_div : forall x, Z.shiftr x 8 = x / 256.
Proof. intros x. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma wrap8_wrap16_wrap32 : forall x, wrap8 (wrap16 (wrap32 x)) = wrap8 (x mod 65536).
Proof. intros x. rewrite wrap16_wrap32. reflexivity. Qed.
Lemma shiftr8_wrap16_wrap32 : forall x, Z.shiftr (wrap16 (wrap32 x)) 8 = (x mod 65536) / 256.
Proof. intros x. rewrite wrap16_wrap32, shiftr8_div. reflexivity. Qed.
Lemma wrap16_wrap16_wrap32_pred : forall x, wrap16 (wrap16 (wrap32 x) - 1) = (x - 1) mod 65536.
Proof. intros x. rewrite wrap16_wrap32, wrap16_pred_mod. reflexivity. Qed.










Definition istep (s : deflate_state) : deflate_state :=
  let s1 := set_strstart s (ds_strstart s + 1) in
  set_match_length (fst (insert_string s1 (ds_strstart s + 1))) (ds_match_length s - 1).

Lemma deflate_fast_insert_step : forall f s,
  deflate_fast_insert (S f) s =
    (let s' := istep s in if negb (Z.eqb (ds_match_length s') 0) then deflate_fast_insert f s' else s').
Proof.
  intros f s. unfold istep. cbn [deflate_fast_insert].
  destruct (insert_string (set_strstart s (ds_strstart s + 1)) (ds_strstart (set_strstart s (ds_strstart s + 1)))) as [s2 hh] eqn:E.
  replace (ds_strstart (set_strstart s (ds_strstart s + 1))) with (ds_strstart s + 1) in E by (destruct s; reflexivity).
  rewrite E. cbn [fst].
  replace (ds_match_length s2) with (ds_match_length s); [reflexivity|].
  assert (E2 : s2 = fst (insert_string (set_strstart s (ds_strstart s + 1)) (ds_strstart s + 1))) by (rewrite E; reflexivity).
  rewrite E2. unfold insert_string. destruct s; reflexivity.
Qed.




Lemma set_match_start_twice : forall s a b, set_match_start (set_match_start s a) b = set_match_start s b.
Proof. intros; destruct s; reflexivity. Qed.
Lemma set_match_start_self : forall s, set_match_start s (ds_match_start s) = s.
Proof. intros; destruct s; reflexivity. Qed.

Lemma longest_match_body_shape : forall s0 v cur cl bl nm lim se1 se,
  exists v', fst (fst (fst (fst (fst (fst (longest_match_body (set_match_start s0 v) cur cl bl nm lim se1 se)))))) = set_match_start s0 v'.
Proof.
  intros. unfold longest_match_body.
  destruct (_ || _); [| destruct (_ <? _)%Z; [destruct (_ <=? _)%Z|]]; cbn -[Z.ltb Z.eqb Z.leb wrap32 arr_get Z.land Z.sub Z.add lm_cmp_loop];
  repeat (first [rewrite set_match_start_twice | destruct (_ <? _)%Z | destruct (negb _)]); cbn -[Z.ltb Z.eqb Z.leb wrap32 arr_get Z.land Z.sub Z.add lm_cmp_loop];
  try rewrite set_match_start_twice; eauto.
Qed.

Lemma longest_match_loop_shape : forall f s0 v cur cl bl nm lim se1 se,
  exists v', fst (longest_match_loop f (set_match_start s0 v) cur cl bl nm lim se1 se) = set_match_start s0 v'.
Proof.
  induction f as [|f IH]; intros; [cbn; eauto|].
  cbn [longest_match_loop].
  destruct (longest_match_body_shape s0 v cur cl bl nm lim se1 se) as [v1 E1].
  destruct (longest_match_body (set_match_start s0 v) cur cl bl nm lim se1 se) as [[[[[[s1 bl1] a1] b1] c1] d1] cont]. cbn in E1. subst s1.
  destruct cont; [apply IH | cbn; eauto].
Qed.

Lemma longest_match_shape : forall s cur, exists v, fst (longest_match s cur) = set_match_start s v.
Proof.
  intros s cur. unfold longest_match.
  match goal with |- context [longest_match_loop ?f s ?a ?b ?c ?d ?e ?g ?h] =>
    destruct (longest_match_loop_shape f s (ds_match_start s) a b c d e g h) as [v' E];
    rewrite set_match_start_self in E;
    destruct (longest_match_loop f s a b c d e g h) as [s' bl] end.
  cbn in E. subst s'. exists v'. destruct (_ <=? _); reflexivity.
Qed.

Definition lm_pre (s : deflate_state) (cur : Z) : Prop :=
  0 <= cur < 2 ^ 32
  /\ 1 <= (if ds_good_match s <=? ds_prev_length s then Z.shiftr (ds_max_chain_length s) 2 else ds_max_chain_length s)
  /\ Forall (fun c => 0 <= c < ds_strstart s) (lm_visited s cur)
  /\ (0 <= ds_strstart s /\ ds_strstart s + 258 < arr_len (ds_window s) /\ arr_len (ds_window s) <= 2 ^ 31)
  /\ (0 <= ds_w_mask s < arr_len (ds_prev s) /\ arr_len (ds_prev s) <= 2 ^ 31)
  /\ 1 <= ds_prev_length s <= 258 /\ 0 <= ds_nice_match s <= 258 /\ 0 <= ds_lookahead s < 2 ^ 31
  /\ 0 <= ds_good_match s < 2 ^ 31 /\ 0 <= ds_max_chain_length s < 2 ^ 31 /\ 262 <= ds_w_size s < 2 ^ 31.









Definition after_tally (s : deflate_state) (bflush : bool) : deflate_state * loop_out :=
  if bflush then
    let '(s, r) := flush_block s 0 in
    match r with Some bs => (s, LRet bs) | None => (s, LCont) end
  else (s, LCont).

Definition dispatch_spec (s : deflate_state) : deflate_state * loop_out :=
  let '(s, bflush) :=
    if Z.leb MIN_MATCH (ds_match_length s) then
      let '(s, bflush) := tr_tally_dist s (wrap32 (ds_strstart s - ds_match_start s))
                                          (ds_match_length s - MIN_MATCH) in
      let s := set_lookahead s (ds_lookahead s - ds_match_length s) in
      let s :=
        if Z.leb (ds_match_length s) (ds_max_lazy_match s)
           && Z.leb MIN_MATCH (ds_lookahead s)
        then
          let s := set_match_length s (ds_match_length s - 1) in
          let s := deflate_fast_insert (Z.to_nat (ds_match_length s)) s in
          set_strstart s (ds_strstart s + 1)
        else
          let s := set_strstart s (ds_strstart s + ds_match_length s) in
          let s := set_match_length s 0 in
          let s := set_ins_h s (arr_get (ds_window s) (ds_strstart s)) in
          set_ins_h s (update_hash s (ds_ins_h s) (arr_get (ds_window s) (ds_strstart s + 1)))
      in (s, bflush)
    else
      let '(s, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s)) in
      let s := set_lookahead s (ds_lookahead s - 1) in
      let s := set_strstart s (ds_strstart s + 1) in
      (s, bflush) in
  after_tally s bflush.

Definition p1_spec (s : deflate_state) : deflate_state * loop_out :=
  let '(s, hash_head) :=
    if Z.leb MIN_MATCH (ds_lookahead s) then insert_string s (ds_strstart s) else (s, NIL) in
  let s :=
    if negb (Z.eqb hash_head NIL)
       && Z.leb (wrap32 (ds_strstart s - hash_head)) (ds_w_size s - MIN_LOOKAHEAD)
    then let '(s, ml) := longest_match s hash_head in set_match_length s ml
    else s in
  dispatch_spec s.

Lemma deflate_fast_body_eq : forall s flush,
  deflate_fast_body s flush =
    if Z.ltb (ds_lookahead s) MIN_LOOKAHEAD then
      let s1 := fill_window s in
      if Z.ltb (ds_lookahead s1) MIN_LOOKAHEAD && Z.eqb flush Z_NO_FLUSH then (s1, LRet need_more)
      else if Z.eqb (ds_lookahead s1) 0 then (s1, LBreak)
      else p1_spec s1
    else p1_spec s.
Proof.
  intros s flush. unfold deflate_fast_body, p1_spec, dispatch_spec, after_tally.
  destruct (Z.ltb (ds_lookahead s) MIN_LOOKAHEAD).
  - cbv zeta. destruct (Z.ltb (ds_lookahead (fill_window s)) MIN_LOOKAHEAD && Z.eqb flush Z_NO_FLUSH); [reflexivity|].
    destruct (Z.eqb (ds_lookahead (fill_window s)) 0); reflexivity.
  - reflexivity.
Qed.

Lemma deflate_fast_loop_step : forall f s flush,
  deflate_fast_loop (S f) s flush =
    (let '(s', o) := deflate_fast_body s flush in
     match o with
     | LCont => deflate_fast_loop f s' flush
     | LBreak => (s', None)
     | LRet bs => (s', Some bs)
     end).
Proof. intros; reflexivity. Qed.

