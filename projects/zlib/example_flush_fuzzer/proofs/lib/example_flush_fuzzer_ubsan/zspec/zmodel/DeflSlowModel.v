(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import DeflFastModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition stally_core (s : deflate_state) : deflate_state * bool :=
  tr_tally_dist s (wrap32 (ds_strstart s - 1 - ds_prev_match s)) (ds_prev_length s - MIN_MATCH).

Definition stally_chain (s : deflate_state) : deflate_state :=
  let n := ds_sym_next s in
  let d := (ds_strstart s - 1 - ds_prev_match s) mod 65536 in
  let len := ds_prev_length s - 3 in
  let lc := arr_get length_code_a len in
  let dc := d_code ((ds_strstart s - 1 - ds_prev_match s - 1) mod 65536) in
  let s6 := sym_buf_set (set_sym_next (sym_buf_set (set_sym_next (sym_buf_set (set_sym_next s (n + 1)) n d) (n + 2)) (n + 1) (d / 256)) (n + 3)) (n + 2) len in
  let s7 := set_Freq s6 TL (lc + 257) (Freq s6 TL (lc + 257) + 1) in
  set_Freq s7 TD dc (Freq s7 TD dc + 1).

Lemma stally_chain_eq : forall s, 0 <= ds_prev_length s - 3 < 256 -> fst (stally_core s) = stally_chain s.
Proof.
  intros s Hml.
  destruct s; cbv -[Z.add Z.sub Z.mul Z.div Z.modulo Z.shiftr Z.ltb Z.leb Z.eqb arr_set arr_get wrap8 wrap16 wrap32 d_code length_code_a].
  cbn in Hml.
  set (LC := length_code_a); clearbody LC. set (DC := d_code); clearbody DC.
  rewrite wrap8_wrap16_wrap32, shiftr8_wrap16_wrap32, wrap8_idem, wrap16_wrap16_wrap32_pred.
  match goal with |- context [arr_get LC (wrap8 (?ml - 3))] =>
    replace (arr_get LC (wrap8 (ml - 3))) with (arr_get LC (ml - 3))
      by (rewrite (wrap8_mod256 (ml - 3)), (Z.mod_small (ml - 3) 256 Hml); reflexivity);
    replace (arr_get LC (ml - 3) + 256 + 1) with (arr_get LC (ml - 3) + 257) by lia
  end.
  match goal with |- context [?n + 1 + 1 + 1] =>
    replace (n + 1 + 1 + 1) with (n + 3) by lia; replace (n + 1 + 1) with (n + 2) by lia end.
  reflexivity.
Qed.


Lemma stally_chain_keeps : forall s,
  ds_sym_next (stally_chain s) = ds_sym_next s + 3 /\ ds_sym_end (stally_chain s) = ds_sym_end s
  /\ ds_lookahead (stally_chain s) = ds_lookahead s /\ ds_strstart (stally_chain s) = ds_strstart s
  /\ ds_prev_length (stally_chain s) = ds_prev_length s /\ ds_match_available (stally_chain s) = ds_match_available s
  /\ ds_block_start (stally_chain s) = ds_block_start s /\ ds_match_length (stally_chain s) = ds_match_length s.
Proof. intros s. unfold stally_chain, sym_buf_set, set_Freq. destruct s; cbn; repeat split; reflexivity. Qed.

Lemma stally_core_keeps : forall s, 0 <= ds_prev_length s - 3 < 256 ->
  ds_sym_next (fst (stally_core s)) = ds_sym_next s + 3 /\ ds_sym_end (fst (stally_core s)) = ds_sym_end s
  /\ ds_lookahead (fst (stally_core s)) = ds_lookahead s /\ ds_strstart (fst (stally_core s)) = ds_strstart s
  /\ ds_prev_length (fst (stally_core s)) = ds_prev_length s /\ ds_match_available (fst (stally_core s)) = ds_match_available s
  /\ ds_block_start (fst (stally_core s)) = ds_block_start s /\ ds_match_length (fst (stally_core s)) = ds_match_length s.
Proof. intros s H. rewrite (stally_chain_eq s H). apply stally_chain_keeps. Qed.






Definition sistep (s : deflate_state) (max_insert : Z) : deflate_state :=
  let s1 := set_strstart s (ds_strstart s + 1) in
  let s2 := if Z.leb (ds_strstart s1) max_insert then fst (insert_string s1 (ds_strstart s1)) else s1 in
  set_prev_length s2 (ds_prev_length s2 - 1).

Lemma deflate_slow_insert_step : forall f s mi,
  deflate_slow_insert (S f) s mi =
    (let s' := sistep s mi in if negb (Z.eqb (ds_prev_length s') 0) then deflate_slow_insert f s' mi else s').
Proof. intros; reflexivity. Qed.







Definition sdispatch (s : deflate_state) : deflate_state * loop_out :=
  if Z.leb MIN_MATCH (ds_prev_length s) && Z.leb (ds_match_length s) (ds_prev_length s) then
    let max_insert := wrap32 (ds_strstart s + ds_lookahead s - MIN_MATCH) in
    let '(s, bflush) := tr_tally_dist s (wrap32 (ds_strstart s - 1 - ds_prev_match s))
                                        (ds_prev_length s - MIN_MATCH) in
    let s := set_lookahead s (wrap32 (ds_lookahead s - (ds_prev_length s - 1))) in
    let s := set_prev_length s (ds_prev_length s - 2) in
    let s := deflate_slow_insert (Z.to_nat (ds_prev_length s)) s max_insert in
    let s := set_match_available s 0 in
    let s := set_match_length s (MIN_MATCH - 1) in
    let s := set_strstart s (ds_strstart s + 1) in
    if bflush then
      let '(s, r) := flush_block s 0 in
      match r with Some bs => (s, LRet bs) | None => (s, LCont) end
    else (s, LCont)
  else if negb (Z.eqb (ds_match_available s) 0) then
    let '(s, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in
    let s := if bflush then flush_block_only s 0 else s in
    let s := set_strstart s (ds_strstart s + 1) in
    let s := set_lookahead s (ds_lookahead s - 1) in
    if Z.eqb (cs_avail_out (ds_strm s)) 0 then (s, LRet need_more) else (s, LCont)
  else
    let s := set_match_available s 1 in
    let s := set_strstart s (ds_strstart s + 1) in
    let s := set_lookahead s (ds_lookahead s - 1) in
    (s, LCont).

Definition slow_p2 (s : deflate_state) (hash_head : Z) : deflate_state * loop_out :=
  let s := set_prev_length s (ds_match_length s) in
  let s := set_prev_match s (ds_match_start s) in
  let s := set_match_length s (MIN_MATCH - 1) in
  let s :=
    if negb (Z.eqb hash_head NIL) && Z.ltb (ds_prev_length s) (ds_max_lazy_match s)
       && Z.leb (wrap32 (ds_strstart s - hash_head)) (ds_w_size s - MIN_LOOKAHEAD)
    then
      let '(s, ml) := longest_match s hash_head in
      let s := set_match_length s ml in
      if Z.leb (ds_match_length s) 5
         && (Z.eqb (ds_strategy s) Z_FILTERED
             || (Z.eqb (ds_match_length s) MIN_MATCH
                 && Z.ltb TOO_FAR (wrap32 (ds_strstart s - ds_match_start s))))
      then set_match_length s (MIN_MATCH - 1)
      else s
    else s in
  sdispatch s.

Definition slow_p1 (s : deflate_state) : deflate_state * loop_out :=
  let '(s, hash_head) :=
    if Z.leb MIN_MATCH (ds_lookahead s) then insert_string s (ds_strstart s) else (s, NIL) in
  slow_p2 s hash_head.

Lemma deflate_slow_body_eq : forall s flush,
  deflate_slow_body s flush =
    if Z.ltb (ds_lookahead s) MIN_LOOKAHEAD then
      let s1 := fill_window s in
      if Z.ltb (ds_lookahead s1) MIN_LOOKAHEAD && Z.eqb flush Z_NO_FLUSH then (s1, LRet need_more)
      else if Z.eqb (ds_lookahead s1) 0 then (s1, LBreak)
      else slow_p1 s1
    else slow_p1 s.
Proof.
  intros s flush. unfold deflate_slow_body, slow_p1, slow_p2, sdispatch.
  destruct (Z.ltb (ds_lookahead s) MIN_LOOKAHEAD).
  - cbv zeta. destruct (Z.ltb (ds_lookahead (fill_window s)) MIN_LOOKAHEAD && Z.eqb flush Z_NO_FLUSH); [reflexivity|].
    destruct (Z.eqb (ds_lookahead (fill_window s)) 0); reflexivity.
  - reflexivity.
Qed.

Lemma deflate_slow_loop_step : forall f s flush,
  deflate_slow_loop (S f) s flush =
    (let '(s', o) := deflate_slow_body s flush in
     match o with
     | LCont => deflate_slow_loop f s' flush
     | LBreak => (s', None)
     | LRet bs => (s', Some bs)
     end).
Proof. intros; reflexivity. Qed.


Lemma ml_set_look : forall s v, ds_match_length (set_lookahead s v) = ds_match_length s. Proof. intros; destruct s; reflexivity. Qed.
Lemma str_set_look : forall s v, ds_strstart (set_lookahead s v) = ds_strstart s. Proof. intros; destruct s; reflexivity. Qed.









