(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk
  TreeModel FillWinModel SendModel BitsModel AdlerModel ZChkAdl SymEx2Expr RefFlushPend1 .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition hdrb (s : deflate_state) : Z := (ds_bi_valid s + 42) / 2 ^ 3.

Lemma hdrb_model : forall s, Z.shiftr (ds_bi_valid s + 42) 3 = hdrb s.
Proof. intros s. unfold hdrb. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma hdrb_range : forall s, 0 <= ds_bi_valid s <= 16 -> 5 <= hdrb s <= 7.
Proof.
  intros s H. unfold hdrb. change (2 ^ 3) with 8.
  pose proof (Z.div_mod (ds_bi_valid s + 42) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ds_bi_valid s + 42) 8 ltac:(lia)). lia.
Qed.

Definition sleft (s : deflate_state) : Z := ds_strstart s - ds_block_start s.

Definition sL1 (s : deflate_state) : Z :=
  if sleft s + cs_avail_in (ds_strm s) <? MAX_STORED then wrap32 (sleft s + cs_avail_in (ds_strm s)) else MAX_STORED.

Definition slen (s : deflate_state) : Z :=
  if cs_avail_out (ds_strm s) - hdrb s <? sL1 s then cs_avail_out (ds_strm s) - hdrb s else sL1 s.

Definition sbrk (flush mb : Z) (s : deflate_state) : bool :=
  (slen s <? mb) && (((slen s =? 0) && negb (flush =? Z_FINISH)) || (flush =? Z_NO_FLUSH)
                     || negb (slen s =? wrap32 (sleft s + cs_avail_in (ds_strm s)))).

Lemma sL1_range : forall s, 0 <= sleft s -> 0 <= cs_avail_in (ds_strm s) ->
  0 <= sL1 s <= MAX_STORED /\ (sleft s + cs_avail_in (ds_strm s) < MAX_STORED -> sL1 s = sleft s + cs_avail_in (ds_strm s))
  /\ (MAX_STORED <= sleft s + cs_avail_in (ds_strm s) -> sL1 s = MAX_STORED).
Proof.
  intros s Hl Ha. unfold sL1, MAX_STORED.
  destruct (Z.ltb_spec (sleft s + cs_avail_in (ds_strm s)) 65535); rewrite ?wrap32_id by lia; lia.
Qed.

Lemma slen_range : forall s, 0 <= sleft s -> 0 <= cs_avail_in (ds_strm s) -> hdrb s <= cs_avail_out (ds_strm s) ->
  0 <= slen s <= sL1 s /\ slen s <= cs_avail_out (ds_strm s) - hdrb s
  /\ (cs_avail_out (ds_strm s) - hdrb s < sL1 s -> slen s = cs_avail_out (ds_strm s) - hdrb s)
  /\ (sL1 s <= cs_avail_out (ds_strm s) - hdrb s -> slen s = sL1 s).
Proof.
  intros s Hl Ha Hh. pose proof (sL1_range s Hl Ha) as (R1 & _). unfold slen.
  destruct (Z.ltb_spec (cs_avail_out (ds_strm s) - hdrb s) (sL1 s)); lia.
Qed.

Definition hdr4 (s1 : deflate_state) (len : Z) : deflate_state :=
  let pb := ds_pending_buf s1 in
  let p := ds_pending s1 in
  let pb := arr_set pb (p - 4) (wrap8 len) in
  let pb := arr_set pb (p - 3) (wrap8 (Z.shiftr len 8)) in
  let pb := arr_set pb (p - 2) (wrap8 (Z.lnot len)) in
  let pb := arr_set pb (p - 1) (wrap8 (Z.shiftr (wrap32 (Z.lnot len)) 8)) in
  set_pending_buf s1 pb.

Definition awpost (s : deflate_state) (left : Z) : deflate_state :=
  let st := ds_strm s in
  let st := cs_emit st (arr_slice (ds_window s) (ds_block_start s) left) in
  let st := cset_avail_out st (cs_avail_out st - left) in
  let st := cset_total_out st (wrap64 (cs_total_out st + left)) in
  let s := set_strm s st in
  set_block_start s (ds_block_start s + left).

Definition tripA_wf (s : deflate_state) : Prop :=
  0 <= ds_bi_valid s <= 16 /\ 0 <= cs_avail_out (ds_strm s) < 2 ^ 32 /\ 0 <= cs_avail_in (ds_strm s) < 2 ^ 32
  /\ 0 <= ds_block_start s <= ds_strstart s /\ ds_strstart s < 2 ^ 31.


