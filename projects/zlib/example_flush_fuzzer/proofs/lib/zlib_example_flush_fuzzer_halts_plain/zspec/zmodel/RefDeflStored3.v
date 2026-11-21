(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk
  TreeModel FillWinModel SendModel BitsModel AdlerModel ZChkAdl SymEx2Expr RefFlushPend1 RefDeflStored2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition rbpost (s : deflate_state) (len : Z) : deflate_state :=
  let '(s, _) := read_buf s RB_next_out len in
  let st := ds_strm s in
  let st := cset_avail_out st (cs_avail_out st - len) in
  let st := cset_total_out st (wrap64 (cs_total_out st + len)) in
  set_strm s st.

Definition sL (s : deflate_state) : Z := if slen s <? sleft s then slen s else sleft s.

Definition tripA (s : deflate_state) : deflate_state :=
  let len := slen s in
  let left := sleft s in
  let s1 := tr_stored_block s None 0 0 in
  let s2 := hdr4 s1 len in
  let s3 := flush_pending s2 in
  let '(s4, len') := if negb (left =? 0) then (awpost s3 (sL s), len - sL s) else (s3, len) in
  if negb (len' =? 0) then rbpost s4 len' else s4.

Lemma body_brkA : forall flush mb s,
  cs_avail_out (ds_strm s) < hdrb s -> deflate_stored_body s flush mb = (s, 0, true).
Proof.
  intros flush mb s H. unfold deflate_stored_body. rewrite hdrb_model.
  rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity.
Qed.

Lemma body_eqA : forall flush mb s,
  flush <> Z_FINISH -> 0 <= ds_block_start s <= ds_strstart s -> ds_strstart s < 2 ^ 32 ->
  hdrb s <= cs_avail_out (ds_strm s) ->
  deflate_stored_body s flush mb = if sbrk flush mb s then (s, 0, true) else (tripA s, 0, false).
Proof.
  intros flush mb s Hf Hbs Hss Hh.
  unfold deflate_stored_body, sbrk, tripA, sL, slen, sL1, sleft, rbpost, awpost, hdr4. rewrite hdrb_model.
  rewrite (proj2 (Z.ltb_ge _ _) Hh).
  rewrite (wrap32_id (ds_strstart s - ds_block_start s)) by lia.
  replace (flush =? Z_FINISH) with false by (symmetry; apply Z.eqb_neq; exact Hf).
  cbn [andb].
  match goal with |- (if ?c then _ else _) = _ => destruct c end; [reflexivity|].
  destruct (negb (ds_strstart s - ds_block_start s =? 0)); reflexivity.
Qed.


Section LoopA.
Variables (ws hs PBL ILEN OCAP : Z).
Variables (flush mb : Z).
Hypothesis Hflush : 0 <= flush <= 5.
Hypothesis Hmb : 0 <= mb < 2 ^ 18.

Local Notation outlen st := (Z.of_nat (length (cs_out_rev st))).

Definition winA_ok (s3 : deflate_state) (L : Z) : Prop :=
  0 <= ds_block_start s3 /\ ds_block_start s3 + L <= 2 * ws
  /\ (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window s3) j < 256)
  /\ outlen (ds_strm s3) + L <= OCAP
  /\ 0 <= cs_avail_out (ds_strm s3) < 2 ^ 32 /\ 0 <= cs_total_out (ds_strm s3) < 2 ^ 64.

Definition ckv (s : deflate_state) (bytes : list Z) : Z :=
  if ds_wrap s =? 1 then adler32_upd (cs_adler (ds_strm s)) bytes
  else if ds_wrap s =? 2 then crc32_upd (cs_adler (ds_strm s)) bytes
  else cs_adler (ds_strm s).

Definition ckpost (s : deflate_state) (bytes : list Z) : deflate_state :=
  set_strm s (cset_adler (ds_strm s) (ckv s bytes)).

Definition rdA_ok (s4 : deflate_state) (len : Z) : Prop :=
  0 <= cs_avail_in (ds_strm s4) < 2 ^ 32 /\ 0 <= ds_bi_valid s4 <= 16 /\ 0 <= cs_avail_out (ds_strm s4) < 2 ^ 32
  /\ (len <> 0 ->
      len <= cs_avail_in (ds_strm s4) /\ 0 <= cs_next_in (ds_strm s4) /\ cs_next_in (ds_strm s4) + len <= ILEN
      /\ outlen (ds_strm s4) + len <= OCAP
      /\ (forall j, 0 <= j < ILEN -> 0 <= arr_get (cs_input (ds_strm s4)) j < 256)
      /\ 0 <= ds_wrap s4 <= 2 /\ (ds_wrap s4 = 1 -> adler_canon (cs_adler (ds_strm s4)))
      /\ (ds_wrap s4 = 2 -> 0 <= cs_adler (ds_strm s4) < 2 ^ 64)
      /\ 0 <= cs_total_in (ds_strm s4) < 2 ^ 64 /\ 0 <= cs_total_out (ds_strm s4) < 2 ^ 64
      /\ len <= cs_avail_out (ds_strm s4)).

Definition tripA_ok (s : deflate_state) : Prop :=
  let len := slen s in
  let left := sleft s in
  let s1 := tr_stored_block s None 0 0 in
  let s2 := hdr4 s1 len in
  let s3 := flush_pending s2 in
  let L := sL s in
  let s4 := (if negb (left =? 0) then awpost s3 L else s3) in
  let len' := (if negb (left =? 0) then len - L else len) in
  tripA_wf s /\ BINV PBL s /\ 4 <= ds_pending s1 <= PBL /\ fp_ok PBL OCAP s2
  /\ (left <> 0 -> winA_ok s3 L) /\ rdA_ok s4 len'.

Fixpoint loopA_ok (fuel : nat) (s : deflate_state) : Prop :=
  match fuel with
  | O => cs_avail_out (ds_strm s) < hdrb s
  | Datatypes.S f => hdrb s <= cs_avail_out (ds_strm s) -> tripA_ok s /\ (sbrk flush mb s = false -> loopA_ok f (tripA s))
  end.

Lemma loopA_model : forall fuel s,
  flush <> Z_FINISH -> 0 <= ds_block_start s <= ds_strstart s -> ds_strstart s < 2 ^ 32 ->
  deflate_stored_loop (Datatypes.S fuel) s flush mb =
    (if cs_avail_out (ds_strm s) <? hdrb s then (s, 0)
     else if sbrk flush mb s then (s, 0) else deflate_stored_loop fuel (tripA s) flush mb).
Proof.
  intros fuel s Hf4 Hbs Hss. cbn [deflate_stored_loop].
  destruct (Z.ltb_spec (cs_avail_out (ds_strm s)) (hdrb s)) as [C|C].
  - rewrite (body_brkA flush mb s C). reflexivity.
  - rewrite (body_eqA flush mb s Hf4 Hbs Hss C). destruct (sbrk flush mb s); reflexivity.
Qed.

End LoopA.
