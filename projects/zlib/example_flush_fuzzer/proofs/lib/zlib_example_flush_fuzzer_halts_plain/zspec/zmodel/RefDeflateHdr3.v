(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  TreeModel FillWinModel SendModel BitsModel RefFlushPend1 RefDeflateEnd1 RefDeflateHdrKit RefDeflateTrl1 RefDeflateHdr1 RefDeflateHdr2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition zhdr0 (s : deflate_state) : Z :=
  let header := Z.shiftl (Z_DEFLATED + Z.shiftl (ds_w_bits s - 8) 4) 8 in
  let level_flags :=
    if Z.leb Z_HUFFMAN_ONLY (ds_strategy s) || Z.ltb (ds_level s) 2 then 0
    else if Z.ltb (ds_level s) 6 then 1
    else if Z.eqb (ds_level s) 6 then 2
    else 3 in
  let header := Z.lor header (Z.shiftl level_flags 6) in
  if negb (Z.eqb (ds_strstart s) 0) then Z.lor header PRESET_DICT else header.

Definition zhdr (s : deflate_state) : Z := zhdr0 s + (31 - zhdr0 s mod 31).

Lemma zhdr0_range : forall s, 9 <= ds_w_bits s <= 15 -> 0 <= zhdr0 s < 2 ^ 15.
Proof.
  intros s Hw. unfold zhdr0, Z_DEFLATED, PRESET_DICT. cbv zeta. rewrite !Z.shiftl_mul_pow2 by lia.
  assert (B : 0 <= (8 + (ds_w_bits s - 8) * 2 ^ 4) * 2 ^ 8 < 2 ^ 15 - 2 ^ 8) by lia.
  set (b := (8 + (ds_w_bits s - 8) * 2 ^ 4) * 2 ^ 8) in *.
  assert (L : forall f, 0 <= f <= 3 -> 0 <= Z.lor b (f * 2 ^ 6) < 2 ^ 15).
  { intros f Hf. split; [apply Z.lor_nonneg; lia|].
    destruct (Z.eq_dec f 0) as [->|NZ]; [rewrite Z.lor_0_r; lia|].
    apply (Z.log2_lt_cancel). rewrite Z.log2_lor by lia. rewrite (Z.log2_pow2 15) by lia.
    apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia. }
  assert (L2 : forall x, 0 <= x < 2 ^ 15 -> 0 <= Z.lor x 32 < 2 ^ 15).
  { intros x Hx. split; [apply Z.lor_nonneg; lia|].
    destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.lor_0_l; lia|].
    apply (Z.log2_lt_cancel). rewrite Z.log2_lor by lia. rewrite (Z.log2_pow2 15) by lia.
    apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia. }
  destruct (_ || _); [| destruct (_ <? 6); [| destruct (_ =? 6)]]; destruct (negb _);
    first [apply L2; apply L; lia | apply L; lia].
Qed.

Lemma zhdr_range : forall s, 9 <= ds_w_bits s <= 15 -> 0 <= zhdr s < 2 ^ 16.
Proof. intros s Hw. unfold zhdr. pose proof (zhdr0_range s Hw). pose proof (Z.mod_pos_bound (zhdr0 s) 31 ltac:(lia)). lia. Qed.

Lemma put_byte_keeps : forall s c,
  ds_strstart (put_byte s c) = ds_strstart s /\ ds_strm (put_byte s c) = ds_strm s
  /\ ds_status (put_byte s c) = ds_status s /\ ds_wrap (put_byte s c) = ds_wrap s.
Proof. intros s c. destruct s; repeat split; reflexivity. Qed.


Lemma putShortMSB_eq : forall s b, 0 <= b -> putShortMSB s b = put_byte (put_byte s (b / 2 ^ 8)) b.
Proof.
  intros s b Hb. unfold putShortMSB. rewrite Z.shiftr_div_pow2 by lia.
  apply put_byte_congr. apply byte_land.
Qed.

Definition zl_s1 (s : deflate_state) (h : Z) : deflate_state := put_byte (put_byte s (h / 2 ^ 8)) h.

Definition zl_s2 (s : deflate_state) (h : Z) : deflate_state :=
  if negb (Z.eqb (ds_strstart s) 0) then ta_post (zl_s1 s h) else zl_s1 s h.

Definition zl_s3 (s : deflate_state) (h : Z) : deflate_state :=
  set_status (set_strm (zl_s2 s h) (cset_adler (ds_strm (zl_s2 s h)) adler32_init)) BUSY_STATE.

Lemma zl_s1_keeps : forall s h,
  ds_strstart (zl_s1 s h) = ds_strstart s /\ ds_strm (zl_s1 s h) = ds_strm s /\ ds_pending (zl_s1 s h) = ds_pending s + 2.
Proof.
  intros s h. unfold zl_s1.
  rewrite !(proj1 (put_byte_keeps _ _)), !(proj1 (proj2 (put_byte_keeps _ _))), !pending_put_byte. repeat split; lia.
Qed.



Definition zlib_s3_spec (s : deflate_state) : deflate_state :=
  let header := Z.shiftl (Z_DEFLATED + Z.shiftl (ds_w_bits s - 8) 4) 8 in
  let level_flags :=
    if Z.leb Z_HUFFMAN_ONLY (ds_strategy s) || Z.ltb (ds_level s) 2 then 0
    else if Z.ltb (ds_level s) 6 then 1
    else if Z.eqb (ds_level s) 6 then 2
    else 3 in
  let header := Z.lor header (Z.shiftl level_flags 6) in
  let header := if negb (Z.eqb (ds_strstart s) 0) then Z.lor header PRESET_DICT else header in
  let header := header + (31 - header mod 31) in
  let s := putShortMSB s header in
  let s :=
    if negb (Z.eqb (ds_strstart s) 0) then
      let adler := cs_adler (ds_strm s) in
      let s := putShortMSB s (wrap32 (Z.shiftr adler 16)) in
      putShortMSB s (Z.land adler 65535)
    else s in
  let s := set_strm s (cset_adler (ds_strm s) adler32_init) in
  set_status s BUSY_STATE.

Lemma deflate_zlib_header_spec : forall s,
  deflate_zlib_header s =
    (let s := flush_pending (zlib_s3_spec s) in
     if negb (Z.eqb (ds_pending s) 0) then (set_last_flush s (-1), Some Z_OK) else (s, None)).
Proof. intros s. reflexivity. Qed.

Definition zl_s3_raw (s : deflate_state) (h : Z) : deflate_state :=
  let s := putShortMSB s h in
  let s :=
    if negb (Z.eqb (ds_strstart s) 0) then
      let adler := cs_adler (ds_strm s) in
      let s := putShortMSB s (wrap32 (Z.shiftr adler 16)) in
      putShortMSB s (Z.land adler 65535)
    else s in
  let s := set_strm s (cset_adler (ds_strm s) adler32_init) in
  set_status s BUSY_STATE.

Lemma zl_s3_raw_eq : forall s h, 0 <= h -> 0 <= cs_adler (ds_strm s) < 2 ^ 32 -> zl_s3_raw s h = zl_s3 s h.
Proof.
  intros s h Hh Ha. unfold zl_s3_raw, zl_s3, zl_s2. cbv zeta.
  rewrite (putShortMSB_eq s h Hh). fold (zl_s1 s h).
  pose proof (zl_s1_keeps s h) as (A & B & C). rewrite A.
  destruct (negb (ds_strstart s =? 0)); [| reflexivity].
  rewrite (ta_post_eq (zl_s1 s h)) by (rewrite B; exact Ha). reflexivity.
Qed.

Lemma zlib_s3_spec_eq : forall s, 9 <= ds_w_bits s <= 15 -> 0 <= cs_adler (ds_strm s) < 2 ^ 32 ->
  zlib_s3_spec s = zl_s3 s (zhdr s).
Proof.
  intros s Hw Ha. transitivity (zl_s3_raw s (zhdr s)); [reflexivity|].
  apply zl_s3_raw_eq; [pose proof (zhdr_range s Hw); lia | exact Ha].
Qed.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section Hdr.
Variables (ws hs PBL ILEN OCAP : Z).
Variable flush : Z.
Hypothesis Hflush : 0 <= flush < 16.

Definition zlib_pre (s : deflate_state) : Prop :=
  9 <= ds_w_bits s <= 15 /\ 0 <= ds_level s <= 9 /\ 0 <= ds_strategy s <= 4 /\ 0 <= ds_strstart s < 2 ^ 32
  /\ 0 <= ds_pending s /\ ds_pending s + 6 <= PBL /\ 0 <= cs_adler (ds_strm s) < 2 ^ 32.

Definition zlib_emit (s : deflate_state) : Prop :=
  let s3 := zlib_s3_spec s in
  fp_ok PBL OCAP s3 /\ 0 <= ds_pending (flush_pending s3) < 2 ^ 63 /\ 0 <= ds_status (flush_pending s3) < 2 ^ 10.

Definition zlib_ok (s : deflate_state) : Prop := zlib_pre s /\ zlib_emit s.

End Hdr.
