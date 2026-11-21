(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  TreeModel FillWinModel SendModel BitsModel RefFlushPend1 RefDeflateEnd1 RefDeflateHdrKit RefDeflateTrl1 RefDeflateHdr1 RefDeflateHdr2 RefDeflateHdr3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma tr_flush_bits_keeps : forall s,
  ds_status (tr_flush_bits s) = ds_status s /\ ds_strm (tr_flush_bits s) = ds_strm s
  /\ ds_lookahead (tr_flush_bits s) = ds_lookahead s /\ ds_wrap (tr_flush_bits s) = ds_wrap s
  /\ ds_level (tr_flush_bits s) = ds_level s /\ ds_strategy (tr_flush_bits s) = ds_strategy s
  /\ ds_last_flush (tr_flush_bits s) = ds_last_flush s /\ ds_strstart (tr_flush_bits s) = ds_strstart s
  /\ ds_gzhead (tr_flush_bits s) = ds_gzhead s /\ ds_w_bits (tr_flush_bits s) = ds_w_bits s.
Proof.
  intros s. unfold tr_flush_bits, bi_flush, put_short.
  (destruct (ds_bi_valid s =? 16); [|destruct (8 <=? ds_bi_valid s)]; destruct s; repeat split; reflexivity).
Qed.

Lemma flush_pending_keeps : forall s,
  ds_status (flush_pending s) = ds_status s
  /\ cs_avail_in (ds_strm (flush_pending s)) = cs_avail_in (ds_strm s)
  /\ ds_lookahead (flush_pending s) = ds_lookahead s
  /\ ds_wrap (flush_pending s) = ds_wrap s
  /\ ds_level (flush_pending s) = ds_level s
  /\ ds_strategy (flush_pending s) = ds_strategy s
  /\ ds_last_flush (flush_pending s) = ds_last_flush s
  /\ ds_strstart (flush_pending s) = ds_strstart s
  /\ ds_gzhead (flush_pending s) = ds_gzhead s
  /\ ds_w_bits (flush_pending s) = ds_w_bits s
  /\ cs_adler (ds_strm (flush_pending s)) = cs_adler (ds_strm s)
  /\ cs_total_in (ds_strm (flush_pending s)) = cs_total_in (ds_strm s).
Proof.
  intros s.
  assert (IFD : forall (f : deflate_state -> Z) (c : bool) (x y : deflate_state), f (if c then x else y) = if c then f x else f y) by (intros f [|] x y; reflexivity).
  assert (IFC : forall (f : deflate_state -> cstrm) (c : bool) (x y : deflate_state), f (if c then x else y) = if c then f x else f y) by (intros f [|] x y; reflexivity).
  assert (IFZ : forall (f : cstrm -> Z) (c : bool) (x y : cstrm), f (if c then x else y) = if c then f x else f y) by (intros f [|] x y; reflexivity).
  assert (IFS : forall (c : bool) (x : Z), (if c then x else x) = x) by (intros [|] x; reflexivity).
  pose proof (tr_flush_bits_keeps s) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  unfold flush_pending. cbv zeta. set (T := tr_flush_bits s) in *.
  (repeat split;
    repeat progress (rewrite ?(IFD ds_status), ?(IFD ds_lookahead), ?(IFD ds_wrap), ?(IFD ds_level), ?(IFD ds_strategy), ?(IFD ds_last_flush),
                             ?(IFD ds_strstart), ?(IFD ds_gzhead), ?(IFD ds_w_bits), ?(IFC ds_strm), ?(IFZ cs_avail_in), ?(IFZ cs_adler), ?(IFZ cs_total_in);
                     cbn [ds_status ds_strm cs_avail_in cs_adler cs_total_in ds_lookahead ds_wrap ds_level ds_strategy ds_last_flush ds_strstart ds_gzhead ds_w_bits
                          set_pending_out set_pending set_strm set_pending_buf set_bi_buf set_bi_valid
                          cset_avail_out cset_total_out cs_emit cset_out_rev]);
    rewrite ?A1, ?A2, ?A3, ?A4, ?A5, ?A6, ?A7, ?A8, ?A9, ?A10; rewrite ?IFS; reflexivity).
Qed.

Lemma put_byte_keeps2 : forall s c,
  ds_level (put_byte s c) = ds_level s /\ ds_strategy (put_byte s c) = ds_strategy s /\ ds_gzhead (put_byte s c) = ds_gzhead s.
Proof. intros s c. destruct s; repeat split; reflexivity. Qed.

Lemma set_strm_keeps : forall s st,
  ds_level (set_strm s st) = ds_level s /\ ds_strategy (set_strm s st) = ds_strategy s /\ ds_gzhead (set_strm s st) = ds_gzhead s
  /\ ds_pending (set_strm s st) = ds_pending s.
Proof. intros s st. destruct s; repeat split; reflexivity. Qed.

Definition gz_xfl (s : deflate_state) : Z :=
  if Z.eqb (ds_level s) 9 then 2
  else if Z.leb Z_HUFFMAN_ONLY (ds_strategy s) || Z.ltb (ds_level s) 2 then 4
  else 0.

Definition gz_s1 (s : deflate_state) : deflate_state :=
  put_byte (put_byte (put_byte (set_strm s (cset_adler (ds_strm s) crc32_init)) 31) 139) 8.

Definition gz_s2 (s : deflate_state) : deflate_state :=
  put_byte (put_byte (put_byte (put_byte (put_byte (put_byte (put_byte (gz_s1 s) 0) 0) 0) 0) 0) (gz_xfl s)) OS_CODE.

Definition gz_s3 (s : deflate_state) : deflate_state := set_status (gz_s2 s) BUSY_STATE.

Lemma gz_s1_keeps : forall s,
  ds_level (gz_s1 s) = ds_level s /\ ds_strategy (gz_s1 s) = ds_strategy s /\ ds_gzhead (gz_s1 s) = ds_gzhead s
  /\ ds_pending (gz_s1 s) = ds_pending s + 3.
Proof.
  intros s. unfold gz_s1.
  rewrite !(proj1 (put_byte_keeps2 _ _)), !(proj1 (proj2 (put_byte_keeps2 _ _))), !(proj2 (proj2 (put_byte_keeps2 _ _))), !pending_put_byte.
  pose proof (set_strm_keeps s (cset_adler (ds_strm s) crc32_init)) as (A & B & C & D). rewrite A, B, C, D.
  repeat split; lia.
Qed.


Definition gzip_s3_spec (s : deflate_state) : deflate_state :=
  let s := set_strm s (cset_adler (ds_strm s) crc32_init) in
  let s := put_byte s 31 in
  let s := put_byte s 139 in
  let s := put_byte s 8 in
  let s := put_byte s 0 in
  let s := put_byte s 0 in
  let s := put_byte s 0 in
  let s := put_byte s 0 in
  let s := put_byte s 0 in
  let s := put_byte s (if Z.eqb (ds_level s) 9 then 2
                       else if Z.leb Z_HUFFMAN_ONLY (ds_strategy s) || Z.ltb (ds_level s) 2 then 4
                       else 0) in
  let s := put_byte s OS_CODE in
  set_status s BUSY_STATE.

Lemma deflate_gzip_header_spec : forall s,
  deflate_gzip_header s =
    (let s := flush_pending (gzip_s3_spec s) in
     if negb (Z.eqb (ds_pending s) 0) then (set_last_flush s (-1), Some Z_OK) else (s, None)).
Proof. intros s. reflexivity. Qed.

Lemma gzip_s3_spec_eq : forall s, gzip_s3_spec s = gz_s3 s.
Proof.
  intros s. unfold gzip_s3_spec, gz_s3, gz_s2, gz_xfl. cbv zeta. fold (gz_s1 s).
  pose proof (gz_s1_keeps s) as (A & B & _ & _).
  rewrite !(proj1 (put_byte_keeps2 _ _)), !(proj1 (proj2 (put_byte_keeps2 _ _))), A, B. reflexivity.
Qed.


Section Hdr.
Variables (ws hs PBL ILEN OCAP : Z).
Variable flush : Z.
Hypothesis Hflush : 0 <= flush < 16.

Definition live_status (st : Z) : Prop := st <> 69 /\ st <> 73 /\ st <> 91 /\ st <> 103.

Definition gzip_pre (s : deflate_state) : Prop :=
  0 <= ds_level s <= 9 /\ 0 <= ds_strategy s <= 4 /\ ds_gzhead s = 0
  /\ 0 <= ds_pending s /\ ds_pending s + 10 <= PBL.

Definition gzip_emit (s : deflate_state) : Prop :=
  let s3 := gzip_s3_spec s in
  fp_ok PBL OCAP s3 /\ 0 <= ds_pending (flush_pending s3) < 2 ^ 63
  /\ 0 <= cs_avail_in (ds_strm (flush_pending s3)) < 2 ^ 32.

Definition gzip_ok (s : deflate_state) : Prop := gzip_pre s /\ gzip_emit s.

End Hdr.
