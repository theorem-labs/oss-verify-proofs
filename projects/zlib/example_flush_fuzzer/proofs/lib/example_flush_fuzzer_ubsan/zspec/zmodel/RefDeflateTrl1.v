(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  TreeModel FillWinModel SendModel BitsModel RefFlushPend1 RefDeflateEnd1 RefDeflateHdrKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).




Section Trl.
Variables (ws hs PBL ILEN OCAP : Z).
Variable flush : Z.
Hypothesis Hflush : 0 <= flush < 16.

Definition ta_post (s : deflate_state) : deflate_state :=
  let a := cs_adler (ds_strm s) in
  put_byte (put_byte (put_byte (put_byte s (a / 2 ^ 24)) (a / 2 ^ 16)) (a / 2 ^ 8)) a.

Definition tb_post (s : deflate_state) : deflate_state :=
  let a := cs_adler (ds_strm s) in
  let t := cs_total_in (ds_strm s) in
  put_byte (put_byte (put_byte (put_byte (put_byte (put_byte (put_byte (put_byte s
    a) (a / 2 ^ 8)) (a / 2 ^ 16)) (a / 2 ^ 24)) t) (t / 2 ^ 8)) (t / 2 ^ 16)) (t / 2 ^ 24).

Definition td_post (s : deflate_state) : deflate_state :=
  if 0 <? ds_wrap s then set_wrap s (- ds_wrap s) else s.

Lemma ta_post_eq : forall s, 0 <= cs_adler (ds_strm s) < 2 ^ 32 ->
  putShortMSB (putShortMSB s (wrap32 (Z.shiftr (cs_adler (ds_strm s)) 16))) (Z.land (cs_adler (ds_strm s)) 65535) = ta_post s.
Proof.
  intros s Ha. unfold putShortMSB, ta_post. cbv zeta.
  rewrite (byte_hi_hi _ Ha).
  rewrite (put_byte_congr (put_byte s _) _ (cs_adler (ds_strm s) / 2 ^ 16) (byte_hi_lo _ Ha)).
  rewrite (put_byte_congr (put_byte (put_byte s _) _) _ (cs_adler (ds_strm s) / 2 ^ 8) (byte_lo_hi (cs_adler (ds_strm s)) ltac:(lia))).
  rewrite (put_byte_congr (put_byte (put_byte (put_byte s _) _) _) _ (cs_adler (ds_strm s)) (byte_lo_lo (cs_adler (ds_strm s)) ltac:(lia))).
  reflexivity.
Qed.

Lemma tb_post_eq : forall s, 0 <= cs_adler (ds_strm s) -> 0 <= cs_total_in (ds_strm s) ->
  (let a := cs_adler (ds_strm s) in let t := cs_total_in (ds_strm s) in
   let s := put_byte s (Z.land a 255) in
   let s := put_byte s (Z.land (Z.shiftr a 8) 255) in
   let s := put_byte s (Z.land (Z.shiftr a 16) 255) in
   let s := put_byte s (Z.land (Z.shiftr a 24) 255) in
   let s := put_byte s (Z.land t 255) in
   let s := put_byte s (Z.land (Z.shiftr t 8) 255) in
   let s := put_byte s (Z.land (Z.shiftr t 16) 255) in
   put_byte s (Z.land (Z.shiftr t 24) 255)) = tb_post s.
Proof.
  intros s Ha Ht. unfold tb_post. cbv zeta.
  rewrite (put_byte_congr s _ (cs_adler (ds_strm s)) (byte_land _)).
  rewrite (put_byte_congr (put_byte _ _) (Z.land (Z.shiftr (cs_adler (ds_strm s)) 8) 255) _ (byte_shr _ 8 Ha ltac:(lia))).
  rewrite (put_byte_congr (put_byte _ _) (Z.land (Z.shiftr (cs_adler (ds_strm s)) 16) 255) _ (byte_shr _ 16 Ha ltac:(lia))).
  rewrite (put_byte_congr (put_byte _ _) (Z.land (Z.shiftr (cs_adler (ds_strm s)) 24) 255) _ (byte_shr _ 24 Ha ltac:(lia))).
  rewrite (put_byte_congr (put_byte _ _) _ (cs_total_in (ds_strm s)) (byte_land _)).
  rewrite (put_byte_congr (put_byte _ _) (Z.land (Z.shiftr (cs_total_in (ds_strm s)) 8) 255) _ (byte_shr _ 8 Ht ltac:(lia))).
  rewrite (put_byte_congr (put_byte _ _) (Z.land (Z.shiftr (cs_total_in (ds_strm s)) 16) 255) _ (byte_shr _ 16 Ht ltac:(lia))).
  rewrite (put_byte_congr (put_byte _ _) (Z.land (Z.shiftr (cs_total_in (ds_strm s)) 24) 255) _ (byte_shr _ 24 Ht ltac:(lia))).
  reflexivity.
Qed.

Lemma pending_td_post : forall s, ds_pending (td_post s) = ds_pending s.
Proof. intros s. unfold td_post. destruct (0 <? ds_wrap s); [destruct s|]; reflexivity. Qed.

Lemma deflate_trailer_eq : forall s, 0 <= cs_adler (ds_strm s) < 2 ^ 32 -> 0 <= cs_total_in (ds_strm s) ->
  deflate_trailer s =
    (let s2 := flush_pending (if ds_wrap s =? 2 then tb_post s else ta_post s) in
     (td_post s2, if negb (ds_pending (td_post s2) =? 0) then Z_OK else Z_STREAM_END)).
Proof.
  intros s Ha Ht. cbv delta [deflate_trailer]. cbv beta. cbv zeta.
  rewrite <- (ta_post_eq s Ha). pose proof (tb_post_eq s ltac:(lia) Ht) as E. cbv zeta in E. rewrite <- E.
  unfold td_post. destruct (ds_wrap s =? 2); reflexivity.
Qed.

Definition trl_pre (s : deflate_state) : Prop :=
  -2 <= ds_wrap s <= 2 /\ 0 <= ds_pending s <= PBL /\ 0 <= cs_adler (ds_strm s) < 2 ^ 32 /\ 0 <= cs_total_in (ds_strm s) < 2 ^ 64.

Definition trl_emit (s : deflate_state) : Prop :=
  let st := ds_strm s in
  let s1 := (if Z.eqb (ds_wrap s) 2 then
               let a := cs_adler st in let t := cs_total_in st in
               let s := put_byte s (Z.land a 255) in
               let s := put_byte s (Z.land (Z.shiftr a 8) 255) in
               let s := put_byte s (Z.land (Z.shiftr a 16) 255) in
               let s := put_byte s (Z.land (Z.shiftr a 24) 255) in
               let s := put_byte s (Z.land t 255) in
               let s := put_byte s (Z.land (Z.shiftr t 8) 255) in
               let s := put_byte s (Z.land (Z.shiftr t 16) 255) in
               put_byte s (Z.land (Z.shiftr t 24) 255)
             else
               let a := cs_adler st in
               let s := putShortMSB s (wrap32 (Z.shiftr a 16)) in
               putShortMSB s (Z.land a 65535)) in
  ds_pending s + (if Z.eqb (ds_wrap s) 2 then 8 else 4) <= PBL
  /\ fp_ok PBL OCAP s1
  /\ -2 <= ds_wrap (flush_pending s1) <= 2 /\ 0 <= ds_pending (flush_pending s1) < 2 ^ 63.

Definition trl_ok (s : deflate_state) : Prop :=
  trl_pre s /\ (flush = Z_FINISH -> 0 < ds_wrap s -> trl_emit s).

End Trl.
