(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz TreeModel FillWinModel SendModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition fp_len (s1 : deflate_state) : Z :=
  if cs_avail_out (ds_strm s1) <? ds_pending s1 then cs_avail_out (ds_strm s1) else ds_pending s1.

Definition fp_post (s1 : deflate_state) (len : Z) : deflate_state :=
  let st := ds_strm s1 in
  let st0 := cs_emit st (arr_slice (ds_pending_buf s1) (ds_pending_out s1) len) in
  let s2 := set_pending_out s1 (ds_pending_out s1 + len) in
  let st1 := cset_total_out st0 (wrap64 (cs_total_out st0 + len)) in
  let st2 := cset_avail_out st1 (cs_avail_out st1 - len) in
  let s3 := set_strm s2 st2 in
  let s4 := set_pending s3 (ds_pending s3 - len) in
  if ds_pending s4 =? 0 then set_pending_out s4 0 else s4.

Lemma flush_pending_eq : forall s, 0 <= ds_pending (tr_flush_bits s) < 2 ^ 32 ->
  flush_pending s =
    (let s1 := tr_flush_bits s in
     let len := fp_len s1 in
     if len =? 0 then s1 else fp_post s1 len).
Proof.
  intros s Hp. unfold flush_pending, fp_len, fp_post. cbv zeta.
  rewrite (wrap32_id (ds_pending (tr_flush_bits s))) by exact Hp. reflexivity.
Qed.

Section FP.
Variables (PBL OCAP : Z).
Local Notation outlen st := (Z.of_nat (length (cs_out_rev st))).

Definition fp_ok (s : deflate_state) : Prop :=
  let s1 := tr_flush_bits s in
  let st := ds_strm s1 in
  BINV PBL s /\ 0 <= ds_pending s1 <= PBL /\ 0 <= ds_pending_out s1 /\ ds_pending_out s1 + ds_pending s1 <= PBL
  /\ 0 <= cs_avail_out st < 2 ^ 32 /\ outlen st + cs_avail_out st <= OCAP /\ 0 <= cs_total_out st < 2 ^ 64
  /\ (forall i, 0 <= i < PBL -> 0 <= arr_get (ds_pending_buf s1) i < 256).

Lemma zlength_of_nat : forall {A} (l : list A), zlength l = Z.of_nat (length l).
Proof. reflexivity. Qed.

End FP.
