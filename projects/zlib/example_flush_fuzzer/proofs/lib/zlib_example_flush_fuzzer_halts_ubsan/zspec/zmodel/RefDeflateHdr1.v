(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  TreeModel FillWinModel SendModel BitsModel RefFlushPend1 RefDeflateEnd1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition f1_spec (s : deflate_state) (flush : Z) : option (deflate_state * Z) :=
  if deflateStateCheck s || Z.ltb Z_BLOCK flush || Z.ltb flush 0 then Some (s, Z_STREAM_ERROR)
  else if Z.eqb (ds_status s) FINISH_STATE && negb (Z.eqb flush Z_FINISH) then Some (err_return s Z_STREAM_ERROR)
  else if Z.eqb (cs_avail_out (ds_strm s)) 0 then Some (err_return s Z_BUF_ERROR)
  else None.


Section Hdr.
Variables (ws hs PBL ILEN OCAP : Z).
Variable flush : Z.
Hypothesis Hflush : 0 <= flush < 16.

Lemma f1_spec_eq : forall s, dstatus_ok (ds_status s) -> 0 <= flush ->
  f1_spec s flush = (if 5 <? flush then Some (s, Z_STREAM_ERROR)
                     else if (ds_status s =? FINISH_STATE) && negb (flush =? Z_FINISH)
                          then Some (set_strm s (cset_msg (ds_strm s) (MSG_ERR Z_STREAM_ERROR)), Z_STREAM_ERROR)
                     else if cs_avail_out (ds_strm s) =? 0
                          then Some (set_strm s (cset_msg (ds_strm s) (MSG_ERR Z_BUF_ERROR)), Z_BUF_ERROR)
                     else None).
Proof.
  intros s Hst Hf. unfold f1_spec, err_return, Z_BLOCK.
  rewrite (proj2 (deflateStateCheck_ok s) Hst). rewrite (proj2 (Z.ltb_ge flush 0) Hf). rewrite Bool.orb_false_r. reflexivity.
Qed.

End Hdr.
