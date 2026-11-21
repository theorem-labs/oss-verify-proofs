(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  TreeModel FillWinModel SendModel BitsModel RefFlushPend1 RefDeflateEnd1 RefDeflateHdr1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Inductive f2_out : Type :=
  | F2Ret (s' : deflate_state) (rc : Z)
  | F2Hdr (s' : deflate_state)
  | F2Fin (s' : deflate_state).

Definition f2_spec (s : deflate_state) (flush : Z) : f2_out :=
  let old_flush := ds_last_flush s in
  let s := set_last_flush s flush in
  let '(s, r) :=
    if negb (Z.eqb (ds_pending s) 0) then
      let s := flush_pending s in
      if Z.eqb (cs_avail_out (ds_strm s)) 0 then (set_last_flush s (-1), Some Z_OK) else (s, None)
    else if Z.eqb (cs_avail_in (ds_strm s)) 0 && Z.leb (RANK flush) (RANK old_flush)
            && negb (Z.eqb flush Z_FINISH)
    then let '(s, rc) := err_return s Z_BUF_ERROR in (s, Some rc)
    else (s, None) in
  match r with
  | Some rc => F2Ret s rc
  | None =>
    if Z.eqb (ds_status s) FINISH_STATE && negb (Z.eqb (cs_avail_in (ds_strm s)) 0)
    then let '(s, rc) := err_return s Z_BUF_ERROR in F2Ret s rc
    else if Z.eqb (ds_status s) FINISH_STATE then F2Fin s else F2Hdr s
  end.


Section Hdr.
Variables (ws hs PBL ILEN OCAP : Z).
Variable flush : Z.
Hypothesis Hflush : 0 <= flush < 16.

Definition f2_ok (s : deflate_state) : Prop :=
  let s1 := set_last_flush s flush in
  0 <= ds_status s < 2 ^ 10 /\ 0 <= cs_avail_in (ds_strm s) < 2 ^ 32 /\ 0 <= ds_pending s < 2 ^ 63 /\ -2 <= ds_last_flush s <= 5
  /\ 0 <= flush <= 5
  /\ (ds_pending s <> 0 ->
        fp_ok PBL OCAP s1
        /\ 0 <= cs_avail_out (ds_strm (flush_pending s1)) < 2 ^ 32
        /\ 0 <= ds_status (flush_pending s1) < 2 ^ 10 /\ 0 <= cs_avail_in (ds_strm (flush_pending s1)) < 2 ^ 32).

End Hdr.
