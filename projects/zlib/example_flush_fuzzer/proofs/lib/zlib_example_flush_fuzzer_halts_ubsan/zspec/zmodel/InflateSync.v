(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint syncsearch_loop (buf : list Z) (got next : Z) : Z * Z :=
  match buf with
  | [] => (got, next)
  | b :: rest =>
      if Z.ltb got 4 then
        let got := if Z.eqb b (if Z.ltb got 2 then 0 else 255) then got + 1
                   else if negb (Z.eqb b 0) then 0
                   else 4 - got in
        syncsearch_loop rest got (next + 1)
      else (got, next)
  end.

Definition syncsearch (have : Z) (buf : list Z) : Z * Z := syncsearch_loop buf have 0.

Fixpoint sync_drain (fuel : nat) (s : inflate_state) (acc : list Z) : inflate_state * list Z :=
  match fuel with
  | O => (s, acc)
  | S f =>
      if Z.leb 8 (is_bits s) then
        let b := Z.land (is_hold s) 255 in
        let s := iset_hold s (Z.shiftr (is_hold s) 8) in
        let s := iset_bits s (is_bits s - 8) in
        sync_drain f s (acc ++ [b])
      else (s, acc)
  end.

Section WithVariant.
  Variable iv : ivariant.

  Definition inflateSync_m (s : inflate_state) (zc : ZCall) : inflate_state * ZRet :=
    let z := zc_strm zc in
    let input := zc_input zc in
    if inflateStateCheck s then (s, mkZRet 0 [] z Z_STREAM_ERROR)
    else if Z.eqb (zlength input) 0 && Z.ltb (is_bits s) 8 then (s, mkZRet 0 [] z Z_BUF_ERROR)
    else
      let s :=
        if negb (Z.eqb (is_mode s) SYNC) then
          let s := iset_mode s SYNC in
          let k := Z.land (is_bits s) 7 in
          let s := iset_hold s (Z.shiftr (is_hold s) k) in
          let s := iset_bits s (is_bits s - k) in
          let '(s, buf) := sync_drain (S (Z.to_nat (Z.shiftr (is_bits s) 3))) s [] in
          let s := iset_have s 0 in
          let '(got, _) := syncsearch (is_have s) buf in
          iset_have s got
        else s in
      let '(got, len) := syncsearch (is_have s) input in
      let s := iset_have s got in
      let z := zs_set_total_in (wrap64 (zs_total_in z + len)) z in
      if negb (Z.eqb (is_have s) 4) then (s, mkZRet len [] z Z_DATA_ERROR)
      else
        let s := if Z.eqb (is_flags s) (-1) then iset_wrap s 0
                 else iset_wrap s (Z.land (is_wrap s) (Z.lnot 4)) in
        let flags := is_flags s in
        let in_ := zs_total_in z in
        let out := zs_total_out z in
        let '(s, z, _) := inflateReset iv s z in
        let z := zs_set_total_in in_ (zs_set_total_out out z) in
        let s := iset_flags s flags in
        let s := iset_mode s TYPE in
        (s, mkZRet len [] z Z_OK).
End WithVariant.
