(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import Prog ZIface InflateState Inftrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition it_room (ty : codetype) : Z :=
  match ty with CODES => 128 | LENS => ENOUGH_LENS | DISTS => ENOUGH_DISTS end.

Definition may_link (e : Z) : bool :=
  (Z.land (code_op e) 240 =? 0) || ((Z.land (code_op e) 16 =? 0) && (Z.land (code_op e) 64 =? 0)).

Section Stmts.
  Variables (ty : codetype) (lens1 lens2 : arr) (lens_ofs codes : Z)
            (tbl1 tbl2 : arr) (table bits : Z) (work1 work2 : arr).

  Definition it_inputs_related : Prop :=
    arr_len tbl1 = arr_len tbl2 /\ arr_len work1 = arr_len work2 /\
    0 <= codes <= 288 /\ codes <= arr_len work1 /\
    0 <= table /\ table + it_room ty <= arr_len tbl1 /\
    1 <= bits <= 15 /\
    (forall i, lens_ofs <= i < lens_ofs + codes -> arr_get lens1 i = arr_get lens2 i) /\
    (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens1 i <= 15) /\
    (ty = CODES -> codes <= 19 /\ bits = 7 /\ forall i, lens_ofs <= i < lens_ofs + codes -> arr_get lens1 i <= 7) /\
    (ty = DISTS -> codes <= 32).

  Let r1 := inflate_table ty lens1 lens_ofs codes tbl1 table bits work1.
  Let r2 := inflate_table ty lens2 lens_ofs codes tbl2 table bits work2.
  Let ret1 := fst (fst (fst (fst r1))).   Let ret2 := fst (fst (fst (fst r2))).
  Let tbl1' := snd (fst (fst (fst r1))).  Let tbl2' := snd (fst (fst (fst r2))).
  Let table1' := snd (fst (fst r1)).     Let table2' := snd (fst (fst r2)).
  Let bits1' := snd (fst r1).            Let bits2' := snd (fst r2).

  Definition it_coverage_stmt : Prop :=
    it_inputs_related ->
    ret1 = ret2 /\
    (ret1 = 0 ->
       table1' = table2' /\ bits1' = bits2' /\
       1 <= bits1' <= bits /\
       table + Z.shiftl 1 bits1' <= table1' <= table + it_room ty /\
       (forall i, table <= i < table1' -> arr_get tbl1' i = arr_get tbl2' i) /\
       (forall i, ~ (table <= i < table1') -> arr_get tbl1' i = arr_get tbl1 i /\ arr_get tbl2' i = arr_get tbl2 i)).

  Definition it_links_stmt : Prop :=
    it_inputs_related -> ret1 = 0 ->
    forall x, 0 <= x < Z.shiftl 1 bits1' ->
      let e := arr_get tbl1' (table + x) in
      may_link e = true -> code_op e <> 0 ->
      1 <= code_op e <= 15 /\
      Z.shiftl 1 bits1' <= code_val e /\
      table + code_val e + Z.shiftl 1 (code_op e) <= table1'.

  Definition it_nochain_stmt : Prop :=
    it_inputs_related -> ret1 = 0 ->
    forall i, table + Z.shiftl 1 bits1' <= i < table1' ->
      let e := arr_get tbl1' i in may_link e = true -> code_op e = 0.

  Definition it_lens_values_stmt : Prop :=
    it_inputs_related -> ret1 = 0 -> ty = LENS ->
    forall i, table <= i < table1' ->
      let e := arr_get tbl1' i in
      16 <= code_op e < 32 -> code_val e + Z.shiftl 1 (Z.land (code_op e) 15) - 1 <= 258.
End Stmts.



Definition inftrees_coverage : Prop :=
  forall ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2,
    it_coverage_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2 /\
    it_links_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2 /\
    it_nochain_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2 /\
    it_lens_values_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2.
