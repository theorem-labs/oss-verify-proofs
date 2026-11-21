(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition it_room (ty : codetype) : Z :=
  match ty with CODES => 128 | LENS => ENOUGH_LENS | DISTS => ENOUGH_DISTS end.

Definition may_link (e : Z) : bool :=
  (Z.land (code_op e) 240 =? 0) || ((Z.land (code_op e) 16 =? 0) && (Z.land (code_op e) 64 =? 0)).

Definition it_ty_ok (ty : codetype) (lens : arr) (lens_ofs codes bits : Z) : Prop :=
  match ty with
  | CODES => codes <= 19 /\ 7 <= bits /\ (forall i, lens_ofs <= i < lens_ofs + codes -> arr_get lens i <= 7)
  | LENS => codes <= 288
  | DISTS => codes <= 32
  end.

Definition nsyms (ty : codetype) : Z := match ty with CODES => 19 | LENS => 288 | DISTS => 32 end.

Definition sym_entry (ty : codetype) (s : Z) : Z * Z :=
  match ty with
  | CODES => (0, s)
  | LENS => if s <? 256 then (0, s)
            else if s =? 256 then (96, 0)
            else (nth (Z.to_nat (s - 257)) lext_l 0, nth (Z.to_nat (s - 257)) lbase_l 0)
  | DISTS => (nth (Z.to_nat s) dext_l 0, nth (Z.to_nat s) dbase_l 0)
  end.

Definition entry_shape (ty : codetype) (root used x e : Z) : Prop :=
  (exists s len,
     0 <= s < nsyms ty /\ 1 <= len <= 15 /\
     code_op e = fst (sym_entry ty s) /\ code_val e = snd (sym_entry ty s) /\
     ((x < 2 ^ root /\ len <= root /\ code_bits e = len) \/
      (2 ^ root <= x /\ root < len /\ code_bits e = len - root)))
  \/ (x < 2 ^ root /\ code_bits e = root /\ 1 <= code_op e <= 15 - root /\
      2 ^ root <= code_val e /\ code_val e + 2 ^ code_op e <= used)
  \/ (code_op e = 64 /\ code_bits e = 1 /\ code_val e = 0 /\ root = 1).

Section Stmts.
  Variable ty : codetype.
Variable lens1 : arr.
Variable lens2 : arr.
Variable lens_ofs : Z.
Variable codes : Z.
Variable tbl1 : arr.
Variable tbl2 : arr.
Variable table : Z.
Variable bits : Z.
Variable work1 : arr.
Variable work2 : arr.

  Definition it_inputs_related : Prop :=
    arr_len tbl1 = arr_len tbl2 /\ arr_len work1 = arr_len work2 /\
    0 <= codes <= 288 /\ codes <= arr_len work1 /\
    0 <= table /\ table + it_room ty <= arr_len tbl1 /\
    1 <= bits <= 15 /\
    (forall i, lens_ofs <= i < lens_ofs + codes -> arr_get lens1 i = arr_get lens2 i) /\
    (forall i, lens_ofs <= i < lens_ofs + codes -> 0 <= arr_get lens1 i <= 15) /\
    it_ty_ok ty lens1 lens_ofs codes bits.

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
       1 <= bits1' <= 15 /\
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

  Definition it_shapes_stmt : Prop :=
    it_inputs_related -> ret1 = 0 ->
    forall i, table <= i < table1' ->
      entry_shape ty bits1' (table1' - table) (i - table) (arr_get tbl1' i).
End Stmts.


Definition inftrees_coverage : Prop :=
  forall ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2,
    it_coverage_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2 /\
    it_links_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2 /\
    it_nochain_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2 /\
    it_lens_values_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2.

Definition inftrees_shapes : Prop :=
  forall ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2,
    it_shapes_stmt ty lens1 lens2 lens_ofs codes tbl1 tbl2 table bits work1 work2.
