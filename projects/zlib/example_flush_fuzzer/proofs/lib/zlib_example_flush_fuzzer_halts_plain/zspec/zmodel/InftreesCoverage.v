(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState Inftrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition it_room (ty : codetype) : Z :=
  match ty with CODES => 128 | LENS => ENOUGH_LENS | DISTS => ENOUGH_DISTS end.

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

End Stmts.


