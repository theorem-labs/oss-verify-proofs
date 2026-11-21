(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require Import Prog ZIface InflateState Inftrees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition it_room (ty : codetype) : Z :=
  match ty with CODES => 128 | LENS => ENOUGH_LENS | DISTS => ENOUGH_DISTS end.


Section Stmts.
  Variables (ty : codetype) (lens1 lens2 : arr) (lens_ofs codes : Z)
            (tbl1 tbl2 : arr) (table bits : Z) (work1 work2 : arr).


  Let r1 := inflate_table ty lens1 lens_ofs codes tbl1 table bits work1.
  Let r2 := inflate_table ty lens2 lens_ofs codes tbl2 table bits work2.
  Let ret1 := fst (fst (fst (fst r1))).   Let ret2 := fst (fst (fst (fst r2))).
  Let tbl1' := snd (fst (fst (fst r1))).  Let tbl2' := snd (fst (fst (fst r2))).
  Let table1' := snd (fst (fst r1)).     Let table2' := snd (fst (fst r2)).
  Let bits1' := snd (fst r1).            Let bits2' := snd (fst r2).




End Stmts.



