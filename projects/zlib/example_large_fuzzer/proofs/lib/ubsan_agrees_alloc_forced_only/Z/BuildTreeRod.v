(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BvAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition SDA (t : tree_id) : Z := match t with TL => A_static_l_desc | TD => A_static_d_desc | TB => A_static_bl_desc end.
Definition STP (t : tree_id) : Z := match t with TL => A_static_ltree | TD => A_static_dtree | TB => 0 end.
Definition EXP (t : tree_id) : Z := match t with TL => A_extra_lbits | TD => A_extra_dbits | TB => A_extra_blbits end.

(* [comment removed for export] *)
Definition sdesc_w64 (j : Z) : Z :=
  match j with
  | 0 => A_static_ltree | 1 => A_extra_lbits | 2 => 257 + 286 * 2 ^ 32 | 3 => 15
  | 4 => A_static_dtree | 5 => A_extra_dbits | 6 => 0 + 30 * 2 ^ 32 | 7 => 15
  | 8 => 0 | 9 => A_extra_blbits | 10 => 0 + 19 * 2 ^ 32 | _ => 7
  end.

Section Rod.

Local Ltac ua := unfold TREES_ROD_LO, TREES_ROD_HI, A_static_l_desc, A_static_d_desc, A_static_bl_desc,
    A_length_code, A_extra_lbits, A_base_length, A_dist_code, A_extra_dbits, A_base_dist,
    A_static_dtree, A_static_ltree, A_bl_order, A_extra_blbits in *.

(* [comment removed for export] *)
Definition sdesc_w32 (j : Z) : Z :=
  match j with
  | 0 => A_static_ltree | 2 => A_extra_lbits | 4 => 257 | 5 => 286 | 6 => 15
  | 8 => A_static_dtree | 10 => A_extra_dbits | 13 => 30 | 14 => 15
  | 18 => A_extra_blbits | 21 => 19 | 22 => 7
  | _ => 0
  end.

End Rod.
