(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBitsLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma upd4_set_pending : forall s A P B V v, set_pending (upd4 s A P B V) v = upd4 s A v B V.
Proof. intros. reflexivity. Qed.
Lemma upd4_set_bi_buf : forall s A P B V v, set_bi_buf (upd4 s A P B V) v = upd4 s A P v V.
Proof. intros. reflexivity. Qed.
Lemma upd4_set_bi_valid : forall s A P B V v, set_bi_valid (upd4 s A P B V) v = upd4 s A P B v.
Proof. intros. destruct s. reflexivity. Qed.
Lemma upd4_set_pending_buf : forall s A P B V v, set_pending_buf (upd4 s A P B V) v = upd4 s v P B V.
Proof. intros. reflexivity. Qed.

Lemma set_bi_buf_upd4_self : forall s j,
  set_bi_buf s j = upd4 s (ds_pending_buf s) (ds_pending s) j (ds_bi_valid s).
Proof. intros. destruct s; reflexivity. Qed.

Lemma upd4_eq_self : forall s A P B V,
  A = ds_pending_buf s -> P = ds_pending s -> B = ds_bi_buf s -> V = ds_bi_valid s -> upd4 s A P B V = s.
Proof. intros; subst. apply upd4_self. Qed.

Lemma upd4_eq_set_bi_buf : forall s A P B V j,
  A = ds_pending_buf s -> P = ds_pending s -> B = j -> V = ds_bi_valid s -> upd4 s A P B V = set_bi_buf s j.
Proof. intros; subst. symmetry. apply set_bi_buf_upd4_self. Qed.


Section Rel4.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Local Notation PB := (p_pending_buf p).
End Rel4.

Lemma wrap16_id' : forall v x, v = x -> 0 <= x < 2 ^ 16 -> v = wrap16 x.
Proof. intros v x -> Hx. rewrite wrap16_mod'. symmetry. apply Z.mod_small. exact Hx. Qed.

Lemma mod16_congr : forall a b, a = b -> a mod 2 ^ 16 = b mod 2 ^ 16.
Proof. intros a b ->. reflexivity. Qed.

Ltac rhs_upd4 :=
  repeat first [ rewrite upd4_set_bi_buf | rewrite upd4_set_bi_valid
               | rewrite upd4_set_pending | rewrite upd4_set_pending_buf | rewrite upd4_upd4 ].

Ltac st_eq4 :=
  rhs_upd4;
  lazymatch goal with
  | |- upd4 ?s _ _ _ _ = upd4 ?s _ _ _ _ => apply upd4_congr
  | |- upd4 ?s _ _ _ _ = set_bi_buf ?s _ => apply upd4_eq_set_bi_buf
  | |- upd4 ?s _ _ _ _ = ?s => apply upd4_eq_self
  end.
