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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Rel.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Local Notation PB := (p_pending_buf p).

End Rel.

Section Rel2.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Local Notation PB := (p_pending_buf p).

End Rel2.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma upd4_congr : forall s A A' P P' B B' V V',
  A = A' -> P = P' -> B = B' -> V = V' -> upd4 s A P B V = upd4 s A' P' B' V'.
Proof. intros; subst; reflexivity. Qed.

Ltac u4 t :=
  lazymatch t with
  | set_bi_valid ?t1 ?v =>
      let r := u4 t1 in lazymatch r with upd4 ?s ?A ?P ?B ?V => constr:(upd4 s A P B v) end
  | set_bi_buf ?t1 ?v =>
      let r := u4 t1 in lazymatch r with upd4 ?s ?A ?P ?B ?V => constr:(upd4 s A P v V) end
  | set_pending ?t1 ?v =>
      let r := u4 t1 in lazymatch r with upd4 ?s ?A ?P ?B ?V => constr:(upd4 s A v B V) end
  | set_pending_buf ?t1 ?v =>
      let r := u4 t1 in lazymatch r with upd4 ?s ?A ?P ?B ?V => constr:(upd4 s v P B V) end
  | upd4 _ _ _ _ _ => t
  | ?s => constr:(upd4 s (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s))
  end.

Ltac st_eq :=
  lazymatch goal with
  | |- ?a = ?b =>
      let a' := u4 a in let b' := u4 b in
      change (a' = b'); apply upd4_congr; dsred
  end.
