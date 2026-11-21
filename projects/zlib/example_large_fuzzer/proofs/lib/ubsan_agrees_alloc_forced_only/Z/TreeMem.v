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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Export TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section WithSegs.

(* [comment removed for export] *)
Fixpoint layout_gap (L : list (Z * nat)) (lo hi : Z) : bool :=
  match L with
  | [] => true
  | (o, w) :: L' => ((o + Z.of_nat w <=? lo) || (hi <=? o)) && layout_gap L' lo hi
  end.

(* [comment removed for export] *)

Section Scalars.
Variables SL SD SB : Z.
End Scalars.

End WithSegs.

(* [comment removed for export] *)
Definition hv (h : arr) (i : Z) : Z := (arr_get h i) mod 573.

Lemma hv_get : forall h i, 0 <= arr_get h i < 573 -> hv h i = arr_get h i.
Proof. intros h i H. unfold hv. apply Z.mod_small. exact H. Qed.

Section Reads.
End Reads.

(* [comment removed for export] *)
Ltac arr_range_auto :=
  first [ lia
        | match goal with
          | R : forall j, _ -> 0 <= arr_get ?a j < _ |- 0 <= arr_get ?a _ < _ => apply R; lia
          | R : forall j, _ -> 0 <= arr_get ?a j < _ |- 0 <= arr_get ?a _ < _ =>
              eapply (fun j H => proj1 (conj (R j H) I)); lia
          end
        | match goal with
          | R : forall j, _ -> 0 <= arr_get ?a j < ?B |- 0 <= arr_get ?a ?i < ?C =>
              let H := fresh in pose proof (R i) as H; lia
          end ].
