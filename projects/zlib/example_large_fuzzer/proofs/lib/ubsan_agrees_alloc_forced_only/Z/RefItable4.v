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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableModel3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableRod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableCtx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefItable1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefItable2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefItable3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.

(* [comment removed for export] *)
Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

Local Notation SV0 := RefItable1.SV0.
Local Notation slots_in := RefItable1.slots_in.

(* [comment removed for export] *)
Fixpoint spills_ok (SV : list (Z * nat * Z)) (l : list (Z * Z)) : bool :=
  match l with
  | [] => true
  | (o, _) :: l' => (112 <=? o) && (o + 8 <=? 208) && fslots_miss SV o 8 && spills_ok SV l'
  end.

(* [comment removed for export] *)
Definition SV1 (s0v s4v s6v s7v s8v : Z) (l : list (Z * nat * Z)) : list (Z * nat * Z) :=
  (136, 8%nat, s8v) :: (144, 8%nat, s7v) :: (152, 8%nat, s6v) :: (168, 8%nat, s4v) :: (200, 8%nat, s0v) :: l.
Definition SV2 (s9v s10v : Z) (l : list (Z * nat * Z)) : list (Z * nat * Z) :=
  (120, 8%nat, s10v) :: (128, 8%nat, s9v) :: l.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition spillsB (v0 v4 v6 v7 v8 : Z) : list (Z * Z) :=
  [(136, v8); (144, v7); (152, v6); (168, v4); (200, v0)].
End Walk.
