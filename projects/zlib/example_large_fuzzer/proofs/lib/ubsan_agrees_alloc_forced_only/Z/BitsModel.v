(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lor_mod_pow2 : forall a b n, 0 <= n ->
  (Z.lor a b) mod 2 ^ n = Z.lor (a mod 2 ^ n) (b mod 2 ^ n).
Proof.
  intros a b n Hn. rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l.
Qed.

Lemma mod_pow2_mod_pow2 : forall x m n, 0 <= n <= m -> (x mod 2 ^ m) mod 2 ^ n = x mod 2 ^ n.
Proof.
  intros x m n H. apply Z.mod_mod_divide.
  exists (2 ^ (m - n)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma wrap16_mod' : forall z, wrap16 z = z mod 2 ^ 16.
Proof. intros. rewrite wrap16_mod. reflexivity. Qed.
Lemma wrap8_mod' : forall z, wrap8 z = z mod 2 ^ 8.
Proof. intros. rewrite wrap8_mod. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wrap8_land255 : forall w, wrap8 (Z.land w 255) = wrap8 w.
Proof. intros w. unfold wrap8. rewrite <- Z.land_assoc. rewrite Z.land_diag. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

