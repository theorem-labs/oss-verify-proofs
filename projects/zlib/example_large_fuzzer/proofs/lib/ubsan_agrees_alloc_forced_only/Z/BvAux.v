(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod_pow2_mod_pow2 : forall x n m, 0 <= m <= n ->
  (x mod 2^n) mod 2^m = x mod 2^m.
Proof.
  intros x n m H. apply Z.bits_inj'. intros k Hk.
  destruct (Z.lt_ge_cases k m) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)

