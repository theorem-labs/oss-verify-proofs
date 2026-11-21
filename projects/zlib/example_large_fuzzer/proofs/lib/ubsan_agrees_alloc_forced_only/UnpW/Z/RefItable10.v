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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefItable4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefItable5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefItable6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefItable7.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefItable8.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefItable9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma shl32c_shr31 : forall d c k, c = k * 4294967296 -> (d * 2 ^ 32 + c) / 2 ^ 31 = 2 * (d + k).
Proof.
  intros d c k ->. replace (d * 2 ^ 32 + k * 4294967296) with ((2 * (d + k)) * 2 ^ 31) by lia.
  rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma shl32c_shr31' : forall d c k, c = k * 4294967296 -> 0 <= d + k < 2 ^ 31 ->
  (d * 2 ^ 32 + c) mod 2 ^ 64 / 2 ^ 31 = 2 * (d + k).
Proof.
  intros d c k Hc Hb. rewrite Z.mod_small by (subst c; split; [nia|]; change (2 ^ 64) with (2 ^ 31 * 2 ^ 33); nia).
  apply shl32c_shr31. exact Hc.
Qed.

Ltac norm_shl32 :=
  repeat match goal with
  | |- context [(?d * 2 ^ 32 + ?c) mod 2 ^ 64 / 2 ^ 31] =>
      let k := eval vm_compute in (c / 4294967296) in
      rewrite (shl32c_shr31' d c k eq_refl) by lia
  | |- context [(?d * 2 ^ 32 + ?c) / 2 ^ 31] =>
      let k := eval vm_compute in (c / 4294967296) in
      rewrite (shl32c_shr31 d c k eq_refl)
  end.

(* [comment removed for export] *)

Section Walk.

(* [comment removed for export] *)
Local Ltac lia2 := rewrite ?Z.pow_1_r in *; lia.

End Walk.
