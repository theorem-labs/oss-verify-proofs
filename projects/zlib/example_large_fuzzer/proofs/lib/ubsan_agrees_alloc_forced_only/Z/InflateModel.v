(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Uncompr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition inflate_model_at (iv : ivariant) : inflate_api inflate_state :=
  mkInflateApi
    (fun St hooks => @inflateInit2_m iv St hooks)
    (fun St hooks => @inflate_m iv St hooks)
    (fun St hooks => @inflateSetDictionary_m St hooks)
    (fun St hooks => @inflateEnd_m St hooks)
    (fun St hooks => @uncompress2_m iv St hooks).

(* [comment removed for export] *)
Definition inflate_model_ref : inflate_api inflate_state := inflate_model_at ivar_ref.
(* [comment removed for export] *)
Definition inflate_model_agent : inflate_api inflate_state := inflate_model_at ivar_agent.
