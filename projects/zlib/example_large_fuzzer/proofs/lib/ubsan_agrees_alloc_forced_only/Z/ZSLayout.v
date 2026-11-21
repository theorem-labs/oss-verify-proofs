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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Record zs_ptrs : Type := ZSP {
  zp_in : Z; zp_out : Z; zp_zalloc : Z; zp_zfree : Z; zp_opaque : Z; zp_reserved : Z;
  zp_msg : Z -> Z }.

Definition zsl_SIZE : Z := 112.

Definition zsl_layout : list (Z * nat) := [
  (0, 8%nat) (* [comment removed for export] *);
  (8, 4%nat) (* [comment removed for export] *);
  (16, 8%nat) (* [comment removed for export] *);
  (24, 8%nat) (* [comment removed for export] *);
  (32, 4%nat) (* [comment removed for export] *);
  (40, 8%nat) (* [comment removed for export] *);
  (48, 8%nat) (* [comment removed for export] *);
  (56, 8%nat) (* [comment removed for export] *);
  (64, 8%nat) (* [comment removed for export] *);
  (72, 8%nat) (* [comment removed for export] *);
  (80, 8%nat) (* [comment removed for export] *);
  (88, 4%nat) (* [comment removed for export] *);
  (96, 8%nat) (* [comment removed for export] *);
  (104, 8%nat) (* [comment removed for export] *)].

Definition zsl_vals (p : zs_ptrs) (S : Z) (st : cstrm) : list Z := [
  zp_in p + cs_next_in st (* [comment removed for export] *);
  cs_avail_in st (* [comment removed for export] *);
  cs_total_in st (* [comment removed for export] *);
  zp_out p + Z.of_nat (length (cs_out_rev st)) (* [comment removed for export] *);
  cs_avail_out st (* [comment removed for export] *);
  cs_total_out st (* [comment removed for export] *);
  zp_msg p (cs_msg st) (* [comment removed for export] *);
  S (* [comment removed for export] *);
  zp_zalloc p (* [comment removed for export] *);
  zp_zfree p (* [comment removed for export] *);
  zp_opaque p (* [comment removed for export] *);
  cs_data_type st (* [comment removed for export] *);
  cs_adler st (* [comment removed for export] *);
  zp_reserved p (* [comment removed for export] *)].

Section WithImage.
End WithImage.
