(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Allocator composition adapted from the pinned cgif YZ04 proof, using the
    separately rechecked zlib-specific routine certificates. *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
  YK11 YM05 YO0d YH02 YN03 YI5b YI5c YL01 YL0g YL0i YL0s
  YN33 YN0i YN10 YN0x YN23 YN2b YN25 YN0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require Import ZTraceSpec ZComplete.
Section Allocator.
Context {rc : RunCeil}.
Let AMH : forall fx : FPState, @alloc_meta_hyp fx rc src0_msyms :=
  fun fx => @src0_alloc_meta fx rc.
Let ASH : forall fx : FPState, @alloc_slot_hyp fx rc src0_msyms :=
  fun fx => @src0_alloc_slot fx rc.
Let MSH : forall fx : FPState, @malloc_small_hyp fx rc src0_msyms :=
  fun fx => @src0_malloc_small fx rc (ASH fx).
Let NTA : forall fx : FPState, @YN0w.ntA_hyp fx rc src0_msyms :=
  fun fx => @src0_ntA fx rc.
Definition zlib_API : AllocAPI src0_msyms := src0_API AMH MSH NTA.
Theorem zlib_allocator_extra : AllocExtra src0_msyms (aa_MR zlib_API).
Proof. apply MRx_AllocExtra. Qed.
End Allocator.
Definition zlib_checksum_contract : Prop := forall rc : RunCeil,
  @lib_contract_x_all rc checksum_shape src0_msyms (@zlib_API rc)
    src0_sink_head src0_sink LIBPC RA_LIB EMPTY LIB_STACK.
Theorem runtime_contracts_from_checksum :
  zlib_checksum_contract -> zlib_runtime_contracts.
Proof.
  intros H rc. exists (@zlib_API rc). split.
  - apply zlib_allocator_extra.
  - apply H.
Qed.
