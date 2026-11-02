(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: written for zlib/checksum_fuzzer on the frame of the cgif proof's library; 5 of its 29 lines of code, among them its imports, match lines of proofs/cgif/cgif_rgb_fuzzer/lib/YCfw.v up to module paths and module names, and the rest is new. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
(** Allocator composition adapted from the pinned cgif YZ04 proof, using the
    separately rechecked zlib-specific routine certificates. *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI5b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI5c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN33.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN23.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import ZTraceSpec.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import ZComplete.
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
