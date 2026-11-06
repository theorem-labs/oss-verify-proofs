(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: written for zlib/checksum_fuzzer on the frame of the cgif proof's library; 5 of its 29 lines of code, among them its imports, match lines of proofs/cgif/cgif_rgb_fuzzer/lib/YCfw.v up to module paths and module names, and the rest is new. *)
(* Modified by Theorem Labs: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/ZAllocator.v at 25e3d17bdb5059606131377a3722d585415ab5d6 for reac-repacer/fuzz_uci; the unit links no calloc: CallocCert is not required and CAL is the vacuous src0_calloc_none (ms_calloc = None); module path OSSVerify.Proofs.reac_repacer.fuzz_uci.lib. *)
(** Allocator composition adapted from the pinned cgif YZ04 proof, using the
    separately rechecked zlib-specific routine certificates. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
  YK11 YM05 YO0d YH02 YN03 YI5b YI5c YL01 YL0g YL0i YL0s
  YN33 YN0i YN10 YN0x YN23 YN2b YN25 YN0w.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import ZTraceSpec ZComplete.
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
(* the unit links no calloc: src0_msyms has ms_calloc = None (YH02), so calloc_realizes holds vacuously. *)
Lemma src0_calloc_none {fx : FPState} : @calloc_realizes fx rc src0_msyms (MRx src0_msyms).
Proof. intros pc L A regs mem md m n Hc. discriminate Hc. Qed.
Let CAL := fun fx => @src0_calloc_none fx.
Definition zlib_API : AllocAPI src0_msyms := src0_API AMH MSH NTA CAL.
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
