From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
  YK11 YM05 YO0d YH02 YN03 YI5b YI5c YL01 YL0g YL0i YL0s
  YN33 YN0i YN10 YN0x YN23 YN2b YN25 YN0w YN0e YN06 YN09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import ZTraceSpec ZComplete ZCompleteMF ZAllocator CallocCert.
(* 08b1429: the may-fail walks run over an allocator record at MayFail, whose invariant is MRx at MayFail: after a
   refused munmap (musl's free and malloc ignore munmap's answer) the ledger keeps a map whose region is dead, and
   MRx at AcfgMode does not hold there (YN03.ledger_ok).  zlib_API_mf is built from the same mode-generic src0
   certificates as ZAllocator's zlib_API. *)
Section Allocator.
Context {rc : RunCeil}.
Definition zlib_API_mf : @AllocAPI rc MayFail src0_msyms :=
  @src0_API rc MayFail (fun fx => @src0_alloc_meta fx rc MayFail)
    (fun fx => @src0_malloc_small fx rc MayFail (@src0_alloc_slot fx rc MayFail))
    (fun fx => @src0_ntA fx rc MayFail)
    (fun fx => @src0_calloc_realizes_m fx rc MayFail).
Theorem zlib_allocator_extra_mf : AllocExtra src0_msyms (aa_MR zlib_API_mf).
Proof. apply MRx_AllocExtra. Qed.
End Allocator.
Definition zlib_mf_allocator : Prop := forall rc : RunCeil, mf_alloc_facts (@zlib_API_mf rc).
Theorem zlib_mf_allocator_holds : zlib_mf_allocator.
Proof.
  intros rc. split; [|split].
  - intros fx. exact (@aa_malloc rc MayFail src0_msyms (@zlib_API_mf rc) fx).
  - intros fx. exact (@aa_free rc MayFail src0_msyms (@zlib_API_mf rc) fx).
  - intros fx. exact (@aa_free_null rc MayFail src0_msyms (@zlib_API_mf rc) fx).
Qed.
