From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import
  YK11 YM05 YO0d YH02 YN03 YI5b YI5c YL01 YL0g YL0i YL0s
  YN33 YN0i YN10 YN0x YN23 YN2b YN25 YN0w YN0e YN06 YN09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import ZTraceSpec ZComplete ZCompleteMF ZAllocator.
Definition zlib_mf_allocator : Prop := forall rc : RunCeil, mf_alloc_facts (@zlib_API rc).
Theorem zlib_mf_allocator_holds : zlib_mf_allocator.
Proof.
  intros rc. split; [|split].
  - intros fx. exact (@src0_malloc_realizes fx rc MayFail (@src0_alloc_meta fx rc MayFail)
      (@src0_malloc_small fx rc MayFail (@src0_alloc_slot fx rc MayFail))).
  - intros fx. exact (@src0_free_realizes fx rc MayFail (@src0_ntfree_of_A fx rc MayFail (@src0_ntA fx rc MayFail))).
  - intros fx. exact (@src0_free_null fx MayFail).
Qed.
