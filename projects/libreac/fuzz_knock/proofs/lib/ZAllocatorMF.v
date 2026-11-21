From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
  YK11 YM05 YO0d YH02 YN03 YI5b YI5c YL01 YL0g YL0i YL0s
  YN33 YN0i YN10 YN0x YN23 YN2b YN25 YN0w YN0e YN06 YN09.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import ZTraceSpec ZComplete ZCompleteMF ZAllocator CallocCert.
(* The may-fail allocator: the same routine certificates as [ZAllocator.zlib_API], at [MayFail].  Its
   ledger is [MRx] at [MayFail], where the three counting fields of [ledger_ok] and the two of
   [ledger_x] are vacuous, so a free whose munmap answers ENOMEM may leave its mapping behind. *)
Section AllocatorMF.
Context {rc : RunCeil}.
Let AMHm : forall fx : FPState, @alloc_meta_hyp fx rc MayFail src0_msyms :=
  fun fx => @src0_alloc_meta fx rc MayFail.
Let ASHm : forall fx : FPState, @alloc_slot_hyp fx rc MayFail src0_msyms :=
  fun fx => @src0_alloc_slot fx rc MayFail.
Let MSHm : forall fx : FPState, @malloc_small_hyp fx rc MayFail src0_msyms :=
  fun fx => @src0_malloc_small fx rc MayFail (ASHm fx).
Let NTAm : forall fx : FPState, @YN0w.ntA_hyp fx rc MayFail src0_msyms :=
  fun fx => @src0_ntA fx rc MayFail.
Let CALm := fun fx => @src0_calloc_realizes fx rc MayFail.
Definition zlib_API_mf : @AllocAPI rc MayFail src0_msyms := src0_API (AM:=MayFail) AMHm MSHm NTAm CALm.
Theorem zlib_allocator_extra_mf : AllocExtra src0_msyms (aa_MR zlib_API_mf).
Proof. apply MRx_AllocExtra. Qed.
End AllocatorMF.
Definition zlib_mf_allocator : Prop := forall rc : RunCeil, mf_alloc_facts (@zlib_API_mf rc).
Theorem zlib_mf_allocator_holds : zlib_mf_allocator.
Proof.
  intros rc. split; [|split].
  - intros fx. exact (@src0_malloc_realizes fx rc MayFail (@src0_alloc_meta fx rc MayFail)
      (@src0_malloc_small fx rc MayFail (@src0_alloc_slot fx rc MayFail))).
  - intros fx. exact (@src0_free_realizes fx rc MayFail (@src0_ntfree_of_A fx rc MayFail (@src0_ntA fx rc MayFail))).
  - intros fx. exact (@src0_free_null fx MayFail).
Qed.
