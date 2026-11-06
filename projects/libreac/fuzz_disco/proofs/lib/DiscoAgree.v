From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_disco Require Statements.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import
  ZTraceSpec ZAllocator Contract FrameAPI AllocSlots AllocRoom SlotAgree AgreeShape AgreeFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require FrameProof SlotTopG.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require FrameProof SlotTopG ZAllocator AllocCf AgreeZlib FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require LLVMFuzzerTestOneInput_c DiscoEnd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require LLVMFuzzerTestOneInput_c DiscoEndCg.
Import ListNotations.
Open Scope Z_scope.

Local Abbreviation P_B := OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YH02.src0_msyms.
Local Abbreviation P_API := (@OSSVerify.Proofs.libreac.fuzz_disco.lib.ZAllocator.zlib_API).
Local Abbreviation P_SH := OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YI5b.src0_sink_head.
Local Abbreviation P_SK := OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YI5c.src0_sink.
Local Abbreviation P_RA := OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YL0s.RA_LIB.
Local Abbreviation P_EMPTY := OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YL0s.EMPTY.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  apply (ubsan_agrees_of_slots (ag_shape checksum_shape) [] Prog.LLVMFuzzerTestOneInput_c.disco_GI
    [] U.Prog.LLVMFuzzerTestOneInput_c.disco_GI).
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj.
    exact (Prog.DiscoEnd.slot_ok P_B P_API (ag_shape checksum_shape) P_SH P_SK
      P_RA P_EMPTY lib.SlotTopG.ms_segs_rsegs ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl eq_refl
      lib.FrameProof.errno_below_ceiling eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(split; vm_compute; reflexivity)
      lib.FrameProof.ctx_not_ro lib.FrameProof.frame_G_facts lib.FrameProof.frame_RELRO_facts (fun pl fs K => eq_refl)
      (fun n b => eq_refl) (ag_room_g checksum_shape) lib.FrameProof.zlib_frame_allocator rc fx j Hj).
  - intros data. apply ag_room_calls.
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj.
    exact (U.Prog.DiscoEndCg.slot_cg_ok U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API) (ag_shape checksum_shape)
      U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
      U.SlotTopG.ms_segs_rsegs ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl eq_refl
      U.FrameProof.errno_below_ceiling eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(split; vm_compute; reflexivity)
      U.FrameProof.ctx_not_ro U.FrameProof.frame_G_facts U.FrameProof.frame_RELRO_facts (fun pl fs K => eq_refl)
      (fun n b => eq_refl) (ag_room_cg checksum_shape) U.FrameProof.zlib_frame_allocator
      (fun rc' fx' => @U.AllocCf.zlib_malloc_contract_cf fx' rc') (fun rc' fx' => @U.AllocCf.zlib_free_contract_cf fx' rc')
      U.AgreeZlib.zlib_limit rc fx j Hj).
Qed.
