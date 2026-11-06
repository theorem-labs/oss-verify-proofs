From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_knock Require Statements.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YN03 YN2b YN33.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require Import
  FrameSlotGMF FrameProof
  ZTraceSpec ZComplete ZAllocator SlotTopG Contract FrameAPI AllocCut BlocksNodup FrameSlotG Img0 ReallocCert.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Reusable.R Require Import Cfg.
Import ListNotations.
Open Scope Z_scope.
Lemma zlib_frame_allocator_mf : forall (rc : RunCeil) (fx : FPState), @frame_allocator_mf rc fx src0_msyms (@zlib_API rc).
Proof.
  intros rc fx. destruct (zlib_frame_allocator rc fx) as (_ & _ & _ & _ & _ & H). exact H.
Qed.
Theorem frame_ubsan_mf_holds : frame_ubsan_mf.
Proof.
  exists src0_msyms, (@zlib_API), checksum_shape, src0_sink_head, src0_sink, RA_LIB, EMPTY.
  split; [exact ms_segs_rsegs|].
  split; [vm_compute; reflexivity|].
  do 4 (split; [reflexivity|]).
  split; [exact errno_below_ceiling|].
  do 14 (split; [reflexivity|]).
  do 3 (split; [reflexivity|]).
  split; [reflexivity|].
  split; [split; vm_compute; reflexivity|].
  split; [exact ctx_not_ro|].
  split; [exact frame_G_facts|].
  split; [exact frame_RELRO_facts|].
  split; [intros pl fs K; reflexivity|].
  split; [intros n b; reflexivity|].
  split; [intros b n H; exact H|].
  split; [exact zlib_frame_allocator_mf|].
  exact plain_halts_mf_of_frame_slot.
Qed.
