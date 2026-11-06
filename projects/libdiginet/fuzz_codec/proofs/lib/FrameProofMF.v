(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_grant: the plain side is fuzz_grant's proved realization (built as its lib/Prog/AgreeGrant.v and lib/AgreeFrame.v build it, at grant_shape), the halting corollary takes srealizes, module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/AsanTop.v, with its module paths and module names changed; 12 of its 37 lines of code are new or changed and 89 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libdiginet.fuzz_codec Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YN03 YN2b YN33.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import
  FrameSlotGMF FrameProof
  ZTraceSpec ZComplete ZAllocator SlotTopG Contract FrameAPI AllocCut BlocksNodup FrameSlotG Img0 ReallocCert.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable.R Require Import Cfg.
Import ListNotations.
Open Scope Z_scope.
Lemma zlib_frame_allocator_mf : forall (rc : RunCeil) (fx : FPState), @frame_allocator_mf rc fx src0_msyms (@zlib_API rc).
Proof.
  intros rc fx. destruct (zlib_frame_allocator rc fx) as (_ & _ & _ & _ & _ & H). exact H.
Qed.
Theorem frame_plain_mf_holds : frame_plain_mf.
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
