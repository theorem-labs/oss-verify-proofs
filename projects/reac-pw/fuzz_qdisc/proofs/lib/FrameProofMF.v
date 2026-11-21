(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_grant: the plain side is fuzz_grant's proved realization (built as its lib/Prog/AgreeGrant.v and lib/AgreeFrame.v build it, at grant_shape), the halting corollary takes srealizes, module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/AsanTop.v, with its module paths and module names changed; 12 of its 37 lines of code are new or changed and 89 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the allocation mode the allocator record carries (a refused munmap leaves a leaked map)). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_qdisc Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YN03 YN2b YN33.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib Require Import
  FrameSlotGMF FrameProof
  ZTraceSpec ZComplete ZAllocator ZAllocatorMF SlotTopG Contract FrameAPI AllocCut BlocksNodup FrameSlotG Img0 ReallocCert.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable.R Require Import Cfg.
Import ListNotations.
Open Scope Z_scope.
(* 08b1429: the may-fail frame is over the record at MayFail (ZAllocatorMF.zlib_API_mf); its structural facts read
   only the record's invariant and laws (AllocCut's _m facts). *)
Lemma zlib_frame_allocator_mf : forall (rc : RunCeil) (fx : FPState), @frame_allocator_mf rc fx src0_msyms (@zlib_API_mf rc).
Proof.
  intros rc fx.
  pose proof (@zlib_allocator_extra_mf rc) as AX.
  assert (HX : forall L A mem md, aa_MR (@zlib_API_mf rc) L A mem md -> MRx (AM:=MayFail) src0_msyms L A mem md)
    by (intros L A mem md H; exact H).
  split; [exact (block_slack_present_ok_m src0_msyms (@zlib_API_mf rc) HX)|].
  split; [exact (ctx_owned_ok_m src0_msyms (@zlib_API_mf rc) HX)|].
  split; [exact (blocks_low_ok_m src0_msyms (@zlib_API_mf rc))|].
  split; [exact (blocks_nodup_ok src0_msyms (@zlib_API_mf rc) HX)|].
  split; [exact (blocks_writable_ok_m src0_msyms (@zlib_API_mf rc))|].
  split; [exact (errno_unowned_ok_m src0_msyms (@zlib_API_mf rc) AX src0_errno_check)|].
  split; [exact (guard_rw_ok_m src0_msyms (@zlib_API_mf rc) ltac:(vm_compute; reflexivity))|].
  split; [exact (libc_no_locks_ok_m src0_msyms (@zlib_API_mf rc) AX)|].
  split; [exact AX|].
  split.
  - intros L A mem md a HM Ha. destruct (frame_G_facts a Ha) as (Himg & Hst & Hctx & _).
    intros [Ho|Ho]; [exact (Hctx (ax_img AX L A mem md a HM Himg Ho)) | exact (Hst Ho)].
  - intros L A mem md a HM Ha. destruct (frame_RELRO_facts a Ha) as (Himg & Hst & Hctx & _).
    intros [Ho|Ho]; [exact (Hctx (ax_img AX L A mem md a HM Himg Ho)) | exact (Hst Ho)].
Qed.
Theorem frame_plain_mf_holds : frame_plain_mf.
Proof.
  exists src0_msyms, (@zlib_API_mf), checksum_shape, src0_sink_head, src0_sink, RA_LIB, EMPTY.
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
