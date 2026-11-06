(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_grant: the plain side is fuzz_grant's proved realization (built as its lib/Prog/AgreeGrant.v and lib/AgreeFrame.v build it, at grant_shape), the halting corollary takes srealizes, module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/AsanTop.v, with its module paths changed; 20 of its 44 lines of code are new or changed and 90 lines of the source are left out. *)
(* Modified by Theorem Labs: the twin of lib/U/FrameProof.v frame_ubsan_holds (no licence line) for a return value of the fuzz target of 0 or -1 *)
(* Donor: reac-repacer/fuzz_lock, proofs/reac-repacer/fuzz_lock/lib/U/FrameProof.v at 901d1549395.
   Module: OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog.FrameRetOk. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_repacer.fuzz_lock Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import FrameRet FrameRetD2 FrameRetD3 FrameRetD6.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require
  FrameRetA10 FrameRetA11 FrameRetA12 FrameRetA13 FrameRetA14 FrameRetA15 FrameRetA16 FrameRetA17 FrameRetA18 FrameRetA19.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YN03 YN2b YN33.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import
  ZTraceSpec ZComplete ZAllocator SlotTopG Contract FrameAPI FrameSlotG FrameProof Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.

(* the ten -1 arms *)
Lemma arms_m1_proved : arms_m1.
Proof.
  exact (conj FrameRetA10.src0_runX_0E1_m1_ok (conj FrameRetA11.src0_runX_0M1_m1_ok
    (conj FrameRetA12.src0_runX_1E1_m1_ok (conj FrameRetA13.src0_runX_1E2_m1_ok
    (conj FrameRetA14.src0_runX_1E3_m1_ok (conj FrameRetA15.src0_runX_1E4_m1_ok
    (conj FrameRetA16.src0_runX_1M1_m1_ok (conj FrameRetA17.src0_runX_1M2_m1_ok
    (conj FrameRetA18.src0_runX_1M3_m1_ok FrameRetA19.src0_runX_1M4_m1_ok))))))))).
Qed.

Theorem frame_ret_ok : frame_ret_hyp.
Proof.
  intros ret HR01.
  exists src0_msyms, (@zlib_API), (ret_shape ret), src0_sink_head, src0_sink, RA_LIB, EMPTY.
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
  split; [exact zlib_frame_allocator|].
  intros G GI HG HL HI HC.
  exact (plain_halts_of_frame_slot_r ret G GI HR01 arms_m1_proved HG HL HI HC).
Qed.
