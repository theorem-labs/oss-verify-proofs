(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_agree.v
   at bc49657c087aa7d6ab0af1ffb2cb67fa08b15de1; module path and this unit's two slot contracts (egress_slot_g_frame,
   egress_slot_cg_frame). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/LLVMFuzzerTestOneInput_agree.v, with its module paths changed; 8 of its 31 lines of code are new or changed and 7 lines of the source are left out. *)
(* ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_agree.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_frame; the agreement step is decode's (AgreeFrame.v ubsan_agrees_of_slots with the shape ag_shape kept_shape, whose leaf is LL 0: LLVMFuzzerTestOneInput returns 0 in both builds); ubsan_agrees_of_llvm takes the plain SR contract of LLVMFuzzerTestOneInput (Prog/Statement.v slot_sr_all, through LLVMFuzzerTestOneInput_gfr.v frame_slot_g_frame) and the crash-free UBSan one (U/Prog/Statement.v slot_sr_cf_all, through U/Prog/LLVMFuzzerTestOneInput_cgt.v frame_slot_cg_frame) as its two hypotheses; module path OSSVerify.Proofs.libdiginet.fuzz_frame.lib. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.libdiginet.fuzz_frame Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YK11 YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import SlotAgree AgreeShape AgreeFrame FrameSlotK.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require ZAllocator.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Statement LLVMFuzzerTestOneInput_gfr.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Statement LLVMFuzzerTestOneInput_cfb
  LLVMFuzzerTestOneInput_cgt.
Local Open Scope Z_scope.

Module PS := OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog.Statement.
Module PG := OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog.LLVMFuzzerTestOneInput_gfr.
Module US := OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog.Statement.
Module UB := OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog.LLVMFuzzerTestOneInput_cfb.
Module UG := OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog.LLVMFuzzerTestOneInput_cgt.

Theorem ubsan_agrees_of_llvm : PS.slot_sr_all -> US.slot_sr_cf_all -> Statements.ubsan_agrees.
Proof.
  intros SRA SRCF.
  refine (ubsan_agrees_of_slots (ag_shape kept_shape) _ _ _ _
    PS.llvm_G_inside (PS.llvm_GI_local _) (PS.llvm_GI_img _) _ _
    US.llvm_G_inside (US.llvm_GI_local _) (US.llvm_GI_img _) _).
  - apply (PG.frame_slot_g_frame SRA).
    + intros pl fs K. reflexivity.
    + intros b n H. exact (ag_room_g kept_shape b n H).
    + intros n b. reflexivity.
  - intros data. apply ag_room_calls.
  - apply (UG.frame_slot_cg_frame SRCF).
    + intros pl fs K. reflexivity.
    + intros b n H. exact (ag_room_cg kept_shape b n H).
    + intros n b. reflexivity.
Qed.
