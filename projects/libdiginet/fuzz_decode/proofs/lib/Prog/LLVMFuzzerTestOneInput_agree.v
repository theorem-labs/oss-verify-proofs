(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: Statements.ubsan_agrees, as libreac/fuzz_decode's released
   lib/Prog/LLVMFuzzerTestOneInput_agree.v: the kit's ubsan_agrees_of_slots (lib/AgreeFrame.v) at ag_shape kept_shape,
   given the plain image's slot contract (lib/Prog/LLVMFuzzerTestOneInput_gfr.v: decode_slot_g_frame) and the UBSan
   image's cut-free one (lib/U/Prog/LLVMFuzzerTestOneInput_cgt.v: decode_slot_cg_frame). fuzz_decode returns 0 on
   every path (fuzz/fuzz_decode.c:290, :343), so the kit's 0-only agree frame applies as it is. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.libdiginet.fuzz_decode Require Statements.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YK11 YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import SlotAgree AgreeShape AgreeFrame FrameSlotK.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require ZAllocator.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Statement LLVMFuzzerTestOneInput_gfr.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Statement LLVMFuzzerTestOneInput_cgt.
Local Open Scope Z_scope.

Module PS := OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog.Statement.
Module PG := OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog.LLVMFuzzerTestOneInput_gfr.
Module US := OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog.Statement.
Module UG := OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog.LLVMFuzzerTestOneInput_cgt.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  refine (ubsan_agrees_of_slots (ag_shape kept_shape) _ _ _ _
    PS.llvm_G_inside (PS.llvm_GI_local _) (PS.llvm_GI_img _) _ _
    US.llvm_G_inside (US.llvm_GI_local _) (US.llvm_GI_img _) _).
  - apply PG.decode_slot_g_frame.
    + intros pl fs K. reflexivity.
    + intros b n H. exact (ag_room_g kept_shape b n H).
    + intros n b. reflexivity.
  - intros data. apply ag_room_calls.
  - apply UG.decode_slot_cg_frame.
    + intros pl fs K. reflexivity.
    + intros b n H. exact (ag_room_cg kept_shape b n H).
    + intros n b. reflexivity.
Qed.
