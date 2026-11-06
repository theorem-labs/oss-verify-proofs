From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.libreac.fuzz_boxreg Require Statements.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import SlotAgree AgreeShape AgreeFrame FrameSlotK.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require ZAllocator.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Statement LLVMFuzzerTestOneInput_gfr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Statement LLVMFuzzerTestOneInput_cfb
  LLVMFuzzerTestOneInput_cgt.
Local Open Scope Z_scope.

Module PS := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.Statement.
Module PG := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.LLVMFuzzerTestOneInput_gfr.
Module US := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog.Statement.
Module UB := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog.LLVMFuzzerTestOneInput_cfb.
Module UG := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog.LLVMFuzzerTestOneInput_cgt.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  refine (ubsan_agrees_of_slots (ag_shape kept_shape) _ _ _ _
    PS.llvm_G_inside (PS.llvm_GI_local _) (PS.llvm_GI_img _) _ _
    US.llvm_G_inside (US.llvm_GI_local _) (US.llvm_GI_img _) _).
  - apply PG.boxreg_slot_g_frame.
    + intros pl fs K. reflexivity.
    + intros b n H. exact (ag_room_g kept_shape b n H).
    + intros n b. reflexivity.
  - intros data. apply ag_room_calls.
  - apply UG.boxreg_slot_cg_frame.
    + intros pl fs K. reflexivity.
    + intros b n H. exact (ag_room_cg kept_shape b n H).
    + intros n b. reflexivity.
Qed.
