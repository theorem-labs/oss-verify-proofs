(* reac-repacer/fuzz_lock: the two builds agree, from the agreement step for a return of 0 or -1
   (AgreeRet.v agree_ret_hyp, proved by AgreeRetOk.v agree_ret_ok) and the two slot contracts of
   LLVMFuzzerTestOneInput, the plain one (lib/Prog/LLVMFuzzerTestOneInput_gfr.v lock_slot_g_frame) and the
   crash-free UBSan one (lib/U/Prog/LLVMFuzzerTestOneInput_cgt.v lock_slot_cg_frame), in the form of
   libreac/fuzz_decode's released lib/Prog/LLVMFuzzerTestOneInput_agree.v (25e3d17bdb50). Both are taken for the
   same return function lock_ret, so the two builds return the same value on a payload and the driver writes the
   same row after each call. The crash-free contracts of the UBSan harness functions come from
   lib/U/Prog/LLVMFuzzerTestOneInput_cflink.v checks_cf_link. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.reac_repacer.fuzz_lock Require Statements.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YM05 YL0i YO09 YO0f.
Import ListNotations.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import AllocSlots AllocRoom SlotAgree AgreeShape
  AgreeFrame AgreeRet FrameSlotK.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require AgreeRetOk.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require ZAllocator.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Statement LLVMFuzzerTestOneInput_gfr strlen.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Statement LLVMFuzzerTestOneInput_cgt
  LLVMFuzzerTestOneInput_cflink check_no_overread_ccf check_lookup_ccf.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require YH02.
Local Open Scope Z_scope.

Module PS := OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog.Statement.
Module PG := OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog.LLVMFuzzerTestOneInput_gfr.
Module PL := OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog.strlen.
Module US := OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog.Statement.
Module UG := OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog.LLVMFuzzerTestOneInput_cgt.
Module UL := OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog.LLVMFuzzerTestOneInput_cflink.
Module UC := OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog.check_no_overread_ccf.
Module UK := OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog.check_lookup_ccf.
Module UH := OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable.YH02.
Module UZ := OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.ZAllocator.

(* the driver's shape for a fuzz target that returns lock_ret: FrameSlotK.v kept_shape with that leaf *)
Definition lock_shape : lib_shape := {|
  LIBK := fun pl fs K => K (LL (lock_ret pl) fs []);
  LIBK_ext := fun pl fs K K' H => H (LL (lock_ret pl) fs []);
  lib_delta := fun n b => b;
  lib_room := fun b n => sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 31 /\ sb_cap b = CAPMAX |}.

(* The crash-free contracts of the UBSan harness functions are lib/U/Prog/LLVMFuzzerTestOneInput_cflink.v
   checks_cf_link and the agreement step is AgreeRetOk.v agree_ret_ok; ubsan_agrees_holds closes both. *)
Theorem ubsan_agrees_of_checks :
  agree_ret_hyp ->
  (forall (rc : YM05.RunCeil) (fx : YK11.FPState),
     @UC.check_no_overread_contract_cf fx rc UH.src0_msyms (@UZ.zlib_API rc)) ->
  (forall (rc : YM05.RunCeil) (fx : YK11.FPState),
     @UK.check_lookup_contract_cf fx rc UH.src0_msyms (@UZ.zlib_API rc)) ->
  Statements.ubsan_agrees.
Proof.
  intros AG UCNO UCL.
  refine (AG lock_ret lock_ret_cases (ag_shape lock_shape) _ _ _ _
    PS.llvm_G_inside (PS.llvm_GI_local _) (PS.llvm_GI_img _) _ _
    US.llvm_G_inside (US.llvm_GI_local _) (US.llvm_GI_img _) _).
  - apply (PG.lock_slot_g_frame PL.strlen_holds).
    + intros pl fs K. reflexivity.
    + intros b n H. exact (ag_room_g lock_shape b n H).
    + intros n b. apply ag_delta.
  - intros data. apply ag_room_calls.
  - apply (UG.lock_slot_cg_frame UCNO UCL).
    + intros pl fs K. reflexivity.
    + intros b n H. exact (ag_room_cg lock_shape b n H).
    + intros n b. apply ag_delta.
Qed.

Theorem ubsan_agrees_of_step : agree_ret_hyp -> Statements.ubsan_agrees.
Proof.
  intros AG. exact (ubsan_agrees_of_checks AG (proj1 UL.checks_cf_link) (proj2 UL.checks_cf_link)).
Qed.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof. exact (ubsan_agrees_of_step AgreeRetOk.agree_ret_ok). Qed.
