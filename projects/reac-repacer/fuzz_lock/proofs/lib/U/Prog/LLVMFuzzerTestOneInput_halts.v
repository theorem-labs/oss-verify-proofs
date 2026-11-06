(* reac-repacer/fuzz_lock: the UBSan build halts. The frame step for a return of 0 or -1 is proved
   (FrameRetOk.v frame_ret_ok over FrameRet.v frame_ret_hyp), the two harness functions meet their contracts
   (LLVMFuzzerTestOneInput_link.v checks_link) and LLVMFuzzerTestOneInput meets its slot contract
   (LLVMFuzzerTestOneInput_end.v llvm_contract). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import memcpy_c memchr_c bcmp_c strlen_c
number_c rp_lock_lookup_c cno_segs check_no_overread_c check_lookup_c
FrameRet FrameRetOk LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_end Statement LLVMFuzzerTestOneInput_link.
From OSSVerify.reac_repacer.fuzz_lock Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Section H.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof.
  apply ubsan_halts_of_slot; [| exact checks_link | exact frame_ret_ok].
  intros rc fx LS B API SH SK FR C1 C2. exact (llvm_contract B API FR C1 C2).
Qed.

End H.
