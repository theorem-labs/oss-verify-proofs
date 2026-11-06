(* fuzz_lock's plain halting statement, in the form of libreac/fuzz_decode's lib/Prog/LLVMFuzzerTestOneInput_halts.v
   (release 25e3d17bdb50). It closes with no premise: the libc strlen contract is strlen.v's strlen_holds (the walk
   of libreac/fuzz_disco's strlen, by path), and the frame step for a return of 0 or -1 (FrameRet.v frame_ret_hyp)
   is FrameRetOk.v's frame_ret_ok. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YM05 YO0d YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import strlen_c FrameRet Statement
  LLVMFuzzerTestOneInput_end.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require strlen FrameRetOk.
From OSSVerify.reac_repacer.fuzz_lock Require Statements.
Local Open Scope Z_scope.

Theorem plain_halts_holds : Statements.plain_halts.
Proof.
  apply plain_halts_of_slot; [|exact FrameRetOk.frame_ret_ok].
  intros rc fx LS B API SH SK FR. exact (llvm_contract B API FR strlen.strlen_holds).
Qed.
