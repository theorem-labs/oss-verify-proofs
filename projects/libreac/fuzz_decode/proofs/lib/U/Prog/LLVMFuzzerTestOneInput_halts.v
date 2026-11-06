From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YK11 YM05 YO0d YL0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require FrameProof.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import Statement LLVMFuzzerTestOneInput_end.
From OSSVerify.libreac.fuzz_decode Require Statements.
Local Open Scope Z_scope.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof.
  apply ubsan_halts_of_slot; [|exact FrameProof.frame_ubsan_holds].
  intros rc fx LS B API SH SK FR. exact (llvm_contract B API FR).
Qed.
