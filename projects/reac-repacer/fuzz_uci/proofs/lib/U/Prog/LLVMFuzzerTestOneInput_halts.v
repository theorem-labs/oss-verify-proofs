(* Modified by Theorem Labs: libreac/fuzz_decode's released lib/U/Prog/LLVMFuzzerTestOneInput_halts.v
   for reac-repacer/fuzz_uci, module paths changed: ubsan_halts from the frame (lib/U/FrameProof.v) and this image's
   harness-body contract (lib/U/Prog/LLVMFuzzerTestOneInput_end.v). *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YK11 YM05 YO0d YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require FrameProof.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require Import Statement LLVMFuzzerTestOneInput_end.
From OSSVerify.reac_repacer.fuzz_uci Require Statements.
Local Open Scope Z_scope.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof.
  apply ubsan_halts_of_slot; [|exact FrameProof.frame_ubsan_holds].
  intros rc fx LS B API SH SK FR. exact (llvm_contract B API FR).
Qed.
