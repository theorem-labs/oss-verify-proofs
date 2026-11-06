(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/U/Prog/LLVMFuzzerTestOneInput_halts.v (6874bc78b1f, itself
   libreac/fuzz_decode's released file) at fuzz_wire's module paths: ubsan_halts from the frame (lib/U/FrameProof.v)
   and this image's harness-body contract (lib/U/Prog/LLVMFuzzerTestOneInput_end.v). *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YK11 YM05 YO0d YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require FrameProof.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import Statement LLVMFuzzerTestOneInput_end.
From OSSVerify.reac_repacer.fuzz_wire Require Statements.
Local Open Scope Z_scope.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof.
  apply ubsan_halts_of_slot; [|exact FrameProof.frame_ubsan_holds].
  intros rc fx LS B API SH SK FR. exact (llvm_contract B API FR).
Qed.
