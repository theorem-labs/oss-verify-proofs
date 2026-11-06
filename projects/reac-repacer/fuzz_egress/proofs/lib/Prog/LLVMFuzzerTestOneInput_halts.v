(* Modified by Theorem Labs: ported from reac-repacer/fuzz_uci proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_halts.v at bc49657c087a; module path only. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Reusable Require Import YK11 YM05 YO0d YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require FrameProof.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import Statement LLVMFuzzerTestOneInput_end.
From OSSVerify.reac_repacer.fuzz_egress Require Statements.
Local Open Scope Z_scope.

Theorem plain_halts_holds : Statements.plain_halts.
Proof.
  apply plain_halts_of_slot; [|exact FrameProof.frame_plain_holds].
  intros rc fx LS B API SH SK FR. exact (llvm_contract B API FR).
Qed.
