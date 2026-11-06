(* ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Prog/LLVMFuzzerTestOneInput_halts.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_frame; ubsan_halts_of_llvm takes the SR contract of LLVMFuzzerTestOneInput (U/Prog/Statement.v slot_sr_all, the walk of the harness and its callees) as its one hypothesis, and the frame step is U/FrameProof.v frame_ubsan_holds; module path OSSVerify.Proofs.libdiginet.fuzz_frame.lib. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YK11 YM05 YO0d YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require FrameProof.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import Statement LLVMFuzzerTestOneInput_end.
From OSSVerify.libdiginet.fuzz_frame Require Statements.
Local Open Scope Z_scope.

Theorem ubsan_halts_of_llvm : slot_sr_all -> Statements.ubsan_halts.
Proof.
  intros SRA. apply ubsan_halts_of_slot; [|exact FrameProof.frame_ubsan_holds].
  intros rc fx LS B API SH SK FR. exact (llvm_contract B API FR SRA).
Qed.
