From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YM05 YO0d YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require FrameProof.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
snprintf LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput Statement LLVMFuzzerTestOneInput_end
LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_case1 LLVMFuzzerTestOneInput_case2 LLVMFuzzerTestOneInput_case3.
From OSSVerify.libreac.fuzz_boxreg Require Statements.
Local Open Scope Z_scope.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof.
  apply ubsan_halts_of_slot; [|exact FrameProof.frame_ubsan_holds].
  intros rc fx LS B API SH SK FR.
  apply (llvm_contract_of_cases B API FR). intros BI.
  pose proof FR as (HA & Hel & _).
  pose proof (fun fx' => proj1 (HA fx')) as HM.
  pose proof (fun fx' => proj1 (proj2 (HA fx'))) as HF.
  destruct (HA fx) as (_ & _ & _ & _ & _ & SLACK & _).
  intros op3 Hop.
  assert (E : op3 = 0 \/ op3 = 1 \/ op3 = 2 \/ op3 = 3) by lia.
  destruct E as [-> | [-> | [-> | ->]]].
  - apply llvm_case0_ok; first [exact HM | exact HF | exact Hel | exact SLACK | exact snprintf_holds].
  - apply llvm_case1_ok.
  - apply llvm_case2_ok.
  - apply llvm_case3_ok; first [exact HM | exact HF | exact Hel | exact SLACK | exact snprintf_holds].
Qed.
