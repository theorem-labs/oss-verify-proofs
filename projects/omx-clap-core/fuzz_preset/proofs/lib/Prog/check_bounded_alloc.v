From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_bounded_alloc_c.
Open Scope Z_scope.

Theorem check_bounded_alloc_holds : check_bounded_alloc_contract.
Proof.
  unfold check_bounded_alloc_contract, CHECK_BOUNDED_ALLOC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m held size
    E0 E1 HH HS HB.
  subst a0 a1.
  step. step. step. step.
  rewrite (unsigned_lit size) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  if_cases HC.
  - zify_cond HC. rewrite ?unsigned_lit_wrap in HC.
    exfalso. lia.
  - step.
    apply evt_done. do 14 eexists. reflexivity.
Qed.
