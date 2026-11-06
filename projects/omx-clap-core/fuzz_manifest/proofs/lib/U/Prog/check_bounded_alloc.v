From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import check_bounded_alloc_c.
Open Scope Z_scope.

Theorem check_bounded_alloc_holds : check_bounded_alloc_contract.
Proof.
  unfold check_bounded_alloc_contract, CHECK_BOUNDED_ALLOC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m H1 H2.
  step. step.
  if_cases HC.
  - exfalso. unfold bv_ltu in HC. apply Z.ltb_lt in HC.
    rewrite unsigned_lit in HC by (pose proof (bv_unsigned_in_range 64 a1) as R; unfold bv_modulus in R; lia). lia.
  - step. apply evt_done. do 15 eexists. reflexivity.
Qed.
