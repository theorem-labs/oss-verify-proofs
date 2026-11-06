From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import check_bounded_alloc_c.
Open Scope Z_scope.

Lemma bound_unsigned : forall x : word,
  bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned x) 2))) 1
                           + Z.shiftr (bv_unsigned x) 2 + 3))
  = bv_unsigned x / 4 * 3 + 3.
Proof.
  intros x.
  assert (R : 0 <= bv_unsigned x < 2^64)
    by (pose proof (bv_unsigned_in_range 64 x) as H; unfold bv_modulus in H; exact H).
  rewrite Z.shiftr_div_pow2 by lia.
  change (2^2) with 4.
  assert (Q : 0 <= bv_unsigned x / 4 < 2^62) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (unsigned_lit (bv_unsigned x / 4)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  change (2^1) with 2.
  rewrite unsigned_lit by lia.
  lia.
Qed.

Theorem check_bounded_alloc_holds : check_bounded_alloc_contract.
Proof.
  unfold check_bounded_alloc_contract, CHECK_BOUNDED_ALLOC, b64_alloc_bound.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HB.
  step. step. step. step. step.
  if_cases HC.
  - exfalso. unfold bv_ltu in HC. apply Z.ltb_lt in HC. rewrite bound_unsigned in HC. lia.
  - step. apply evt_done. do 2 eexists. reflexivity.
Qed.
