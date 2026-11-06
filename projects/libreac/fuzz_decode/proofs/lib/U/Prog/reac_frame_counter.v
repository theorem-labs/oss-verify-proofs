From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import FrameBytes reac_frame_counter_c.
Import ListNotations.
Open Scope Z_scope.

Theorem reac_frame_counter_holds : reac_frame_counter_contract.
Proof.
  unfold reac_frame_counter_contract, REAC_FRAME_COUNTER.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs NZ LEN BA.
  pose proof BA as (B0 & B1 & _).
  pose proof (rd1 m _ bs 14 BA ltac:(lia)) as R14. change (Z.of_nat 14) with 14 in R14.
  pose proof (rd1 m _ bs 15 BA ltac:(lia)) as R15. change (Z.of_nat 15) with 15 in R15.
  remember (nth 14 bs (Z_to_bv 8 0)) as b14 eqn:E14.
  remember (nth 15 bs (Z_to_bv 8 0)) as b15 eqn:E15.
  step. if_false. step. step. if_false. step. if_false.
  do 7 step.
  apply evt_done.
  pose proof (byte_range b14) as X14. pose proof (byte_range b15) as X15.
  unfold zxb. rewrite !zxb_u, lor_bytes16.
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned b14 + 256 * bv_unsigned b15) 48))
    by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (Z.shiftl_mul_pow2 (bv_unsigned b14 + 256 * bv_unsigned b15) 48) by lia.
  rewrite (Z.shiftr_div_pow2 ((bv_unsigned b14 + 256 * bv_unsigned b15) * 2 ^ 48) 48) by lia.
  rewrite Z.div_mul by lia.
  replace (bv_unsigned b14 + 256 * bv_unsigned b15) with (counter_result bs)
    by (unfold counter_result, counter_byte; rewrite <- E14, <- E15; reflexivity).
  eexists. reflexivity.
Qed.
