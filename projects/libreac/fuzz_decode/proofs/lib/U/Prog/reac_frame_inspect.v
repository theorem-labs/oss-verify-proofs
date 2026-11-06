From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import FrameBytes reac_frame_inspect_c.
Import ListNotations.
Open Scope Z_scope.

Theorem reac_frame_inspect_holds : reac_frame_inspect_contract.
Proof.
  unfold reac_frame_inspect_contract, REAC_FRAME_INSPECT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs HB.
  destruct (Z.eq_dec (bv_unsigned a1) 1492) as [EL|NL].
  - destruct (HB EL) as (LEN & BA & NZ).
    pose proof BA as (B0 & B1 & _). rewrite LEN in B1. change (Z.of_nat 1492) with 1492 in B1.
    pose proof (rd1 m _ bs 12 BA ltac:(lia)) as R12. change (Z.of_nat 12) with 12 in R12.
    pose proof (rd1 m _ bs 13 BA ltac:(lia)) as R13. change (Z.of_nat 13) with 13 in R13.
    pose proof (rd1 m _ bs 14 BA ltac:(lia)) as R14. change (Z.of_nat 14) with 14 in R14.
    pose proof (rd1 m _ bs 15 BA ltac:(lia)) as R15. change (Z.of_nat 15) with 15 in R15.
    pose proof (rd1 m _ bs 1490 BA ltac:(lia)) as R1490. change (Z.of_nat 1490) with 1490 in R1490.
    pose proof (rd1 m _ bs 1491 BA ltac:(lia)) as R1491. change (Z.of_nat 1491) with 1491 in R1491.
    remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
    remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
    remember (nth 14 bs (Z_to_bv 8 0)) as b14 eqn:E14.
    remember (nth 15 bs (Z_to_bv 8 0)) as b15 eqn:E15.
    remember (nth 1490 bs (Z_to_bv 8 0)) as b1490 eqn:E1490.
    remember (nth 1491 bs (Z_to_bv 8 0)) as b1491 eqn:E1491.
    step. step. if_false.
    step. if_false. step. step. if_false.
    step. step. step. if_cases HC.
    + zify_cond HC. rewrite zxb_u in HC.
      assert (W : inspect_result (bv_unsigned a1) bs = 0).
      { unfold inspect_result, inspect_wf, inspect_byte. rewrite EL, <- E12.
        rewrite (proj2 (Z.eqb_neq _ _) HC). reflexivity. }
      do 4 step. apply evt_done. rewrite W. do 2 eexists. reflexivity.
    + zify_cond HC. rewrite zxb_u in HC.
      step. step. if_false.
      step. step. step. if_cases HD.
      * zify_cond HD. rewrite zxb_u in HD.
        assert (W : inspect_result (bv_unsigned a1) bs = 0).
        { unfold inspect_result, inspect_wf, inspect_byte. rewrite EL, <- E12, <- E13.
          rewrite (proj2 (Z.eqb_eq _ _) HC), (proj2 (Z.eqb_neq _ _) HD). reflexivity. }
        do 4 step. apply evt_done. rewrite W. do 2 eexists. reflexivity.
      * zify_cond HD. rewrite zxb_u in HD.
        step. step. if_false.
        step. step. step. if_cases HE.
        -- zify_cond HE. rewrite zxb_u in HE.
           assert (W : inspect_result (bv_unsigned a1) bs = 0).
           { unfold inspect_result, inspect_wf, inspect_byte. rewrite EL, <- E12, <- E13, <- E1490.
             rewrite (proj2 (Z.eqb_eq _ _) HC), (proj2 (Z.eqb_eq _ _) HD), (proj2 (Z.eqb_neq _ _) HE).
             reflexivity. }
           do 4 step. apply evt_done. rewrite W. do 2 eexists. reflexivity.
        -- zify_cond HE. rewrite zxb_u in HE.
           step. step. if_false.
           step. step. step. if_cases HF.
           ++ zify_cond HF. rewrite zxb_u in HF.
              assert (W : inspect_result (bv_unsigned a1) bs = 0).
              { unfold inspect_result, inspect_wf, inspect_byte. rewrite EL, <- E12, <- E13, <- E1490, <- E1491.
                rewrite (proj2 (Z.eqb_eq _ _) HC), (proj2 (Z.eqb_eq _ _) HD), (proj2 (Z.eqb_eq _ _) HE),
                  (proj2 (Z.eqb_neq _ _) HF).
                reflexivity. }
              do 4 step. apply evt_done. rewrite W. do 2 eexists. reflexivity.
           ++ zify_cond HF. rewrite zxb_u in HF.
              step. step. if_false. step. step. if_false.
              do 9 step.
              apply evt_done.
              assert (V : inspect_result (bv_unsigned a1) bs = 2^32 + (bv_unsigned b14 + 256 * bv_unsigned b15)).
              { unfold inspect_result, inspect_wf, inspect_counter, inspect_byte.
                rewrite EL, <- E12, <- E13, <- E1490, <- E1491, <- E14, <- E15, HC, HD, HE, HF. reflexivity. }
              rewrite V. unfold zxb. rewrite !zxb_u.
              pose proof (byte_range b14) as X14. pose proof (byte_range b15) as X15.
              rewrite (unsigned_lit (Z.shiftl (bv_unsigned b15) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
              rewrite (Z.lor_comm (Z.shiftl (bv_unsigned b15) 8) (bv_unsigned b14)).
              rewrite lor_shiftl8_add by lia.
              rewrite (unsigned_lit (bv_unsigned b14 + 256 * bv_unsigned b15)) by lia.
              rewrite lor_pow32 by lia.
              replace (bv_unsigned b14 + 256 * bv_unsigned b15 + 4294967296)
                with (2^32 + (bv_unsigned b14 + 256 * bv_unsigned b15)) by lia.
              do 2 eexists. reflexivity.
  - step. step. if_true.
    assert (W : inspect_result (bv_unsigned a1) bs = 0).
    { unfold inspect_result, inspect_wf. rewrite (proj2 (Z.eqb_neq _ _) NL). reflexivity. }
    do 4 step. apply evt_done. rewrite W. do 2 eexists. reflexivity.
Qed.
