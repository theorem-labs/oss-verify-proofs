From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import FrameBytes reac_frame_is_reac_c.
Import ListNotations.
Open Scope Z_scope.

Theorem reac_frame_is_reac_holds : reac_frame_is_reac_contract.
Proof.
  unfold reac_frame_is_reac_contract, REAC_FRAME_IS_REAC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs HB.
  step. step.
  if_cases HZ.
  - zify_cond HZ.
    assert (W : is_reac_result (bv_unsigned a0) (bv_unsigned a1) bs = 0).
    { unfold is_reac_result. rewrite (proj2 (Z.eqb_eq _ _) HZ). reflexivity. }
    step. step. apply evt_done. rewrite W. do 3 eexists. reflexivity.
  - zify_cond HZ.
    step. step. if_cases HL.
    + zify_cond HL.
      assert (W : is_reac_result (bv_unsigned a0) (bv_unsigned a1) bs = 0).
      { unfold is_reac_result. rewrite (proj2 (Z.eqb_neq _ _) HZ), (proj2 (Z.ltb_lt _ _) HL). reflexivity. }
      step. step. apply evt_done. rewrite W. do 3 eexists. reflexivity.
    + zify_cond HL. destruct (HB HZ HL) as [LEN BA].
      pose proof BA as (B0 & B1 & _).
      pose proof (rd1 m _ bs 12 BA ltac:(lia)) as R12. change (Z.of_nat 12) with 12 in R12.
      pose proof (rd1 m _ bs 13 BA ltac:(lia)) as R13. change (Z.of_nat 13) with 13 in R13.
      remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
      remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
      step. step. if_false.
      step. step. step. if_cases HC.
      * zify_cond HC. rewrite zxb_u in HC.
        assert (W : is_reac_result (bv_unsigned a0) (bv_unsigned a1) bs = 0).
        { unfold is_reac_result, is_reac_byte. rewrite <- E12.
          rewrite (proj2 (Z.eqb_neq _ _) HZ), (proj2 (Z.ltb_ge _ _) HL), (proj2 (Z.eqb_neq _ _) HC).
          reflexivity. }
        step. step. step. apply evt_done. rewrite W. do 3 eexists. reflexivity.
      * zify_cond HC. rewrite zxb_u in HC.
        step. step. if_false.
        do 6 step. apply evt_done.
        assert (A0 : v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b13) + -25)) 1
                     = Z_to_bv 64 (is_reac_result (bv_unsigned a0) (bv_unsigned a1) bs)).
        { unfold v_sltiu, is_reac_result, is_reac_byte, zxb. rewrite <- E12, <- E13, zxb_u.
          rewrite (proj2 (Z.eqb_neq _ _) HZ), (proj2 (Z.ltb_ge _ _) HL), HC.
          pose proof (byte_range b13) as X13.
          destruct (Z.eq_dec (bv_unsigned b13) 25) as [E|E].
          - rewrite E. vm_compute. reflexivity.
          - rewrite (proj2 (Z.eqb_neq _ _) E), andb_false_r.
            rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
            replace ((bv_unsigned b13 + -25) mod 2 ^ 64 <? 1) with false; [reflexivity|].
            symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia. }
        rewrite A0. do 3 eexists. reflexivity.
Qed.
