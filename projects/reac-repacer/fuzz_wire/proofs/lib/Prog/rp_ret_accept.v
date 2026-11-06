From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import FrameBytes rp_ret_accept_c.
Import ListNotations.
Open Scope Z_scope.

(* rp_ret_accept at 0x13504 (11 words); the tail `lbu a0, 13(a0); addi a0, a0, -25; seqz a0, a0` is the one of decode's
   reac_frame_is_reac and is closed as decode's walk closes it. *)

Lemma ret_seqz : forall (b13 : byte) (n : Z) (bs : list byte),
  14 <= n -> ret_byte bs 12 = 0x88 -> ret_byte bs 13 = bv_unsigned b13 ->
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b13) + -25)) 1 = Z_to_bv 64 (ret_accept_result n bs).
Proof.
  intros b13 n bs HL H12 H13.
  unfold v_sltiu, ret_accept_result, zxb. rewrite H12, H13, zxb_u, (proj2 (Z.ltb_ge _ _) HL).
  pose proof (byte_range b13) as X13.
  destruct (Z.eq_dec (bv_unsigned b13) 25) as [E|E].
  - rewrite E. vm_compute. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) E), andb_false_r.
    rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
    replace ((bv_unsigned b13 + -25) mod 2 ^ 64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Theorem rp_ret_accept_holds : rp_ret_accept_contract.
Proof.
  unfold rp_ret_accept_contract, RP_RET_ACCEPT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs HB.
  step. step. if_cases HL.
  - zify_cond HL.
    assert (W : ret_accept_result (bv_unsigned a1) bs = 0).
    { unfold ret_accept_result. rewrite (proj2 (Z.ltb_lt _ _) HL). reflexivity. }
    step. step. apply evt_done. rewrite W. do 2 eexists. reflexivity.
  - zify_cond HL. destruct (HB HL) as [LEN BA].
    pose proof (rd1 m _ bs 12 BA ltac:(lia)) as R12. change (Z.of_nat 12) with 12 in R12.
    pose proof (rd1 m _ bs 13 BA ltac:(lia)) as R13. change (Z.of_nat 13) with 13 in R13.
    remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
    remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
    step. step. step. if_cases HC.
    + zify_cond HC. rewrite zxb_u in HC.
      assert (W : ret_accept_result (bv_unsigned a1) bs = 0).
      { unfold ret_accept_result, ret_byte. rewrite <- E12.
        rewrite (proj2 (Z.ltb_ge _ _) HL), (proj2 (Z.eqb_neq _ _) HC). reflexivity. }
      step. step. apply evt_done. rewrite W. do 2 eexists. reflexivity.
    + zify_cond HC. rewrite zxb_u in HC.
      step. step. step. step. apply evt_done.
      rewrite (ret_seqz b13 (bv_unsigned a1) bs HL)
        by (unfold ret_byte; rewrite <- ?E12, <- ?E13; first [exact HC | reflexivity]).
      do 2 eexists. reflexivity.
Qed.
