From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcLib RcLeaf RcLeafLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import reac_ctrl_headamp_record_verify_c.
Import ListNotations.
Open Scope Z_scope.

Section Loop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (rec : list byte).
  Hypothesis Hp : 0 < p.
  Hypothesis Hp40 : p + 40 <= 2^64.
  Hypothesis Hlen : length rec = 6%nat.
  Hypothesis HR : bytes_at rsegs m (p + 34) rec.

  Definition Qh : machine_state -> Prop :=
    fun ms' => exists a1' a2' a3' a4' a5' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if rsum rec =? 0 then 0 else -1))
                    a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom rsegs).

  Lemma hloop : forall n i x5,
    (i + n = 6)%nat -> (0 < n)%nat ->
    evt rsegs Qh
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + 34)) (Z_to_bv 64 (psum rec i))
               (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (18446744073709551615 - (p + 34))) (Z_to_bv 64 6) x5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1445c) fc None m (seg_rom rsegs)).
  Proof.
    induction n as [|n IH]; intros i x5 Hin Hn; [lia|].
    pose proof (rd_byte rsegs m (p + 34) rec i HR ltac:(lia)) as RD.
    pose proof (psum_range rec i) as PR.
    step. rc_false.
    step.
    step. step. step. step.
    rewrite psum_S_zxb.
    rewrite (eqb_le64 (Z.of_nat i + 1) 6) by lia.
    destruct n as [|n].
    - replace (Z.of_nat i + 1 =? 6) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb].
      replace i with 5%nat in * by lia.
      step. step. step. step. step.
      pose proof (psum_range rec 6) as R6. change (Z.of_nat 6) with 6 in R6.
      rewrite (rcl_fin127 (psum rec 6)) by lia.
      apply evt_done. unfold Qh, rsum. do 5 eexists. reflexivity.
    - replace (Z.of_nat i + 1 =? 6) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb].
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      apply (IH (S i)); lia.
  Qed.
End Loop.

Theorem reac_ctrl_headamp_record_verify_holds : reac_ctrl_headamp_record_verify_contract.
Proof.
  unfold reac_ctrl_headamp_record_verify_contract, REAC_CTRL_HEADAMP_RECORD_VERIFY.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p b0 b1 rec -> Hp Hp40 HB Hlen HR.
  pose proof (rcl_rd rsegs m (p + 18) [b0; b1] 0 b0 HB eq_refl) as R0.
  pose proof (rcl_rd rsegs m (p + 18) [b0; b1] 1 b1 HB eq_refl) as R1.
  change (Z.of_nat 0) with 0 in R0. change (Z.of_nat 1) with 1 in R1.
  replace (p + 18 + 0) with (p + 18) in R0 by lia. replace (p + 18 + 1) with (p + 19) in R1 by lia.
  step. rc_false.
  step. step. rc_false.
  step. step. step. step. step.
  rewrite (rcl_zxb_eqb b0 4) by lia.
  destruct (Z.eqb_spec (bv_unsigned b0) 4) as [E0|E0]; cbn [negb].
  - step. step. rc_false.
    step. step. step.
    rewrite (rcl_zxb_eqb b1 3) by lia.
    destruct (Z.eqb_spec (bv_unsigned b1) 3) as [E1|E1]; cbn [negb].
    + step. step. rc_false.
      step. step. step. step. step.
      rewrite (unsigned_lit (p + 34)) by lia. rewrite (zb_lxor_ones (p + 34)) by lia.
      replace (hv b0 b1 rec) with (rsum rec =? 0) by (unfold hv; rewrite E0, E1; reflexivity).
      exact (hloop ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p rec
               Hp Hp40 Hlen HR 6 0 _ eq_refl ltac:(lia)).
    + step. step.
      replace (hv b0 b1 rec) with false by (unfold hv; rewrite E0; apply Z.eqb_neq in E1; rewrite E1;
        rewrite Bool.andb_false_r; reflexivity).
      apply evt_done. do 5 eexists. reflexivity.
  - step. step.
    replace (hv b0 b1 rec) with false by (unfold hv; apply Z.eqb_neq in E0; rewrite E0; reflexivity).
    apply evt_done. do 5 eexists. reflexivity.
Qed.
