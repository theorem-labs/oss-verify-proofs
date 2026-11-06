From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib reac_ctrl_checksum_verify_c.
Import ListNotations.
Open Scope Z_scope.

Section Loop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (bs : list byte).
  Hypothesis Hp : 0 < p.
  Hypothesis Hp50 : p + 50 <= 2^64.
  Hypothesis Hlen : length bs = 32%nat.
  Hypothesis HB : bytes_at rsegs m (p + 18) bs.

  Definition Qv : machine_state -> Prop :=
    fun ms' => exists a1' a2' a3' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if blocksum bs =? 0 then 0 else -1))
                    a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom rsegs).

  Lemma loop : forall n i x3,
    (i + n = 32)%nat -> (0 < n)%nat ->
    evt rsegs Qv
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + 50)) (Z_to_bv 64 (psum bs i))
               (Z_to_bv 64 (p + 18 + Z.of_nat i)) x3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14180) fc None m (seg_rom rsegs)).
  Proof.
    induction n as [|n IH]; intros i x3 Hin Hn; [lia|].
    pose proof (rd_byte rsegs m (p + 18) bs i HB ltac:(lia)) as RD.
    pose proof (psum_range bs i) as PR.
    step. step. step. step.
    assert (R1 : 0 < p + 18 + Z.of_nat i + 1 <= 2^64) by lia.
    assert (R2 : 0 < p + 50 <= 2^64) by lia.
    rewrite (eqb_le64 (p + 18 + Z.of_nat i + 1) (p + 50) R1 R2).
    rewrite psum_S_zxb.
    destruct n as [|n].
    - replace (p + 18 + Z.of_nat i + 1 =? p + 50) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb].
      replace i with 31%nat in * by lia.
      step. step. step. step.
      pose proof (psum_range bs 32) as R32. change (Z.of_nat 32) with 32 in R32.
      rewrite (fin_a0 (psum bs 32)) by lia.
      apply evt_done. unfold Qv, blocksum. do 3 eexists. reflexivity.
    - replace (p + 18 + Z.of_nat i + 1 =? p + 50) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb].
      replace (p + 18 + Z.of_nat i + 1) with (p + 18 + Z.of_nat (S i)) by lia.
      apply (IH (S i)); lia.
  Qed.
End Loop.

Theorem reac_ctrl_checksum_verify_holds : reac_ctrl_checksum_verify_contract.
Proof.
  unfold reac_ctrl_checksum_verify_contract, REAC_CTRL_CHECKSUM_VERIFY.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p bs
    Hp Hp50 -> Hlen HB.
  step. step. step.
  change (Z_to_bv 64 0) with (Z_to_bv 64 (psum bs 0)).
  replace (p + 18) with (p + 18 + Z.of_nat 0) by lia.
  exact (loop ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p bs
           Hp Hp50 Hlen HB 32 0 a3 eq_refl ltac:(lia)).
Qed.
