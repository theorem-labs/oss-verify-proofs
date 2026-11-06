From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import record_sum_closes_c.
Import ListNotations.
Open Scope Z_scope.

Section Loop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte).
  Hypothesis Hq : bv_unsigned a0 <> 0.
  Hypothesis Hqn : bv_unsigned a0 + Z.of_nat (length bs) <= 2^64.
  Hypothesis HB : bytes_at rsegs m (bv_unsigned a0) bs.

  Definition Qr : machine_state -> Prop :=
    fun ms' => exists a1' a2' a3' a4' a5' a6' : word,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if recsum bs =? 0 then 1 else 0))
                    a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom rsegs).

  Lemma loop : forall k i x1 x4 x5 x6,
    (i + k = length bs)%nat -> (0 < k)%nat ->
    bv_unsigned x1 = Z.of_nat k ->
    bv_unsigned x4 = bv_unsigned a0 + Z.of_nat i ->
    bv_unsigned x5 = bv_unsigned a0 + Z.of_nat i ->
    evt rsegs Qr
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x1 (Z_to_bv 64 (psum bs i)) (v_sltu (Z_to_bv 64 0) a0) x4 x5 x6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x143bc) fc None m (seg_rom rsegs)).
  Proof.
    induction k as [|k IH]; intros i x1 x4 x5 x6 Hik Hk H1 H4 H5; [lia|].
    pose proof (rd_byte rsegs m (bv_unsigned a0) bs i HB ltac:(lia)) as RD.
    rewrite <- H5 in RD. rewrite (wa_of_var x5 (bv_unsigned x5) eq_refl) in RD.
    pose proof (zr_word a0) as Ra. unfold inr64 in Ra.
    step.
    rewrite (rc_ltu_ge a0 x4) by lia.
    step. step. step.
    rewrite (rc_ubchk a0 x4) by lia.
    step.
    rewrite (rc_neq0w a0) by exact Hq.
    step. step. step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb0 (bv_unsigned x1 + -1)) by lia.
    destruct k as [|k].
    - replace (bv_unsigned x1 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb].
      step. step. step.
      rewrite rc_fin1.
      apply evt_done. unfold Qr, recsum. replace (length bs) with (S i) by lia.
      do 6 eexists. reflexivity.
    - replace (bv_unsigned x1 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb].
      apply (IH (S i)); first [lia | rewrite unsigned_lit by lia; lia].
  Qed.
End Loop.

Theorem record_sum_closes_holds : record_sum_closes_contract.
Proof.
  unfold record_sum_closes_contract, RECORD_SUM_CLOSES.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    Hlen Hpre.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  destruct (Z.eq_dec (bv_unsigned a1) 0) as [H0 | Hn].
  - assert (E : bs = []) by (destruct bs; [reflexivity | cbn in Hlen; lia]). subst bs.
    step.
    rewrite (rc_eq0w a1) by exact H0.
    step. step.
    apply evt_done. do 6 eexists. reflexivity.
  - destruct Hpre as [H0 | (Hq & Hqn & HB)]; [contradiction|].
    step.
    rewrite (rc_neq0w a1) by exact Hn.
    step. step. step. step.
    exact (loop ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
             Hq ltac:(lia) HB (length bs) 0 a1 a0 a0 a6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
