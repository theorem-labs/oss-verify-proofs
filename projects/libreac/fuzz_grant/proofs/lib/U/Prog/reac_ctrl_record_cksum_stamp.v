From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel RcLib RcRec RcRecLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import reac_ctrl_record_cksum_stamp_c.
Import ListNotations.
Open Scope Z_scope.

Section Stamp.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte).
  Hypothesis Hq : bv_unsigned a0 <> 0.
  Hypothesis Hqn : bv_unsigned a0 + bv_unsigned a1 <= 2^64.
  Hypothesis Hlen : Z.of_nat (length bs) = bv_unsigned a1 - 1.
  Hypothesis HB : bytes_at rsegs m (bv_unsigned a0) bs.
  Hypothesis HW : wr_at rsegs m (bv_unsigned a0 + bv_unsigned a1 - 1) 1.

  Definition Qs : machine_state -> Prop :=
    fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ bytes_at rsegs m' (bv_unsigned a0 + bv_unsigned a1 - 1) [Z_to_bv 8 (stampck bs)]
      /\ bytes_at rsegs m' (bv_unsigned a0) bs
      /\ recsum (bs ++ [Z_to_bv 8 (stampck bs)]) = 0
      /\ munch [(bv_unsigned a0 + bv_unsigned a1 - 1, bv_unsigned a0 + bv_unsigned a1)] m m'
      /\ wmono rsegs m m'
      /\ (mem_inv rsegs m -> mem_inv rsegs m').

  Lemma tail : forall x2 y3 y4 y5 y6 y7,
    bv_unsigned x2 = bv_unsigned a1 - 1 ->
    evt rsegs Qs
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (psum bs (length bs))) x2 y3 y4 y5 y6 y7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13f80) fc None m (seg_rom rsegs)).
  Proof.
    intros x2 y3 y4 y5 y6 y7 H2.
    pose proof (zr_word a0) as Ra. unfold inr64 in Ra.
    pose proof (wr_at_store_ok rsegs m _ 1 0 1 HW ltac:(lia) ltac:(lia)) as HS0.
    rewrite Z.add_0_r in HS0.
    pose proof HS0 as HS.
    replace (bv_unsigned a0 + bv_unsigned a1 - 1) with (bv_unsigned x2 + bv_unsigned a0) in HS by lia.
    step. step.
    rewrite (rc_ltu_ge a0 (Z_to_bv 64 (bv_unsigned x2 + bv_unsigned a0))) by (rewrite unsigned_lit by lia; lia).
    step. step. step. step.
    rewrite (rc_ubchk a0 (Z_to_bv 64 (bv_unsigned x2 + bv_unsigned a0))) by (try rewrite unsigned_lit by lia; lia).
    step.
    rewrite (rc_neq0w a0) by exact Hq.
    step. step. step. step.
    rewrite rc_le1_stamp. change ((- psum bs (length bs)) mod 128) with (stampck bs).
    replace (Z_to_bv 64 (bv_unsigned x2 + bv_unsigned a0)) with (wa (bv_unsigned a0 + bv_unsigned a1 - 1))
      by (unfold wa; f_equal; lia).
    apply evt_done. unfold Qs.
    do 8 eexists. exists (write_to_mem m (wa (bv_unsigned a0 + bv_unsigned a1 - 1)) [Z_to_bv 8 (stampck bs)]).
    split; [reflexivity|].
    split; [apply bytes_at_write_same; cbn [length]; lia|].
    split; [apply bytes_at_write_other; [exact HB | lia | cbn [length]; lia | left; lia]|].
    split; [apply rc_recsum_stamp|].
    split; [apply munch_write; [apply munch_refl | lia | cbn [length]; lia | cbn [inside]; left; cbn [length]; lia]|].
    split; [apply wmono_write; apply wmono_refl|].
    intros HI. apply mem_inv_store; [exact HI | exact HS0].
  Qed.

  Lemma loop : forall k i x2 x4 x5 x6 x7,
    (i + k = length bs)%nat -> (0 < k)%nat ->
    bv_unsigned x2 = bv_unsigned a1 - 1 ->
    bv_unsigned x6 = Z.of_nat k ->
    bv_unsigned x4 = bv_unsigned a0 + Z.of_nat i ->
    bv_unsigned x5 = bv_unsigned a0 + Z.of_nat i ->
    evt rsegs Qs
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (psum bs i)) x2 (v_sltu (Z_to_bv 64 0) a0) x4 x5 x6 x7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13f4c) fc None m (seg_rom rsegs)).
  Proof.
    induction k as [|k IH]; intros i x2 x4 x5 x6 x7 Hik Hk H2 H6 H4 H5; [lia|].
    pose proof (rd_byte rsegs m (bv_unsigned a0) bs i HB ltac:(lia)) as RD.
    rewrite <- H5 in RD. rewrite (wa_of_var x5 (bv_unsigned x5) eq_refl) in RD.
    pose proof (zr_word a0) as Ra. unfold inr64 in Ra.
    step.
    rewrite (rc_ltu_ge a0 x4) by lia.
    step. step. step.
    rewrite (rc_ubchk a0 x4) by lia.
    step.
    rewrite (rc_neq0w a0) by exact Hq.
    step. step. step. step.
    rewrite psum_S_zxb.
    step. step.
    rewrite (rc_eqb0 (bv_unsigned x6 + -1)) by lia.
    destruct k as [|k].
    - replace (bv_unsigned x6 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      cbv iota. assert (E : S i = length bs) by lia. rewrite E.
      apply tail. exact H2.
    - replace (bv_unsigned x6 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbv iota. step.
      apply (IH (S i)); first [lia | rewrite unsigned_lit by lia; lia].
  Qed.
End Stamp.

Theorem reac_ctrl_record_cksum_stamp_holds : reac_ctrl_record_cksum_stamp_contract.
Proof.
  unfold reac_ctrl_record_cksum_stamp_contract, REAC_CTRL_RECORD_CKSUM_STAMP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    Hn Hq Hqn Hlen HB HW.
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  assert (Hlen' : Z.of_nat (length bs) = bv_unsigned a1 - 1) by lia.
  step. step. step.
  unfold bv_ltu. change (bv_unsigned (Z_to_bv 64 2)) with 2.
  destruct (Z.ltb_spec (bv_unsigned a1) 2) as [L|L].
  - cbv iota.
    assert (E : bs = []) by (destruct bs; [reflexivity | cbn in Hlen; lia]). subst bs.
    step.
    apply (tail ra sp gp tp t0 t1 t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m []);
      first [exact Hq | exact Hqn | exact Hlen' | exact HB | exact HW | rewrite unsigned_lit by lia; lia].
  - cbv iota.
    step. step. step. step. step.
    apply (loop ra sp gp tp t0 t1 t2 s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
             Hq Hqn Hlen' HB HW (length bs) 0);
      first [lia | rewrite unsigned_lit by lia; lia].
Qed.
