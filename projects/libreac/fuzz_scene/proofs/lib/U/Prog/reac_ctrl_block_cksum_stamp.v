From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import RcModel RcLib RcFin RcFinLib.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import reac_ctrl_block_cksum_stamp_c.
Import ListNotations.
Open Scope Z_scope.

Section Loop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z) (B : list byte).
  Hypothesis Hq : 0 < q.
  Hypothesis Hq32 : q + 32 <= 2^64.
  Hypothesis Hlen : length B = 32%nat.
  Hypothesis HB : bytes_at rsegs m q B.
  Hypothesis HW : wr_at rsegs m q 32.

  Definition Qv : machine_state -> Prop :=
    fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch [(q + 31, q + 32)] m m' /\ wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m')
         /\ rw_cells rsegs m' q [CB 32 (stamp32 B)] /\ blocksum (stamp32 B) = 0.

  Lemma loop : forall k i x6,
    (i + k = 31)%nat -> (0 < k)%nat ->
    evt rsegs Qv
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 (psum B i)) (Z_to_bv 64 (31 - Z.of_nat i))
               (Z_to_bv 64 1) (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (q + Z.of_nat i)) x6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15770) fc None m (seg_rom rsegs)).
  Proof.
    induction k as [|k IH]; intros i x6 Hik Hk; [lia|].
    pose proof (rd_byte rsegs m q B i HB ltac:(lia)) as RD.
    pose proof (psum_range B i) as PR.
    step.
    rewrite (rcf_ltu (q + Z.of_nat i) q) by lia.
    replace (q + Z.of_nat i <? q) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    step. step. step.
    rewrite (rcf_chk (q + Z.of_nat i)) by lia. cbv iota.
    step.
    rewrite (rcf_eqb q 0) by lia. replace (q =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step. step. step. step. step. step.
    rewrite psum_S_zxb.
    rewrite (rcf_eqb (31 - Z.of_nat i + -1) 0) by lia.
    destruct k as [|k].
    - replace (31 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      replace i with 30%nat in * by lia.
      assert (HS : store_ok rsegs m (wa (q + 31)) 1 = true) by (apply (wr_at_store_ok rsegs m q 32 31 1 HW); lia).
      step. step.
      rewrite (rcf_ltu_neg q (-31)) by lia.
      replace (q <? 2^64 + -31) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
      step. step. step.
      pose proof (psum_range B 31) as R31. change (Z.of_nat 31) with 31 in R31.
      rewrite (rcf_neg_byte (psum B 31)) by lia.
      change (Z_to_bv 64 (q + 31)) with (wa (q + Z.of_nat 31)).
      assert (HW2 : wr_at rsegs m q (Z.of_nat (length B))) by (rewrite Hlen; exact HW).
      destruct (rcf_store1 rsegs [(q + 31, q + 32)] m m q B 31 (Z_to_bv 8 ((- psum B 31) mod 256))
                  (munch_refl _ _) (wmono_refl _ _) (fun H => H) HB HW2 ltac:(lia) ltac:(cbn [inside]; left; lia))
        as (MU & WM & MI & HB' & HW').
      rewrite Hlen in HW'.
      apply evt_done. unfold Qv. do 8 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      split; [|apply rcf_stamp32_sum; exact Hlen].
      unfold rw_cells, cells_at. split; [split|].
      + cbn [cells_wf cell_wf]. split; [apply rcf_stamp32_len; exact Hlen | exact I].
      + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB'.
      + cbn [cells_size csize]. exact HW'.
    - replace (31 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (31 - Z.of_nat i + -1) with (31 - Z.of_nat (S i)) by lia.
      replace (q + Z.of_nat i + 1) with (q + Z.of_nat (S i)) by lia.
      apply (IH (S i)); lia.
  Qed.

  Lemma loop0 : forall x6,
    evt rsegs Qv
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 0) (Z_to_bv 64 31)
               (Z_to_bv 64 1) (Z_to_bv 64 q) (Z_to_bv 64 q) x6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15770) fc None m (seg_rom rsegs)).
  Proof.
    intros x6. pose proof (loop 31 0 x6 eq_refl ltac:(lia)) as L.
    replace (q + Z.of_nat 0) with q in L by lia. exact L.
  Qed.
End Loop.

Theorem reac_ctrl_block_cksum_stamp_holds : reac_ctrl_block_cksum_stamp_contract.
Proof.
  unfold reac_ctrl_block_cksum_stamp_contract, REAC_CTRL_BLOCK_CKSUM_STAMP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q B
    Hq Hq32 -> HRW.
  destruct HRW as [[HWF HB] HW]. cbn [cells_bytes cbytes cells_size csize cells_wf cell_wf] in HB, HW, HWF.
  rewrite app_nil_r in HB. destruct HWF as [Hlen _].
  step. step. step. step. step.
  rewrite v_sltu_b2z. rewrite !unsigned_lit by lia.
  replace (0 <? q) with true by (symmetry; apply Z.ltb_lt; lia). change (Z.b2z true) with 1.
  apply loop0; assumption.
Qed.