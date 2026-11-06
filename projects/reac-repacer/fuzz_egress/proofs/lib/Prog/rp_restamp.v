From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Prog Require Import rp_restamp_c.
Import ListNotations.
Open Scope Z_scope.

Theorem rp_restamp_holds : rp_restamp_contract.
Proof.
  unfold rp_restamp_contract, RP_RESTAMP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Ha0 HW HI.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. change (bv_modulus 64) with (2^64) in Ra0.
  pose proof HW as (HW0 & HW1 & _).
  assert (HS1 : store_ok rsegs m (wa (bv_unsigned a0 + 14)) 1 = true).
  { replace (wa (bv_unsigned a0 + 14)) with (wa (bv_unsigned a0 + 14 + 0)) by (f_equal; lia).
    apply (wr_at_store_ok rsegs m _ 2 0 1 HW); cbn; lia. }
  step.
  step.
  change (Z_to_bv 64 (bv_unsigned a0 + 14)) with (wa (bv_unsigned a0 + 14)).
  set (m1 := write_to_mem m (wa (bv_unsigned a0 + 14)) (le1 a1)).
  assert (HS2 : store_ok rsegs m1 (wa (bv_unsigned a0 + 15)) 1 = true).
  { replace (wa (bv_unsigned a0 + 15)) with (wa (bv_unsigned a0 + 14 + 1)) by (f_equal; lia).
    apply (wr_at_store_ok rsegs m1 _ 2 1 1); [apply wr_at_write; exact HW | lia | cbn; lia]. }
  step.
  step.
  change (Z_to_bv 64 (bv_unsigned a0 + 15)) with (wa (bv_unsigned a0 + 15)).
  apply evt_done. exists a1, (Z_to_bv 64 (bv_unsigned a1 ≫ 8)).
  eexists. split; [reflexivity|].
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. change (bv_modulus 64) with (2^64) in Ra1.
  assert (L1 : forall v, length (le1 v) = 1%nat) by exact length_le1.
  split; [|split; [|split]].
  - apply munch_write; [apply munch_write; [apply munch_refl | lia | rewrite L1; cbn; lia | rewrite L1; cbn; lia]
                       | lia | rewrite L1; cbn; lia | rewrite L1; cbn; lia].
  - apply wmono_write, wmono_write, wmono_refl.
  - apply mem_inv_store; [apply mem_inv_store; [exact HI | rewrite L1; exact HS1] | rewrite L1; exact HS2].
  - assert (E : restamp_bytes (bv_unsigned a1) = le1 a1 ++ le1 (Z_to_bv 64 (bv_unsigned a1 ≫ 8))).
    { unfold restamp_bytes, le1. cbn [Z_to_le_bytes app]. rewrite Z.shiftr_div_pow2 by lia.
      rewrite (unsigned_lit (bv_unsigned a1 / 2 ^ 8)).
      2: { split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (bv_unsigned a1)); [apply Z.div_le_upper_bound; lia | lia]. }
      f_equal; [apply Z_to_bv8_mod; rewrite Z.mod_mod by lia; reflexivity|].
      f_equal. apply Z_to_bv8_mod. rewrite Z.mod_mod by lia. reflexivity. }
    rewrite E. apply bytes_at_app. rewrite L1. cbn [Z.of_nat Pos.of_succ_nat].
    split.
    + apply bytes_at_write_other; [apply bytes_at_write_same; [lia | rewrite L1; cbn; lia] | lia | rewrite L1; cbn; lia
                                  | rewrite L1; cbn; lia].
    + replace (bv_unsigned a0 + 14 + Z.of_nat 1) with (bv_unsigned a0 + 15) by lia.
      apply bytes_at_write_same; [lia | rewrite L1; cbn; lia].
Qed.
