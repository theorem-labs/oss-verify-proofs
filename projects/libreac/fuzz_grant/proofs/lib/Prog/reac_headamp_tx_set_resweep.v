From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel reac_headamp_tx_set_resweep_c.
Import ListNotations.
Open Scope Z_scope.

Theorem reac_headamp_tx_set_resweep_holds : reac_headamp_tx_set_resweep_contract.
Proof.
  unfold reac_headamp_tx_set_resweep_contract, REAC_HEADAMP_TX_SET_RESWEEP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m t T -> HL HB HW.
  pose proof (bytes_at_bound rsegs m t T HB) as Ht. rewrite HL in Ht. change (Z.of_nat 460) with 460 in Ht.
  assert (HS1 : store_ok rsegs m (wa (t + 452)) 4 = true) by (apply (wr_at_store_ok rsegs m t 460 452 4 HW); lia).
  zstep.
  change (Z_to_bv 64 (t + 452)) with (wa (t + 452)).
  set (m1 := write_to_mem m (wa (t + 452)) (le4 a1)).
  pose proof (wr_at_write rsegs m t 460 (wa (t + 452)) (le4 a1) HW) as HW1. fold m1 in HW1.
  assert (HS2 : store_ok rsegs m1 (wa (t + 456)) 4 = true) by (apply (wr_at_store_ok rsegs m1 t 460 456 4 HW1); lia).
  zstep. zstep.
  change (Z_to_bv 64 (t + 456)) with (wa (t + 456)).
  apply evt_done. do 15 eexists. exists (write_to_mem m1 (wa (t + 456)) (le4 (Z_to_bv 64 0))).
  split; [reflexivity|].
  split; [|split].
  - unfold set_resweep_T.
    change 456%nat with (Z.to_nat 456). change 452%nat with (Z.to_nat 452).
    apply bytes_at_write_inside; [|lia|rewrite upd_bytes_length; rewrite ?length_le4, ?HL; cbn; lia].
    apply bytes_at_write_inside; [exact HB|lia|rewrite ?length_le4, HL; cbn; lia].
  - apply munch_write; [|lia|rewrite length_le4; cbn; lia|cbn [inside]; rewrite length_le4; cbn; lia].
    apply munch_write; [apply munch_refl|lia|rewrite length_le4; cbn; lia|cbn [inside]; rewrite length_le4; cbn; lia].
  - apply wmono_write. apply wmono_write. apply wmono_refl.
Qed.
