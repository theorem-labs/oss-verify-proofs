From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import sb_ch_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sb_ch_land7 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Theorem sb_ch_holds : sb_ch_contract.
Proof.
  unfold sb_ch_contract, SB_CH, sb_rec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    p cap n over HAL HB HW HN HP MI.
  pose proof (zr_word a0) as Ra0. pose proof (zr_word p) as Rp. pose proof (zr_word cap) as Rcap.
  pose proof (zr_word n) as Rn. unfold inr64 in *.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite !length_app, !length_le8, length_le4 in BB.
  assert (FR : rw_cells rsegs m (bv_unsigned a0) [C8 p; C8 cap; C8 n; C4 over]).
  { split; [split; [cbn; tauto|] |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
    - exact HW. }
  clear HB HW.
  zstep. zstep.
  rewrite (sb_ch_land7 (bv_unsigned a0) HAL). if_false.
  zstep. zstep. zstep. zstep.
  rewrite bv_ltu_Z, (unsigned_lit (bv_unsigned n + 1)) by lia.
  destruct (Z.ltb_spec (bv_unsigned n + 1) (bv_unsigned cap)) as [HC|HC]; cbn [negb].
  - destruct (HP HC) as (HP0 & HPN & HPW & HPD). clear HP.
    pose proof (munch_refl [(bv_unsigned a0 + 16, bv_unsigned a0 + 24);
                            (bv_unsigned p + bv_unsigned n, bv_unsigned p + bv_unsigned n + 1)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. zstep.
    rewrite bv_ltu_Z, (unsigned_lit (bv_unsigned p + bv_unsigned n)) by lia. if_false.
    zstep. zstep. zstep. zstep.
    replace (0 <? bv_unsigned p) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (bv_unsigned p + bv_unsigned n <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    if_false.
    zstep. if_false.
    pose proof (wr_at_store_ok rsegs m0 _ 1 0 1 HPW ltac:(lia) ltac:(lia)) as HS.
    zstep.
    assert (HBY : bytes_at rsegs (write_to_mem m0 (wa (bv_unsigned p + bv_unsigned n + 0)) (le1 a1))
                    (bv_unsigned p + bv_unsigned n + 0) (le1 a1))
      by (apply bytes_at_write_same; rewrite ?length_le1; lia).
    store_done.
    zstep. finish.
    right. split; [exact HC|]. split; [exact MU|]. split.
    + destruct FR as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
    + rewrite Z.add_0_r in HBY. exact HBY.
  - pose proof (munch_refl [(bv_unsigned a0 + 24, bv_unsigned a0 + 28)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. finish.
    left. split; [lia|]. split; [exact MU|].
    destruct FR as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
Qed.
