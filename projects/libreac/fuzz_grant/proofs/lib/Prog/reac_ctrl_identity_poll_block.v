From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantSweepModel memcpy_c reac_ctrl_identity_poll_block_c.
Import ListNotations.
Open Scope Z_scope.

Lemma wr_ro_disj : forall m d n s bs,
  mem_inv rsegs m -> wr_at rsegs m d n -> ro_bytes rsegs s bs -> 0 < n -> 0 <= s -> (0 < length bs)%nat ->
  d + n <= s \/ s + Z.of_nat (length bs) <= d.
Proof.
  intros m d n s bs HI (Hd & Hdn & HW) HR Hn Hs Hl.
  destruct (Z_le_gt_dec (d + n) s) as [?|H1]; [left; lia|].
  destruct (Z_le_gt_dec (s + Z.of_nat (length bs)) d) as [?|H2]; [right; lia|].
  exfalso.
  destruct (nth_error bs (Z.to_nat (Z.max d s - s))) as [b|] eqn:E.
  2:{ apply nth_error_None in E. lia. }
  pose proof (ro_bytes_nth rsegs bs s _ b HR E) as [_ Hro].
  replace (s + Z.of_nat (Z.to_nat (Z.max d s - s))) with (Z.max d s) in Hro by lia.
  specialize (HW (Z.max d s - d) ltac:(lia)). replace (d + (Z.max d s - d)) with (Z.max d s) in HW by lia.
  destruct (m (wa (Z.max d s))) eqn:Em.
  - pose proof (HI _ _ Em). congruence.
  - pose proof (wview_not_ro rsegs m (wa (Z.max d s)) HW Em). congruence.
Qed.

Lemma gb_ro : forall i, 0 <= i <= 5 -> ro_bytes rsegs (0x10470 + 34 * i) (GB i).
Proof.
  intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) as H by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    apply ro_bytes_b_sound; vm_compute; reflexivity.
Qed.

Lemma mod64_int32_small : forall i, -2^31 <= i < 2^31 ->
  (i mod 18446744073709551616 <= 5 <-> 0 <= i <= 5).
Proof.
  intros i Hi. destruct (Z_lt_le_dec i 0).
  - rewrite <- (Z.mod_add i 1 18446744073709551616) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

Theorem reac_ctrl_identity_poll_block_holds : memcpy_contract -> reac_ctrl_identity_poll_block_contract.
Proof.
  intros MEMC.
  unfold reac_ctrl_identity_poll_block_contract, REAC_CTRL_IDENTITY_POLL_BLOCK, REAC_CTRL_IDENTITY_POLL_BLOCK_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m i lo junk -> Hi HMI ST LO HO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  unfold bv_modulus in Rsp, Ra1.
  zstep. zstep. zstep.
  zstep.
  if_cases HC1; zify_cond HC1.
  - assert (Hn : ~ (0 <= i <= 5)) by (intros Hc; pose proof (proj2 (mod64_int32_small i Hi) Hc); lia).
    assert (Hpf : poll_ok i a1 = false)
      by (unfold poll_ok; destruct (Z.leb_spec 0 i); destruct (Z.leb_spec i 5); cbn [andb]; try reflexivity; lia).
    zstep. finish.
    all: first [ apply munch_refl | apply wmono_refl | (rewrite Hpf; split; reflexivity) ].
  - apply (proj1 (mod64_int32_small i Hi)) in HC1.
    zstep.
    if_cases HC2; zify_cond HC2.
    + assert (Hpf : poll_ok i a1 = false)
        by (unfold poll_ok; replace (bv_unsigned a1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia);
            cbn [negb]; rewrite andb_false_r; reflexivity).
      zstep. finish.
      all: first [ apply munch_refl | apply wmono_refl | (rewrite Hpf; split; reflexivity) ].
    + assert (Hok : poll_ok i a1 = true)
        by (unfold poll_ok; rewrite (proj2 (Z.leb_le 0 i)), (proj2 (Z.leb_le i 5)), (proj2 (Z.eqb_neq _ 0)) by lia; reflexivity).
      destruct (HO Hok) as [HRW HD]. clear HO.
      pose proof (gb_ro i HC1) as HGB.
      pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 34)] m) as MU.
      pose proof (wmono_refl rsegs m) as WM.
      carve_frame 16%nat ST.
      zstep. zstep.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      assert (U34 : bv_unsigned (Z_to_bv 64 34) = 34) by reflexivity.
      assert (UG : bv_unsigned (Z_to_bv 64 (66672 + i * 34)) = 0x10470 + 34 * i)
        by (rewrite unsigned_lit by lia; lia).
      pose proof (wr_ro_disj _ _ _ _ _ HMI (proj2 HRW) HGB ltac:(cbn; lia) ltac:(lia)
                    ltac:(rewrite length_GB; lia)) as HDJ.
      rewrite length_GB in HDJ. cbn [cells_size csize] in HDJ.
      call MEMC.
      { rewrite UG. apply (ro_bytes_at rsegs m0 (0x10470 + 34 * i) (GB i) HMI); [lia | rewrite length_GB; lia | exact HGB]. }
      { rewrite length_GB. reflexivity. }
      { change (Z.to_nat (bv_unsigned (Z_to_bv 64 34))) with 34%nat. exact HRW. }
      { rewrite UG, U34. lia. }
      { exact HMI. }
      zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep.
      finish.
      rewrite Hok. split; [reflexivity|].
      match goal with H : rw_cells _ _ (bv_unsigned a1) _ |- _ => exact H end.
Qed.
