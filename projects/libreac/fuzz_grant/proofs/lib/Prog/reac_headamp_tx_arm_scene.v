From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel TxStore reac_headamp_tx_arm_scene_c.
Import ListNotations.
Open Scope Z_scope.

Ltac arm_exit :=
  zstep; apply evt_done; do 16 eexists; split; [reflexivity|];
  match goal with |- (if ?c then _ else _) => replace c with true by (symmetry; apply orb_true_iff; lia) end;
  reflexivity.

Ltac arm_tail t base width :=
  tx_store t 436 1%nat; tx_store t 437 1%nat; tx_store t 440 4%nat; tx_store t 444 4%nat;
  tx_store t 448 1%nat; tx_store t 449 1%nat; tx_store t 450 1%nat; tx_store t 456 4%nat;
  zstep; apply evt_done; do 16 eexists; split; [reflexivity|];
  replace ((width =? 0) || (48 <=? base)) with false
    by (symmetry; apply orb_false_iff; split; [apply Z.eqb_neq | apply Z.leb_gt]; lia);
  split; [|split];
  [ match goal with H : bytes_at rsegs ?mf t _ |- bytes_at rsegs ?mf t _ => eapply bytes_at_ext; [exact H|] end
  | assumption | assumption ].

Theorem reac_headamp_tx_arm_scene_holds : reac_headamp_tx_arm_scene_contract.
Proof.
  unfold reac_headamp_tx_arm_scene_contract, REAC_HEADAMP_TX_ARM_SCENE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m t base width T -> -> -> HB0 HW0 HL HB HW.
  pose proof (bytes_at_bound rsegs m t T HB) as Ht. rewrite HL in Ht. change (Z.of_nat 460) with 460 in Ht.
  assert (Ht' : 0 <= t < 2^64) by lia.
  pose proof (munch_refl [(t, t + 460)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep.
  if_cases HC1; zify_cond HC1.
  - arm_exit.
  - zstep.
    if_cases HC2; zify_cond HC2.
    + arm_exit.
    + zstep. zstep. zstep.
      if_cases HC3; zify_cond HC3.
      * arm_tail t base width.
        unfold arm_T, arm_w. rewrite (proj2 (Z.ltb_ge 48 (base + width))) by lia. reflexivity.
      * zstep. arm_tail t base width.
        unfold arm_T, arm_w. rewrite (proj2 (Z.ltb_lt 48 (base + width))) by lia. reflexivity.
Qed.
