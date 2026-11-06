From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_hunt_verdict_name_c.
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_at_read0 : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof H as (H0 & H1 & _).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a bs 0 (length bs) H) by lia.
  f_equal. apply firstn_all.
Qed.

Ltac set_a0 V :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ _ (TNode _ _ (TNode (TNode _ (Some ?X) _) _ _))) _ _ _ _ _ _) => replace X with V
  end.

Ltac vfin S :=
  apply evt_done; cbv beta; eexists; split; [reflexivity | exact S].

Theorem reac_hunt_verdict_name_holds : reac_hunt_verdict_name_contract.
Proof.
  unfold reac_hunt_verdict_name_contract, REAC_HUNT_VERDICT_NAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m v E Hv HT0 HT1 HT2 HSM HSS HSR HSH. subst a0.
  pose proof (bytes_at_read0 m _ _ HT0) as R0. change (ov_read_bytes rsegs m (wa 0x1058c) 4 = Some (le4 (Z_to_bv 64 (-422)))) in R0.
  pose proof (bytes_at_read0 m _ _ HT1) as R1. change (ov_read_bytes rsegs m (wa 0x10590) 4 = Some (le4 (Z_to_bv 64 (-313)))) in R1.
  pose proof (bytes_at_read0 m _ _ HT2) as R2. change (ov_read_bytes rsegs m (wa 0x10594) 4 = Some (le4 (Z_to_bv 64 (-477)))) in R2.
  assert (Hc : v = 1 \/ v = 2 \/ v = 3 \/ (v < 1 \/ 3 < v)) by lia.
  destruct Hc as [-> | [-> | [-> | Hd]]].
  - step. step. step. if_false. step. step. step. step. step. step. step.
    set_a0 (Z_to_bv 64 A_MASTER); [vfin HSM | apply bv_eq; vm_compute; reflexivity].
  - step. step. step. if_false. step. step. step. step. step. step. step.
    set_a0 (Z_to_bv 64 A_SLAVE); [vfin HSS | apply bv_eq; vm_compute; reflexivity].
  - step. step. step. if_false. step. step. step. step. step. step. step.
    set_a0 (Z_to_bv 64 A_REFUSED); [vfin HSR | apply bv_eq; vm_compute; reflexivity].
  - assert (Hm : reac_hunt_verdict_name_model v = A_HUNTING).
    { unfold reac_hunt_verdict_name_model.
      rewrite (proj2 (Z.eqb_neq v 1)), (proj2 (Z.eqb_neq v 2)), (proj2 (Z.eqb_neq v 3)) by lia. reflexivity. }
    assert (Hs : reac_hunt_verdict_name_str v = S_HUNTING).
    { unfold reac_hunt_verdict_name_str.
      rewrite (proj2 (Z.eqb_neq v 1)), (proj2 (Z.eqb_neq v 2)), (proj2 (Z.eqb_neq v 3)) by lia. reflexivity. }
    rewrite Hm, Hs.
    assert (HB : bv_ltu (Z_to_bv 64 2) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + -1))) = true).
    { unfold bv_ltu. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
      replace (bv_half_modulus 32) with 2147483648 by reflexivity.
      replace (bv_modulus 32) with 4294967296 by reflexivity.
      apply Z.ltb_lt. Z.div_mod_to_equations. lia. }
    step. step. step. rewrite HB. cbv iota. step. step. step.
    set_a0 (Z_to_bv 64 A_HUNTING); [vfin HSH | apply bv_eq; vm_compute; reflexivity].
Qed.
