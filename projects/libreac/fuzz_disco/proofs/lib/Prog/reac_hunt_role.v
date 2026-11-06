From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_hunt_role_c.
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_at_read0 : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof H as (H0 & H1 & _).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a bs 0 (length bs) H) by lia.
  f_equal. apply firstn_all.
Qed.

Lemma sx32_lit : forall v, -2^31 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. f_equal. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Ltac set_a0 V :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ _ (TNode _ _ (TNode (TNode _ (Some ?X) _) _ _))) _ _ _ _ _ _) => replace X with V
  end.

Theorem reac_hunt_role_holds : reac_hunt_role_contract.
Proof.
  unfold reac_hunt_role_contract, REAC_HUNT_ROLE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m h v E Hh H8 Hv HB. subst a0.
  pose proof (bytes_at_read0 m _ _ HB) as RD.
  change (ov_read_bytes rsegs m (wa (h + 440)) 4 = Some (le4 (Z_to_bv 64 v))) in RD.
  step. step. step. step.
  set_a0 (Z_to_bv 64 (reac_hunt_role_model v)).
  - apply evt_done. eexists. reflexivity.
  - unfold v_sltiu, reac_hunt_role_model. rewrite sx32_lit by lia. rewrite !unsigned_lit_wrap.
    replace (bv_wrap 64 1) with 1 by reflexivity.
    destruct (Z.eqb_spec v 2) as [-> | Hne].
    + vm_compute. reflexivity.
    + rewrite (proj2 (Z.ltb_ge _ 1)) by (Z.div_mod_to_equations; lia). reflexivity.
Qed.
