From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_hunt_heard_anything_c.
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

Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 64) with (2^63) by reflexivity.
  replace (bv_modulus 64) with (2^64) by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac zcu HC := unfold bv_eqb, bv_ltu in HC; rewrite ?unsigned_lit_wrap in HC; try change (bv_wrap 64 7) with 7 in HC; rewrite ?land7 in HC;
  zify_bool HC; Z.div_mod_to_equations; lia.

Theorem reac_hunt_heard_anything_holds : reac_hunt_heard_anything_contract.
Proof.
  unfold reac_hunt_heard_anything_contract, REAC_HUNT_HEARD_ANYTHING.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m h n E Hh H8 Hn HB. subst a0.
  pose proof (bytes_at_read0 m _ _ HB) as RD.
  change (ov_read_bytes rsegs m (wa (h + 384)) 4 = Some (le4 (Z_to_bv 64 n))) in RD.
  step. if_cases HCa; [exfalso; zcu HCa | ]. step. step. if_cases HCb; [exfalso; zcu HCb | ].
  step. step. step.
  set_a0 (Z_to_bv 64 (reac_hunt_heard_anything_model n)).
  - apply evt_done. eexists. reflexivity.
  - unfold v_slt, c_lts, bv_lts, reac_hunt_heard_anything_model. rewrite sx32_lit by lia.
    rewrite !signed_lit by lia. destruct (0 <? n); reflexivity.
Qed.
