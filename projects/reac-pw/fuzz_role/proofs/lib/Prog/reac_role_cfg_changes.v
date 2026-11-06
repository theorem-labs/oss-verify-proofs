From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import reac_role_cfg_changes_c.
Import ListNotations.
Open Scope Z_scope.

(** reac_role_cfg_changes of the plain image (0x143e8, 3 instructions), walked with Lib/Tac.v and Lib/Step.v:
    `xor a0, a0, a1; snez a0, a0; ret`. [snez_xor_changes] turns the snez of the xor into changes_res. *)

(** snez (sltu rd, zero, rs) of a xor b is 0 when a and b are the same word, else 1. *)
Lemma snez_xor_changes : forall a b : word,
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (bv_unsigned a) (bv_unsigned b))) = Z_to_bv 64 (changes_res a b).
Proof.
  intros a b. rewrite v_sltu_b2z. f_equal.
  pose proof (zr_word a) as Ra. pose proof (zr_word b) as Rb. unfold inr64 in Ra, Rb.
  rewrite (unsigned_lit 0) by lia.
  rewrite unsigned_lit by (apply (zr_lxor _ _ (zr_word a) (zr_word b))).
  unfold changes_res, bv_eqb.
  destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
  - rewrite E, Z.lxor_nilpotent. reflexivity.
  - assert (L : 0 <= Z.lxor (bv_unsigned a) (bv_unsigned b)) by (apply Z.lxor_nonneg; split; intros; lia).
    assert (N : Z.lxor (bv_unsigned a) (bv_unsigned b) <> 0).
    { intros Z0. apply E. apply Z.lxor_eq_0_iff. exact Z0. }
    destruct (Z.ltb_spec 0 (Z.lxor (bv_unsigned a) (bv_unsigned b))); [reflexivity | lia].
Qed.

Theorem reac_role_cfg_changes_holds : reac_role_cfg_changes_contract.
Proof.
  unfold reac_role_cfg_changes_contract, REAC_ROLE_CFG_CHANGES.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m.
  (* xor a0, a0, a1; snez a0, a0 *)
  step. step.
  match goal with |- context [v_sltu ?x ?y] =>
    replace (v_sltu x y) with (Z_to_bv 64 (changes_res a0 a1)) by (symmetry; apply snez_xor_changes)
  end.
  (* ret *)
  step. finish.
Qed.
