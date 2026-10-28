(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BAgentLib BSymExec2 BSymExec2Sound BainDefs.
Import ListNotations.
Import BPropExec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Definition cfg_hi_Z (b1 : Z) : Z :=
  Z.shiftr ((2 ^ 57 * (bv_swrap 8 b1 mod 2 ^ 64)) mod 2 ^ 64) 49.

Definition cfg_hi_ok (b1 : Z) : bool := Z.eqb (cfg_hi_Z b1) (256 * (b1 mod 128)).

Lemma cfg_hi_all : forallb cfg_hi_ok (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cfg_hi_val : forall b1, 0 <= b1 < 256 -> cfg_hi_Z b1 = 256 * (b1 mod 128).
Proof.
  intros b1 Hb.
  assert (Hin : In b1 (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat b1). split; [lia|]. apply in_seq. lia. }
  pose proof (proj1 (forallb_forall _ _) cfg_hi_all b1 Hin) as H. unfold cfg_hi_ok in H.
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma lor_disjoint_add : forall a k, 0 <= a < 256 -> 0 <= k -> Z.lor (256 * k) a = 256 * k + a.
Proof.
  intros a k Ha Hk. rewrite <- Z.lxor_lor.
  - symmetry. rewrite Z.add_comm. rewrite Z.add_nocarry_lxor. + apply Z.lxor_comm. +
      rewrite Z.land_comm.
      apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
      destruct (Z_lt_le_dec n 8) as [Hl|Hh].
      * replace (256 * k) with (k * 2 ^ 8) by lia. rewrite Z.mul_pow2_bits by lia.
        rewrite (Z.testbit_neg_r k) by lia. reflexivity.
      * rewrite (Z.bits_above_log2 a n); [apply andb_false_r| lia |].
        destruct (Z.eq_dec a 0) as [->|Hnz]; [cbn; lia|].
        apply Z.lt_le_trans with (m := 8); [|lia]. apply Z.log2_lt_pow2; lia.
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 8) as [Hl|Hh].
    + replace (256 * k) with (k * 2 ^ 8) by lia. rewrite Z.mul_pow2_bits by lia.
      rewrite (Z.testbit_neg_r k) by lia. reflexivity.
    + rewrite (Z.bits_above_log2 a n); [apply andb_false_r| lia |].
      destruct (Z.eq_dec a 0) as [->|Hnz]; [cbn; lia|].
      apply Z.lt_le_trans with (m := 8); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma cfg_word : forall (b0 b1 : Z), 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  v_or (v_srl (v_mul (Z_to_bv 64 (2 ^ 57)) (Z_to_bv 64 (bv_swrap 8 b1))) (Z_to_bv 64 49)) (Z_to_bv 64 b0)
  = Z_to_bv 64 ((b0 + 256 * b1) mod 32768).
Proof.
  intros b0 b1 H0 H1.
  unfold v_or, v_srl, v_mul. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  change (49 mod 2 ^ 64 mod 64) with 49. rewrite (Z.mod_small (2 ^ 57)) by lia.
  pose proof (cfg_hi_val b1 H1) as Hv. unfold cfg_hi_Z in Hv.
  assert (Hr : 0 <= 256 * (b1 mod 128) < 2 ^ 64) by (pose proof (Z.mod_pos_bound b1 128); lia).
  rewrite (Z.mod_small (Z.shiftr _ 49)).
  2:{ rewrite Hv. exact Hr. }
  rewrite Hv. rewrite (Z.mod_small b0) by lia.
  rewrite lor_disjoint_add by (pose proof (Z.mod_pos_bound b1 128); lia).
  f_equal. pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as Hm.
  replace (b0 + 256 * b1) with ((b0 + 256 * (b1 mod 128)) + (b1 / 128) * 32768)
    by (rewrite (Z.div_mod b1 128) at 1 by lia; lia).
  rewrite Z_mod_plus_full. symmetry. rewrite Z.mod_small by lia. lia.
Qed.

Lemma hdr_cfg_range : forall data, 0 <= hdr_cfg data < 32768.
Proof. intros. unfold hdr_cfg. apply Z.mod_pos_bound. lia. Qed.
