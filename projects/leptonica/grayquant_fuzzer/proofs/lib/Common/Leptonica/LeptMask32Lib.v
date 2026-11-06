(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs GrayLib LeptExec DitherLib LeptRmcLib.
Import SX2. Import SX2S.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition px_r (pw : Z) : Z := Z.shiftr pw 24.
Definition px_m (k pw : Z) : Z := Z.shiftr ((2 ^ k * pw) mod 2 ^ 64) 56.

Lemma px_r_range : forall pw, 0 <= pw < 2 ^ 32 -> 0 <= px_r pw <= 255.
Proof.
  intros pw H. unfold px_r. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  assert (pw / 2 ^ 24 < 256) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma px_m_range : forall k pw, 0 <= px_m k pw <= 255.
Proof.
  intros k pw. unfold px_m. pose proof (Z.mod_pos_bound (2 ^ k * pw) (2 ^ 64) ltac:(lia)) as B.
  rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.div_pos ((2 ^ k * pw) mod 2 ^ 64) (2 ^ 56) ltac:(lia) ltac:(lia)).
  assert ((2 ^ k * pw) mod 2 ^ 64 / 2 ^ 56 < 256) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Section Mask32Lib.
Context {fx : FPState}.

Lemma px_r_eq : forall pw, 0 <= pw < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 pw) (Z_to_bv 64 24) = Z_to_bv 64 (px_r pw).
Proof. intros pw H. rewrite alu_srl. unfold v_srl, px_r. rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma px_m_eq : forall k pw, 0 <= k ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 (2 ^ k)) (Z_to_bv 64 pw)) (Z_to_bv 64 56) = Z_to_bv 64 (px_m k pw).
Proof.
  intros k pw Hk. rewrite m_mul, zbv_mul. rewrite alu_srl. unfold v_srl, px_m.
  rewrite (u_Z2bv 56) by lia. change (56 mod 64) with 56. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma blt_m1_false : forall x, 0 <= x < 2 ^ 63 -> branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 18446744073709551615) = false.
Proof.
  intros x Hx. cbn [branch_taken]. unfold bv_lts. rewrite bv_signed_Zs by lia.
  replace (bv_signed (Z_to_bv 64 18446744073709551615)) with (-1) by (vm_compute; reflexivity). apply Z.ltb_ge. lia.
Qed.
Lemma blt_1 : forall x (b : bool), 0 <= x < 2 ^ 63 -> (if b then 1 < x else x <= 1) -> branch_taken BC_LT (Z_to_bv 64 1) (Z_to_bv 64 x) = b.
Proof.
  intros x b Hx Hb. cbn [branch_taken]. unfold bv_lts. rewrite !bv_signed_Zs by lia. destruct b; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

(* [comment removed for export] *)
Lemma ub_mul_guard : forall a b p, a * b = p -> 0 <= a < 2 ^ 31 -> 0 <= b < 2 ^ 31 -> 0 <= p < 2 ^ 31 ->
  branch_taken BC_NE (sext 64 (mul_div M_MUL (low32 (Z_to_bv 64 a)) (low32 (Z_to_bv 64 b)))) (mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b)) = false.
Proof.
  intros a b p E Ha Hb Hp. rewrite w_mulw, m_mul. rewrite zbv_mul. rewrite zbv_mulw_small by lia. rewrite E. cbn [branch_taken]. unfold bv_eqb.
  rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma ub_ptr_guard : forall a b p base, a * b = p -> 0 <= p < 2 ^ 31 -> 0 <= base -> base + 4 * p < 2 ^ 63 ->
  branch_taken BC_EQ
    (alu64 ALU_XOR (alu64 ALU_XOR
       (alu64 ALU_SLTU (alu64 ALU_ADD (Z_to_bv 64 base) (mul_div M_MUL (Z_to_bv 64 4)
           (sext 64 (alu32 ALU_ADD (low32 (mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b))) (low32 (Z_to_bv 64 0)))))) (Z_to_bv 64 base))
       (alu64 ALU_SLT (sext 64 (alu32 ALU_ADD (low32 (mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b))) (low32 (Z_to_bv 64 0)))) (Z_to_bv 64 0)))
       (Z_to_bv 64 1)) (Z_to_bv 64 0) = false.
Proof.
  intros a b p base E Hp Hb Hbp. rewrite !m_mul. rewrite !zbv_mul. rewrite E. rewrite !w_addw. rewrite !zbv_addw_small by lia. rewrite zbv_mul, alu_add, zbv_add.
  rewrite alu_sltu. rewrite zbv_sltu_ge by lia. rewrite alu_slt. rewrite v_slt_Z by lia. replace (p + 0 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sx32_val : forall pw, 0 <= pw < 2 ^ 32 ->
  exists spw, ext_val true 0 4 (Z_to_bv 64 pw) = Z_to_bv 64 spw /\ 0 <= spw < 2 ^ 64 /\ spw mod 2 ^ 32 = pw.
Proof.
  intros pw H. unfold ext_val, ext_Z. rewrite u_Z2bv by lia. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small pw) by lia. change (8 * N.of_nat 4)%N with 32%N.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  destruct (Z_lt_ge_dec pw (2 ^ 31)) as [L|G].
  - exists pw. rewrite Z.mod_small by lia. split; [f_equal; lia|]. split; [lia | apply Z.mod_small; lia].
  - exists (pw + (2 ^ 64 - 2 ^ 32)). replace ((pw + 2 ^ 31) mod 2 ^ 32) with (pw - 2 ^ 31).
    + split.
      * apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        replace (pw + (2 ^ 64 - 2 ^ 32)) with (pw - 2 ^ 31 - 2 ^ 31 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. reflexivity.
      * split; [lia|]. replace (pw + (2 ^ 64 - 2 ^ 32)) with (pw + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
    + symmetry. replace (pw + 2 ^ 31) with (pw - 2 ^ 31 + 1 * 2 ^ 32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma srlw24_sx : forall spw, 0 <= spw < 2 ^ 64 ->
  sext 64 (alu32 ALU_SRL (low32 (Z_to_bv 64 spw)) (low32 (Z_to_bv 64 24))) = Z_to_bv 64 (px_r (spw mod 2 ^ 32)).
Proof.
  intros spw H. rewrite w_srlw. unfold v_srlw. rewrite !u_Z2bv by lia. change (24 mod 32) with 24.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  pose proof (Z.mod_pos_bound spw (2 ^ 32) ltac:(lia)) as B. pose proof (px_r_range (spw mod 2 ^ 32) B) as R. unfold px_r in *.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia). reflexivity.
Qed.
Lemma px_m_sx : forall k spw, 32 <= k -> px_m k spw = px_m k (spw mod 2 ^ 32).
Proof.
  intros k spw Hk. unfold px_m. f_equal. rewrite (Z.div_mod spw (2 ^ 32)) at 1 by lia.
  replace (2 ^ k * (2 ^ 32 * (spw / 2 ^ 32) + spw mod 2 ^ 32)) with (2 ^ k * (spw mod 2 ^ 32) + (2 ^ (k - 32) * (spw / 2 ^ 32)) * 2 ^ 64).
  - apply Z_mod_plus_full.
  - replace (2 ^ k) with (2 ^ (k - 32) * 2 ^ 32) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). ring.
Qed.

(* [comment removed for export] *)
Lemma sub0_Z : forall v, 0 <= v < 2 ^ 31 -> alu64 ALU_SUB (Z_to_bv 64 0) (Z_to_bv 64 v) = Z_to_bv 64 (- v).
Proof. intros v H. rewrite alu_sub. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma swrap32_neg : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap32_shift : forall z k, bv_swrap 32 (z + k * 2 ^ 64) = bv_swrap 32 z.
Proof.
  intros z k. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32). f_equal.
  replace (z + k * 2 ^ 64 + bv_half_modulus 32) with (z + bv_half_modulus 32 + (k * 2 ^ 32) * 2 ^ 32) by (change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); ring).
  apply Z_mod_plus_full.
Qed.
Lemma u_neg : forall v, 0 <= v < 2 ^ 31 -> bv_unsigned (Z_to_bv 64 (- v)) = if Z.eqb v 0 then 0 else - v + 1 * 2 ^ 64.
Proof.
  intros v H. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|]. rewrite <- (Z_mod_plus_full (- v) 1 (2 ^ 64)). apply Z.mod_small. lia.
Qed.
Lemma subw0_Z : forall v, 0 <= v < 2 ^ 31 -> sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 (Z_to_bv 64 v))) = Z_to_bv 64 (- v).
Proof. intros v H. rewrite w_subw. unfold v_subw. rewrite !u_Z2bv by lia. rewrite swrap32_neg by lia. reflexivity. Qed.
Lemma sextw_neg : forall v, 0 <= v < 2 ^ 31 -> sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 (- v))) (low32 (Z_to_bv 64 0))) = Z_to_bv 64 (- v).
Proof.
  intros v H. rewrite w_addw. unfold v_addw. rewrite u_neg by lia. rewrite (u_Z2bv 0) by lia. f_equal.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|]. rewrite Z.add_0_r, swrap32_shift. apply swrap32_neg. lia.
Qed.
Lemma negw_neg : forall v, 0 <= v < 2 ^ 31 -> sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 (Z_to_bv 64 (- v)))) = Z_to_bv 64 v.
Proof.
  intros v H. rewrite w_subw. unfold v_subw. rewrite u_neg by lia. rewrite (u_Z2bv 0) by lia. f_equal.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|]. replace (0 - (- v + 1 * 2 ^ 64)) with (v + (-1) * 2 ^ 64) by lia. rewrite swrap32_shift. apply swrap32_neg. lia.
Qed.
(* [comment removed for export] *)
Lemma bgez_neg : forall v, 0 <= v < 2 ^ 31 -> branch_taken BC_GE (Z_to_bv 64 (- v)) (Z_to_bv 64 0) = Z.eqb v 0.
Proof.
  intros v H. cbn [branch_taken]. unfold bv_lts. rewrite !bv_signed_Zs by lia. destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply negb_false_iff. apply Z.ltb_lt. lia.
Qed.
End Mask32Lib.
