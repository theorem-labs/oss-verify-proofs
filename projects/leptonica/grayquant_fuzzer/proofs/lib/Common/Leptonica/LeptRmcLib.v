(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec SeqExec CatSim StepTac Hoare StoreOk MemSplit LibMaskBits RefMemcpyLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib DitherLib.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition lut_o0 (sw : Z) : Z := 4 * Z.land sw 255.
Definition lut_o1 (sw : Z) : Z := Z.land (Z.shiftr sw 6) 1020.
Definition lut_o2 (sw : Z) : Z := Z.land (Z.shiftr sw 14) 1020.
Definition lut_o3 (sw : Z) : Z := 4 * Z.shiftr sw 24.

Lemma land_le_l' : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros a b Ha Hb. pose proof (Z.add_lor_land (Z.ldiff a b) (Z.land a b)) as Hal. rewrite Z.lor_ldiff_and in Hal.
  assert (Hand : Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  rewrite Hand in Hal. assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia). lia.
Qed.
Lemma land_le_r' : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= b.
Proof. intros a b Ha Hb. rewrite Z.land_comm. apply land_le_l'; assumption. Qed.

Lemma lut_o_range : forall sw, 0 <= sw < 2 ^ 32 ->
  0 <= lut_o0 sw <= 1020 /\ 0 <= lut_o1 sw <= 1020 /\ 0 <= lut_o2 sw <= 1020 /\ 0 <= lut_o3 sw <= 1020.
Proof.
  intros sw Hsw. unfold lut_o0, lut_o1, lut_o2, lut_o3.
  pose proof (Z.land_nonneg sw 255) as N0. pose proof (land_le_r' sw 255 ltac:(lia) ltac:(lia)) as U0.
  assert (S6 : 0 <= Z.shiftr sw 6) by (apply Z.shiftr_nonneg; lia). assert (S14 : 0 <= Z.shiftr sw 14) by (apply Z.shiftr_nonneg; lia).
  pose proof (Z.land_nonneg (Z.shiftr sw 6) 1020) as N1. pose proof (land_le_r' (Z.shiftr sw 6) 1020 S6 ltac:(lia)) as U1.
  pose proof (Z.land_nonneg (Z.shiftr sw 14) 1020) as N2. pose proof (land_le_r' (Z.shiftr sw 14) 1020 S14 ltac:(lia)) as U2.
  assert (S24 : 0 <= Z.shiftr sw 24 < 256).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma rdv_byte_range : forall bs : list byte, length bs = 1%nat -> 0 <= rdv false 1 bs <= 255.
Proof.
  intros bs L. destruct bs as [|b [|? ?]]; cbn in L; try lia. unfold rdv, extz. cbn [bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as B. change (bv_modulus 8) with 256 in B.
  rewrite Z.shiftl_0_l, Z.lor_0_r. rewrite u_Z2bv by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall g, 0 <= g < 2 ^ 64 -> Z.lxor g (2 ^ 64 - 1) = 2 ^ 64 - 1 - g.
Proof.
  intros g Hg. change (2 ^ 64 - 1) with (Z.ones 64).
  assert (N : Z.land (Z.lxor g (Z.ones 64)) g = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z_lt_ge_dec i 64) as [L|G].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit g i); reflexivity.
    - rewrite (Z.bits_above_log2 g i); [apply andb_false_r | lia |]. destruct (Z.eq_dec g 0) as [->|NZ]; [cbn; lia|].
      assert (Z.log2 g < 64) by (apply Z.log2_lt_pow2; lia). lia. }
  pose proof (Z.add_nocarry_lxor _ _ N) as E.
  assert (X : Z.lxor (Z.lxor g (Z.ones 64)) g = Z.ones 64) by (rewrite (Z.lxor_comm g), Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r; reflexivity).
  rewrite X in E. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_word_val : forall {fx : FPState} segs (M : word -> option byte) (a : word) bs, rdn segs M a 4 = Some bs ->
  exists v, 0 <= v < 2 ^ 32 /\ rdn segs M a 4 = Some (Z_to_le_bytes 4 v).
Proof.
  intros fx segs M a bs R. pose proof (rdn_length _ _ _ _ _ R) as L. exists (lez bs). split.
  - pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. cbn in B. lia.
  - rewrite R. f_equal. rewrite <- L at 1. symmetry. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
Definition lut_u (k sw : Z) : Z := 4 * Z.shiftr ((2 ^ k * sw) mod 2 ^ 64) 56.
Lemma lut_u_range : forall k sw, 0 <= lut_u k sw <= 1020.
Proof.
  intros k sw. unfold lut_u. pose proof (Z.mod_pos_bound (2 ^ k * sw) (2 ^ 64) ltac:(lia)) as B.
  rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.div_pos ((2 ^ k * sw) mod 2 ^ 64) (2 ^ 56) ltac:(lia) ltac:(lia)).
  assert ((2 ^ k * sw) mod 2 ^ 64 / 2 ^ 56 < 256) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Section Lut.
Context {fx : FPState}.

Lemma zbv_not : forall g, 0 <= g < 2 ^ 64 -> v_xor (Z_to_bv 64 g) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - g).
Proof.
  intros g Hg. unfold v_xor. rewrite u_Z2bv by lia.
  replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by (symmetry; vm_compute; reflexivity).
  rewrite lxor_ones64 by lia. reflexivity.
Qed.

Lemma lut_a0 : forall g sw, 0 <= sw < 2 ^ 32 ->
  alu64 ALU_ADD (Z_to_bv 64 g) (mul_div M_MUL (Z_to_bv 64 4) (alu64 ALU_AND (ext_val false 0 4 (Z_to_bv 64 sw)) (Z_to_bv 64 255))) = Z_to_bv 64 (g + lut_o0 sw).
Proof.
  intros g sw Hsw. rewrite ext_val_zx_id by (rewrite u_Z2bv by lia; cbn; lia). rewrite alu_and, v_and_Z by lia.
  rewrite m_mul, zbv_mul, alu_add, zbv_add. reflexivity.
Qed.

Lemma lut_a12 : forall g sw k, 0 <= sw < 2 ^ 32 -> 0 <= k < 64 ->
  alu64 ALU_ADD (Z_to_bv 64 g) (alu64 ALU_AND (alu64 ALU_SRL (ext_val false 0 4 (Z_to_bv 64 sw)) (Z_to_bv 64 k)) (Z_to_bv 64 1020))
  = Z_to_bv 64 (g + Z.land (Z.shiftr sw k) 1020).
Proof.
  intros g sw k Hsw Hk. rewrite ext_val_zx_id by (rewrite u_Z2bv by lia; cbn; lia). rewrite alu_srl. unfold v_srl. rewrite !u_Z2bv by lia.
  rewrite (Z.mod_small k 64) by lia.
  assert (S : 0 <= Z.shiftr sw k < 2 ^ 64).
  { rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite alu_and, v_and_Z by lia. rewrite alu_add, zbv_add. reflexivity.
Qed.

Lemma lut_a3 : forall g sw, 0 <= sw < 2 ^ 32 ->
  alu64 ALU_ADD (Z_to_bv 64 g) (mul_div M_MUL (Z_to_bv 64 4) (sext 64 (alu32 ALU_SRL (low32 (ext_val false 0 4 (Z_to_bv 64 sw))) (low32 (Z_to_bv 64 24)))))
  = Z_to_bv 64 (g + lut_o3 sw).
Proof.
  intros g sw Hsw. rewrite ext_val_zx_id by (rewrite u_Z2bv by lia; cbn; lia). rewrite w_srlw. unfold v_srlw. rewrite !u_Z2bv by lia.
  change (24 mod 32) with 24. rewrite (bv_wrap_small 32 sw) by (change (bv_modulus 32) with (2 ^ 32); lia).
  assert (S24 : 0 <= Z.shiftr sw 24 < 256).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  rewrite m_mul, zbv_mul, alu_add, zbv_add. reflexivity.
Qed.
Lemma lut_au_off : forall sw k, 0 <= sw < 2 ^ 32 -> 0 <= k ->
  mul_div M_MUL (Z_to_bv 64 4) (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 (2 ^ k)) (ext_val false 0 4 (Z_to_bv 64 sw))) (Z_to_bv 64 56)) = Z_to_bv 64 (lut_u k sw).
Proof.
  intros sw k Hsw Hk. rewrite ext_val_zx_id by (rewrite u_Z2bv by lia; cbn; lia). rewrite m_mul, zbv_mul. rewrite alu_srl. unfold v_srl.
  rewrite (u_Z2bv 56) by lia. change (56 mod 64) with 56. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite ?m_mul, ?zbv_mul. reflexivity.
Qed.
Lemma lut_au : forall g sw k, 0 <= sw < 2 ^ 32 -> 0 <= k ->
  alu64 ALU_ADD (Z_to_bv 64 g) (mul_div M_MUL (Z_to_bv 64 4) (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 (2 ^ k)) (ext_val false 0 4 (Z_to_bv 64 sw))) (Z_to_bv 64 56)))
  = Z_to_bv 64 (g + lut_u k sw).
Proof. intros g sw k Hsw Hk. rewrite lut_au_off by assumption. rewrite alu_add, zbv_add. reflexivity. Qed.
Lemma lut_a3_off : forall sw, 0 <= sw < 2 ^ 32 ->
  mul_div M_MUL (Z_to_bv 64 4) (sext 64 (alu32 ALU_SRL (low32 (ext_val false 0 4 (Z_to_bv 64 sw))) (low32 (Z_to_bv 64 24)))) = Z_to_bv 64 (lut_o3 sw).
Proof.
  intros sw Hsw. rewrite ext_val_zx_id by (rewrite u_Z2bv by lia; cbn; lia). rewrite w_srlw. unfold v_srlw. rewrite !u_Z2bv by lia.
  change (24 mod 32) with 24. rewrite (bv_wrap_small 32 sw) by (change (bv_modulus 32) with (2 ^ 32); lia).
  assert (S24 : 0 <= Z.shiftr sw 24 < 256).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  rewrite ?m_mul, ?zbv_mul. reflexivity.
Qed.

End Lut.
