(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool SpecFloat.
From Flocq.Core Require Import Digits Zaux.
From Flocq.IEEE754 Require Import BinarySingleNaN.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec FPSteps SymExec3Sound.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HFpu.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Definition two23f : Z := 0x4b000000.
Definition neg1f  : Z := 0xbf800000.
Definition two64f : Z := 0x5f800000.

Lemma ieee_2p23 : ieee (2 ^ 23) = two23f.
Proof. vm_compute. reflexivity. Qed.

Lemma decode_neg1 : fp_decode F32 neg1f = S754_finite true 8388608 (-23).
Proof. vm_compute. reflexivity. Qed.
Lemma is_nan_neg1 : fp_is_nan F32 neg1f = false.
Proof. vm_compute. reflexivity. Qed.
Lemma decode_two64 : fp_decode F32 two64f = S754_finite false 8388608 41.
Proof. vm_compute. reflexivity. Qed.
Lemma is_nan_two64 : fp_is_nan F32 two64f = false.
Proof. vm_compute. reflexivity. Qed.

Lemma lt_neg1_val : forall n, 1 <= n < 2 ^ 24 -> fp_lt F32 neg1f (ieee n) = (true, no_flags).
Proof.
  intros n Hn. unfold fp_lt, fp_compare.
  rewrite is_nan_neg1, (is_nan_ieee n Hn), decode_neg1, (decode_ieee n Hn). reflexivity.
Qed.

Lemma lt_two64_val : forall n, 1 <= n < 2 ^ 24 -> fp_lt F32 (ieee n) two64f = (true, no_flags).
Proof.
  intros n Hn. unfold fp_lt, fp_compare.
  rewrite is_nan_two64, (is_nan_ieee n Hn), decode_two64, (decode_ieee n Hn). cbn [orb SFcompare].
  pose proof (fexpo_bounds n Hn) as He.
  rewrite (proj2 (Z.compare_lt_iff (fexpo n) 41)) by lia. reflexivity.
Qed.

Lemma lt_two23_val : forall n, 1 <= n < 2 ^ 24 -> fp_lt F32 (ieee n) two23f = ((n <? 2 ^ 23), no_flags).
Proof. intros n Hn. rewrite <- ieee_2p23. apply lt_val; lia. Qed.

Lemma of_int_val_gen : forall md (sgn : bool) bits n, 1 <= n < 2 ^ 24 -> 32 <= bits ->
  fp_of_int F32 md sgn bits n = (ieee n, no_flags).
Proof.
  intros md sgn bits n Hn Hb.
  transitivity (fp_of_int F32 md false 64 n); [| apply of_int_val; exact Hn].
  unfold fp_of_int, int_wrap. rewrite !Z.land_ones by lia.
  assert (H2 : 2 ^ 24 <= 2 ^ (bits - 1)) by (apply Z.pow_le_mono_r; lia).
  assert (H3 : 2 ^ (bits - 1) <= 2 ^ bits) by (apply Z.pow_le_mono_r; lia).
  rewrite !Z.mod_small by lia.
  rewrite (testbit_high_false n (bits - 1)) by lia. rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma bit31_small : forall a, 0 <= a < 2 ^ 31 -> bit 31 (Z_to_bv 32 a) = false.
Proof.
  intros a Ha. unfold bit. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  apply testbit_high_false; lia.
Qed.

Lemma sgnj_val_pos : forall op a b, 0 <= a < 2 ^ 31 -> 0 <= b < 2 ^ 31 -> op <> F_SGNJN ->
  sgnj_val op (Z_to_bv 32 a) (Z_to_bv 32 b) = Z_to_bv 32 a.
Proof.
  intros op a b Ha Hb Hop. unfold sgnj_val. change (32 - 1)%N with 31%N.
  rewrite (bit31_small a Ha), (bit31_small b Hb).
  replace (match op with F_SGNJ => false | F_SGNJN => negb false | F_SGNJX => xorb false false end) with false
    by (destruct op; [reflexivity | exfalso; exact (Hop eq_refl) | reflexivity]).
  apply bv_eq. rewrite bv_concat_unsigned by reflexivity.
  rewrite bv_extract_unsigned, !Z_to_bv_unsigned. change (Z.of_N 0) with 0. change (Z.of_N 31) with 31.
  rewrite Z.shiftr_0_r, Z.shiftl_0_l, Z.lor_0_l. rewrite !bv_wrap_small by (unfold bv_modulus; rewrite ?bv_wrap_small by (unfold bv_modulus; lia); lia). reflexivity.
Qed.

Lemma low32_val : forall c, low32 (Z_to_bv 64 c) = Z_to_bv 32 (c mod 2 ^ 32).
Proof.
  intros c. apply bv_eq. unfold low32. rewrite bv_extract_unsigned, !Z_to_bv_unsigned.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap.
  change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 32 * 2 ^ 32).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_mod by lia. reflexivity.
Qed.

Lemma sext64_w_small : forall n, 0 <= n < 2 ^ 31 -> sext 64 (Z_to_bv 32 n) = Z_to_bv 64 n.
Proof.
  intros n Hn. rewrite (SX2S.sext64_small 32 n) by (cbn; lia). f_equal.
  unfold bv_swrap. unfold bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Open Scope bv_scope.

Lemma hp_step_fsgnj_s : forall (fx : FPState) segs regs pc mem rom w op rd rs1 rs2 a b,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fsgnj op FMT_S rd rs1 rs2, 4%Z) ->
  fholds fx rs1 a -> fholds fx rs2 b -> (0 <= a < 2 ^ 31)%Z -> (0 <= b < 2 ^ 31)%Z -> op <> F_SGNJN ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (Z_to_bv 32 a)) (@fp_regs fx)) (@fp_csr fx))
               regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w op rd rs1 rs2 a b Hf He Hd Ha Hb Har Hbr Hop.
  destruct fx as [fr cs]. unfold fholds in Ha, Hb. cbn [fp_csr fp_regs] in *.
  fp_pipeline Hf He Hd. cbn [fp_regs fp_csr].
  rewrite Ha, Hb, !unbox_nan_box.
  rewrite (sgnj_val_pos op a b Har Hbr Hop). rewrite b_npc4. reflexivity.
Qed.

Lemma hp_step_fmv_w_x : forall (fx : FPState) segs regs pc mem rom w rd rs1 c,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fmv FMV_F_X FMT_S rd rs1, 4%Z) ->
  getr regs rs1 = Z_to_bv 64 c ->
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (Z_to_bv 32 (c mod 2 ^ 32))) (@fp_regs fx)) (@fp_csr fx))
               regs (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd rs1 c Hf He Hd Hr.
  rewrite (fp_step_fmv_w_x fx segs regs pc mem rom w rd rs1 Hf He Hd). rewrite Hr, low32_val. reflexivity.
Qed.
