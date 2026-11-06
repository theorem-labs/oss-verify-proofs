(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "lt"; "land"; "sub"; "add"; "div"; "modulo"; "lxor"; "mul"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "M_DIVU"; "@LinuxProcessSemantics.Riscv.Sem"; "mul_div"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundA Glue3.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma land_mask_down : ltac2:(tb__ "0|5|
S0S0S2S4Z0R2A2M0S4R2Z40M1A2A2S2G0S6R2S5Z2M2G1A2M3A2A2S1S0S7R3S8G3S5G2R4A2M4A2A2S8R3SbR3G4A2A2A3F_;F_;Fx;Fn;").
Proof.
  intros n x Hn Hx.
  assert (E : 2 ^ 64 - 2 ^ n = Z.shiftl (Z.ones (64 - n)) n).
  { rewrite Z.shiftl_mul_pow2, Z.ones_equiv by lia. rewrite Z.mul_pred_l. rewrite <- Z.pow_add_r by lia. replace (64 - n + n) with 64 by lia. lia. }
  rewrite E. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.shiftl_spec by lia.
  assert (Ediff : x - x mod 2 ^ n = Z.shiftl (Z.shiftr x n) n).
  { rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. pose proof (Z.div_mod x (2 ^ n) ltac:(lia)). lia. }
  rewrite Ediff, Z.shiftl_spec by lia.
  destruct (Z_lt_dec i n) as [L|G].
  - rewrite (Z.testbit_neg_r _ (i - n)) by lia. rewrite (Z.testbit_neg_r _ (i - n)) by lia. apply Bool.andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - n + n) with i by lia.
    destruct (Z_lt_dec i 64) as [L64|G64].
    + rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry.
      apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|].
      apply Z.lt_le_trans with (2 ^ 64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land_m4096_id : ltac2:(tb__ "0|1|
S0S2S4Z0M0R1A2S6R1S5Z2Z40A2A2A2S1S0SbR2Z1000A2G0A3S1S0S7R3Zfffffffffffff000A2R3A3F_;F_;Fx;").
Proof. intros x Hx Hm. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite (land_mask_down 12 x) by lia. change (2 ^ 12) with 4096. lia. Qed.

Lemma land_m18_small : ltac2:(tb__ "0|1|
S0S2S4Z0M0R1A2S6R1S5Z2Z12A2A2A2S1S0S7R2Zfffffffffffc0000A2G0A3F_;Fx;").
Proof. intros x Hx. change 18446744073709289472 with (2 ^ 64 - 2 ^ 18). rewrite (land_mask_down 18 x) by lia. rewrite Z.mod_small by lia. lia. Qed.

Lemma land_m18_up : ltac2:(tb__ "0|3|
S0S4Z0R1A2S6S9R2Z3ffffM0A2S5Z2Z40A2A2S1S0S7S9R3G0A2M1Zfffffffffffc0000A2SdSaG1Z40000M2A2G2A2A3F_;F_;Fx;").
Proof.
  intros x Hx Hb. change 18446744073709289472 with (2 ^ 64 - 2 ^ 18). rewrite (land_mask_down 18 (x + 262143)) by lia. change (2 ^ 18) with 262144.
  pose proof (Z.div_mod (x + 262143) 262144 ltac:(lia)). lia.
Qed.

Lemma divu_val : ltac2:(tb__ "0|2|
SfQ40M0A1M1G1S3S1S0SeG0R1A2Z0A3A1S1S0SeG0S11G0S10R3R2A4A2SaSeG0R3A2SeG0R2A2A2A3F_;Fy;Fx;").
Proof.
  intros x y Hy. unfold mul_div.
  destruct (Z.eqb_spec (bv_unsigned y) 0) as [E|E]; [contradiction|]. rewrite bv_divu_unsigned. reflexivity.
Qed.

Lemma lxor_ones64 : ltac2:(tb__ "0|1|
S0S2S4Z0R1A2S6R1S5Z2Z40A2A2A2S1S0ScR2ZffffffffffffffffM0A2S8G0R2A2A3F_;Fx;").
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  assert (E : Z.ones 64 - x = Z.land (Z.lnot x) (Z.ones 64)).
  { rewrite Z.land_ones by lia. unfold Z.lnot. rewrite Z.ones_equiv. change (2 ^ 64) with 18446744073709551616 in *.
    apply (Z.mod_unique_pos _ _ (-1)); lia. }
  rewrite E. apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z_lt_dec i 64) as [L|G].
  - rewrite Z.ones_spec_low by lia. rewrite Bool.andb_true_r. apply Bool.xorb_true_r.
  - rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r, Bool.xorb_false_r.
    destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.testbit_0_l|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
    apply Z.lt_le_trans with (2 ^ 64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
