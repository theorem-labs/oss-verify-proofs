(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia Bool Reals.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM00 YM01 YM02.
Unset Lia Cache. Unset Nia Cache.
Local Abbreviation D := fmt_double.
Local Abbreviation S := fmt_single.
Local Open Scope Z_scope.
Lemma unsigned_Z_to_bv64 v : 0 <= v < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 v) = v.
Proof. intros H. apply Z_to_bv_small. exact H. Qed.
Lemma unsigned_Z_to_bv32 v : 0 <= v < 2 ^ 32 -> bv_unsigned (Z_to_bv 32 v) = v.
Proof. intros H. apply Z_to_bv_small. exact H. Qed.
Lemma word_range (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. apply (bv_unsigned_in_range 64 w). Qed.
Lemma bv32_range (x : bv 32) : 0 <= bv_unsigned x < 2 ^ 32.
Proof. apply (bv_unsigned_in_range 32 x). Qed.







Lemma testbit_small a n m : 0 <= a < 2 ^ n -> 0 <= n <= m -> Z.testbit a m = false.
Proof.
intros Ha Hm. apply (proj2 (Z.testbit_false a m ltac:(lia))).
rewrite Z.div_small; [reflexivity|]. split; [lia|].
apply Z.lt_le_trans with (2 ^ n); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma nan_box_unsigned (x : bv 32) :
bv_unsigned (nan_box x) = (2 ^ 32 - 1) * 2 ^ 32 + bv_unsigned x.
Proof.
unfold nan_box. rewrite bv_concat_unsigned by reflexivity.
pose proof (bv32_range x) as Hx.
change (bv_unsigned (Z_to_bv 32 (-1))) with (2 ^ 32 - 1).
rewrite Z.shiftl_mul_pow2 by lia. change (Z.of_N 32) with 32.
assert (H : Z.land ((2 ^ 32 - 1) * 2 ^ 32) (bv_unsigned x) = 0).
{ apply Z.bits_inj'; intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.ltb_spec n 32).
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- rewrite (testbit_small (bv_unsigned x) 32 n) by lia. apply Bool.andb_false_r. }
rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H.
Qed.
Lemma low32_nan_box (x : bv 32) : low32 (nan_box x) = x.
Proof.
apply bv_eq. unfold low32. rewrite bv_extract_unsigned, nan_box_unsigned.
change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
pose proof (bv32_range x). unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma high32_nan_box (x : bv 32) : bv_unsigned (bv_extract 32 32 (nan_box x)) = Z.ones 32.
Proof.
rewrite bv_extract_unsigned, nan_box_unsigned. change (Z.of_N 32) with 32.
pose proof (bv32_range x). rewrite Z.shiftr_div_pow2 by lia.
rewrite Z.add_comm, Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Theorem unbox_nan_box (x : bv 32) : unbox_s (nan_box x) = x.
Proof. unfold unbox_s. rewrite high32_nan_box. cbn [Z.eqb Z.ones]. apply low32_nan_box. Qed.
Theorem unsigned_unbox_nan_box v :
0 <= v < 2 ^ 32 -> bv_unsigned (unbox_s (nan_box (Z_to_bv 32 v))) = v.
Proof. intros H. rewrite unbox_nan_box. apply unsigned_Z_to_bv32. exact H. Qed.





Section d.
Context {n : N}.
Hypothesis Hn : (0 < n)%N.
Let k : Z := Z.of_N n - 1.
Lemma sgnj_val_unsigned op (a b : bv n) :
bv_unsigned (sgnj_val op a b) =
Z.lor (Z.shiftl (if (match op with
| F_SGNJ => bit (n - 1) b
| F_SGNJN => negb (bit (n - 1) b)
| F_SGNJX => xorb (bit (n - 1) a) (bit (n - 1) b)
end) then 1 else 0) k)
(bv_unsigned a mod 2 ^ k).
Proof.
unfold sgnj_val. rewrite bv_concat_unsigned by lia.
unfold bv_wrap, bv_modulus. replace (Z.of_N (n - 1)) with k by (unfold k; lia).
f_equal. f_equal. destruct (match op with F_SGNJ => _ | _ => _ end); reflexivity.
rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
unfold bv_wrap, bv_modulus. f_equal. f_equal. unfold k. lia.
Qed.
Lemma bit_top (a : bv n) : bit (n - 1) a = Z.testbit (bv_unsigned a) k.
Proof. unfold bit. f_equal. unfold k. lia. Qed.
Lemma k_nonneg : 0 <= k.
Proof. unfold k. lia. Qed.
Lemma testbit_above (a : bv n) m : k < m -> Z.testbit (bv_unsigned a) m = false.
Proof.
intros Hm. pose proof (bv_unsigned_in_range n a) as Ha. unfold bv_modulus in Ha.
apply (testbit_small _ (Z.of_N n)); unfold k in Hm; lia.
Qed.
Theorem sgnj_same (a : bv n) : sgnj_val F_SGNJ a a = a.
Proof.
apply bv_eq. rewrite sgnj_val_unsigned, bit_top. pose proof k_nonneg.
apply Z.bits_inj'. intros m Hm.
rewrite Z.lor_spec, Z.shiftl_spec by lia.
destruct (Z.lt_trichotomy m k) as [Hlt|[->|Hgt]].
- rewrite Z.mod_pow2_bits_low by lia. rewrite (Z.testbit_neg_r _ (m - k)) by lia. reflexivity.
- rewrite Z.sub_diag, Z.mod_pow2_bits_high by lia.
destruct (Z.testbit (bv_unsigned a) k); reflexivity.
- rewrite Z.mod_pow2_bits_high by lia. rewrite (testbit_above a m) by lia.
destruct (Z.testbit (bv_unsigned a) k); [rewrite Z.bits_above_log2|rewrite Z.bits_0]; try reflexivity; cbn; lia.
Qed.
Theorem sgnjx_same (a : bv n) : bv_unsigned (sgnj_val F_SGNJX a a) = bv_unsigned a mod 2 ^ k.
Proof.
rewrite sgnj_val_unsigned, Bool.xorb_nilpotent. rewrite Z.shiftl_0_l. apply Z.lor_0_l.
Qed.

End d.
Theorem fabs_d_word (a : word) : sgnj_val F_SGNJX a a = Z_to_bv 64 (fp_abs D (bv_unsigned a)).
Proof.
apply bv_eq. rewrite (@sgnjx_same 64 eq_refl a). rewrite fp_abs_D.
change (Z.of_N 64 - 1) with 63. symmetry. apply unsigned_Z_to_bv64.
pose proof (Z.mod_pos_bound (bv_unsigned a) (2 ^ 63) ltac:(lia)). lia.
Qed.

Theorem fmv_d_word (a : word) : sgnj_val F_SGNJ a a = a.
Proof. apply sgnj_same. reflexivity. Qed.

Theorem dexp_field_word (a : word) :
((bv_unsigned a * 2) mod 2 ^ 64) / 2 ^ 53 = fp_exp_field D (bv_unsigned a).
Proof. apply dexp_field_asm. apply word_range. Qed.
Theorem dval_pos_signed (a : word) r :
dval (bv_unsigned a) r -> (0 < r)%R -> 0 <= bv_signed a.
Proof.
intros Ha Hr. destruct (dval_pos_bits (bv_unsigned a) r Ha Hr (word_range a)) as [Hlt _].
unfold bv_signed. rewrite bv_swrap_small; [apply word_range|].
pose proof (word_range a). unfold bv_half_modulus, bv_modulus. cbn -[Z.lt Z.le Z.opp bv_unsigned] in *. lia.
Qed.
