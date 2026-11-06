(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import SFModel Arr FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Import Prelim SoftFloat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require FloatScan.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Import FloatScan FloatScanProps.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require FloatScan_nn.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec.FloatScan_nn.FloatScan_split.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require F_scan_calls.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require Import F_scan_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Ltac show_goal := match goal with |- ?g => idtac g end.
(* [comment removed for export] *)
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.
Ltac mlia2 := rewrite ?land_W64 in *; Z.div_mod_to_equations; lia.
(* [comment removed for export] *)
Ltac decb := repeat match goal with
  | |- context [Z.ltb ?a ?b] => first [replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; mlia2) | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; mlia2)]
  | |- context [Z.leb ?a ?b] => first [replace (Z.leb a b) with true by (symmetry; apply Z.leb_le; mlia2) | replace (Z.leb a b) with false by (symmetry; apply Z.leb_gt; mlia2)]
  | |- context [Z.eqb ?a ?b] => first [replace (Z.eqb a b) with true by (symmetry; apply Z.eqb_eq; mlia2) | replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; mlia2)]
  end.

(* [comment removed for export] *)
Lemma sx32_M64 : sx32 (Z_to_bv 64 18446744073709551615) = Z_to_bv 64 18446744073709551615.
Proof. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit by lia. vm_compute. reflexivity. Qed.
Lemma zx32_lit : forall z, (0 <= z < 2^32)%Z -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bv_lts_lit : forall a e, (-2^63 <= a < 2^63)%Z -> (-2^63 <= e < 2^63)%Z -> bv_lts (Z_to_bv 64 a) (Z_to_bv 64 e) = (a <? e)%Z.
Proof. intros a e Ha He. unfold bv_lts. rewrite !signed_of_Z by lia. reflexivity. Qed.
Lemma swrap32_land64_add : forall e k, (-2^31 <= e + k < 2^31)%Z -> (-2^31 <= k < 2^31)%Z ->
  bv_swrap 32 (Z.land e 18446744073709551615 + k) = (e + k)%Z.
Proof. intros e k H1 H2. rewrite land_W64, swrap32_eq. Z.div_mod_to_equations. lia. Qed.
Lemma swrap32_shift : forall x k k', (k' = k - 2^64)%Z -> bv_swrap 32 (x + k) = bv_swrap 32 (x + k').
Proof. intros x k k' ->. rewrite !swrap32_eq. f_equal. replace (x + (k - 2^64) + 2147483648)%Z with (x + k + 2147483648 + (- 4294967296) * 4294967296)%Z by lia. rewrite Z.mod_add by lia. reflexivity. Qed.
Lemma swrap32_shift_sub : forall x k k', (k' = 2^64 - k)%Z -> bv_swrap 32 (x - k) = bv_swrap 32 (x + k').
Proof. intros x k k' ->. rewrite !swrap32_eq. f_equal. replace (x + (2^64 - k) + 2147483648)%Z with (x - k + 2147483648 + 4294967296 * 4294967296)%Z by lia. rewrite Z.mod_add by lia. reflexivity. Qed.
Lemma swrap32_landW : forall a c, bv_swrap 32 (Z.land a 18446744073709551615 + c) = bv_swrap 32 (a + c).
Proof.
  intros a c. rewrite land_W64, !swrap32_eq. f_equal.
  rewrite (Z.mod_eq a (2^64)) by lia.
  replace (a - 2 ^ 64 * (a / 2 ^ 64) + c + 2147483648)%Z with ((a + c + 2147483648) + (- (a / 2 ^ 64) * 4294967296) * 4294967296)%Z by lia.
  apply Z.mod_add. lia.
Qed.
Lemma swrap32_landW_sub : forall a c, bv_swrap 32 (Z.land a 18446744073709551615 - c) = bv_swrap 32 (a - c).
Proof. intros a c. rewrite <- !Z.add_opp_r. apply swrap32_landW. Qed.
Lemma swrap32_swrap32_add : forall e k, bv_swrap 32 (Z.land (bv_swrap 32 e) 18446744073709551615 + k) = bv_swrap 32 (e + k).
Proof.
  intros e k. rewrite swrap32_landW. rewrite !swrap32_eq.
  Z.div_mod_to_equations. lia.
Qed.
Lemma bv_lts_0_lit : forall e, (-2^63 <= e < 2^63)%Z -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 e) = (0 <? e)%Z.
Proof. intros e He. unfold bv_lts. rewrite !signed_of_Z by lia. reflexivity. Qed.
Ltac brs K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
  repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
  first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac]; try (exfalso; lia).
Lemma swrap32_land64_small : forall e, (-2^31 <= e < 2^31)%Z -> bv_swrap 32 (Z.land e 18446744073709551615) = e.
Proof. intros e He. rewrite land_W64, swrap32_eq. Z.div_mod_to_equations; lia. Qed.
Ltac fixw2 := rewrite ?swrap32_landW, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
Ltac fixw :=
  try match goal with |- context [bv_swrap 32 (?x + ?k)] =>
        lazymatch isZcst k with true => idtac end;
        first [ assert_succeeds (assert (2^63 <= k)%Z by lia);
                let k' := eval vm_compute in (k - 2^64)%Z in rewrite (swrap32_shift x k k') by reflexivity
              | idtac ] end;
  try match goal with |- context [bv_swrap 32 (?x - ?k)] =>
        lazymatch isZcst k with true => idtac end;
        first [ assert_succeeds (assert (2^63 <= k)%Z by lia);
                let k' := eval vm_compute in (2^64 - k)%Z in rewrite (swrap32_shift_sub x k k') by reflexivity
              | idtac ] end;
  try rewrite swrap32_land64_add by lia; try rewrite swrap32_land64_small by lia; try rewrite swrap32_small by lia.

(* [comment removed for export] *)
Lemma f128_le_range : forall a b, (-1 <= f128_le a b <= 1)%Z.
Proof.
intros a b. unfold f128_le.
repeat (lazymatch goal with |- context [if ?c then _ else _] => destruct c | _ => fail end; try (cbn; lia)).
unfold nez64, b2z. destruct (negb _); cbn; lia.
Qed.
Lemma fpclass_not_nan : forall y, Z.land (Z.shiftr (hi64 y) 48) 0x7fff <> 0x7fff%Z -> (m_fpclassifyl y =? 0) = false.
Proof.
intros y H. unfold m_fpclassifyl.
destruct (Z.land (Z.shiftr (hi64 y) 48) 0x7fff =? 0); [destruct (nz _); reflexivity|].
replace (Z.land (Z.shiftr (hi64 y) 48) 32767 =? 32767) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity.
Qed.
Lemma fpclass_nan : forall y, Z.land (Z.shiftr (hi64 y) 48) 0x7fff = 0x7fff%Z ->
(m_fpclassifyl y =? 0) = nz (Z.lor (lo64 y) (Z.land (hi64 y) 0x0000ffffffffffff)).
Proof.
intros y H. unfold m_fpclassifyl. rewrite H. cbn [Z.eqb]. destruct (nz _); reflexivity.
Qed.
Lemma land_pow2_bit : forall a n, (0 <= n)%Z -> Z.land a (2^n) = (if Z.testbit a n then 2^n else 0)%Z.
Proof.
  intros a n Hn. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec n i).
  - subst i. destruct (Z.testbit a n); [rewrite Z.pow2_bits_true by lia | rewrite Z.bits_0]; reflexivity.
  - rewrite Bool.andb_false_r. destruct (Z.testbit a n); [rewrite Z.pow2_bits_false by lia | rewrite Z.bits_0]; reflexivity.
Qed.
Lemma zbv_u64 : forall v, Z_to_bv 64 (u64 v) = Z_to_bv 64 v.
Proof. intros. apply Z_to_bv_eqm. unfold u64. apply Z.mod_mod. lia. Qed.
Lemma shl48_land64 : forall v, Z.land (Z.shiftl v 48) 18446744073709551615 = Z.shiftl (Z.land v 65535) 48.
Proof.
  intros v. change 18446744073709551615%Z with (Z.ones 64). change 65535%Z with (Z.ones 16).
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.shiftl_spec, Z.land_spec by lia.
  destruct (Z.lt_ge_cases (i - 48) 0) as [Hn|Hn].
  - rewrite !(Z.testbit_neg_r _ (i - 48)) by lia. reflexivity.
  - rewrite !Z.testbit_ones_nonneg by lia.
    destruct (Z.ltb_spec0 i 64); destruct (Z.ltb_spec0 (i - 48) 16); try lia; rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; reflexivity.
Qed.
Lemma pack_hi_range : forall xhi v, (0 <= Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land v 65535) 48) < 2^64)%Z.
Proof.
  intros xhi v. apply Bytes.lor_lt_pow2.
  - pose proof (land48_range xhi). change 0x0000ffffffffffff%Z with 281474976710655%Z in H. lia.
  - rewrite Z.shiftl_mul_pow2 by lia.
    assert (0 <= Z.land v 65535 < 2^16)%Z.
    { split; [apply Z.land_nonneg; right; lia|].
      apply PropExec.Z_bounded_by_bits; [lia | apply Z.land_nonneg; right; lia |].
      intros k Hk. rewrite Z.land_spec. replace 65535%Z with (Z.ones 16) by reflexivity.
      rewrite Z.testbit_ones_nonneg by lia. destruct (Z.ltb_spec0 k 16); [lia|]. apply Bool.andb_false_r. }
    change (2^64)%Z with (2^16 * 2^48)%Z. nia.
Qed.
Lemma pack_eq : forall xhi xlo v, (0 <= xlo < 2^64)%Z ->
  Z_to_bv 64 (Z.lor (Z.land (Z.shiftl v 48) 18446744073709551615) (Z.land xhi 281474976710655))
  = Z_to_bv 64 (hi64 (mk128 (Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land v 65535) 48)) xlo))
  /\ Z_to_bv 64 xlo = Z_to_bv 64 (lo64 (mk128 (Z.lor (Z.land xhi 281474976710655) (Z.shiftl (Z.land v 65535) 48)) xlo)).
Proof.
  intros xhi xlo v Hxlo. pose proof (pack_hi_range xhi v).
  rewrite hi64_mk128, lo64_mk128 by lia. split; [|reflexivity].
  rewrite shl48_land64, Z.lor_comm. reflexivity.
Qed.
Lemma sbb_bridge : forall xhi xlo yhi ylo, (0 <= xhi < 2^64)%Z -> (0 <= xlo < 2^64)%Z -> (0 <= yhi < 2^64)%Z -> (0 <= ylo < 2^64)%Z ->
  let hi' := (if xlo <? ylo then u64 (u64 (xhi - yhi) - 1) else u64 (xhi - yhi))%Z in
  Z.land (Z.land (xhi - yhi) 18446744073709551615 - Z.b2z (xlo <? ylo)%Z) 18446744073709551615 = hi'
  /\ Z_to_bv 64 (Z.land (xhi - yhi) 18446744073709551615 - Z.b2z (xlo <? ylo)%Z) = Z_to_bv 64 hi'
  /\ (0 <= hi' < 2^64)%Z /\ u64 (xlo - ylo) = Z.land (xlo - ylo) 18446744073709551615.
Proof.
  intros xhi xlo yhi ylo Rxh Rxl Ryh Ryl. cbv zeta. rewrite !land_W64. unfold u64.
  destruct (Z.ltb_spec0 xlo ylo); cbn [Z.b2z].
  - split; [reflexivity|]. split; [apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; reflexivity|].
    split; [apply Z.mod_pos_bound; lia | reflexivity].
  - rewrite Z.sub_0_r, Z.mod_mod by lia. split; [reflexivity|]. split; [reflexivity|].
    split; [apply Z.mod_pos_bound; lia | reflexivity].
Qed.
Lemma shr63_eqb : forall h, (0 <= h < 2^64)%Z -> (Z.shiftr h 63 =? 0) = (h <? 2^63)%Z.
Proof.
  intros h Hh. rewrite Z.shiftr_div_pow2 by lia.
  destruct (Z.ltb_spec0 h (2^63)).
  - rewrite Z.div_small by lia. reflexivity.
  - apply Z.eqb_neq. intros E. assert (h / 2^63 >= 1)%Z by (apply Z.le_ge, Z.div_le_lower_bound; lia). lia.
Qed.
Lemma shr48_range : forall h, (0 <= h < 2^64)%Z -> (0 <= Z.shiftr h 48 < 65536)%Z.
Proof. intros h Hh. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma land63_range : forall x, (0 <= x < 2^64)%Z -> (0 <= Z.land x 0x7fffffffffffffff < 2^64)%Z.
Proof. intros x Hx. apply Bytes.land_lt_pow2; lia. Qed.
Lemma testbit_small_high : forall x k i, (0 <= x < 2^k)%Z -> (0 <= k <= i)%Z -> Z.testbit x i = false.
Proof.
  intros x k i Hx Hk. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lor_low_high : forall x y k, (0 <= x < 2^k)%Z -> (0 <= y)%Z -> (0 <= k)%Z -> Z.lor x (y * 2^k) = (x + y * 2^k)%Z.
Proof.
  intros x y k Hx Hy Hk. apply lor_disjoint_add.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k).
  - rewrite Z.mul_pow2_bits_low by lia. apply Bool.andb_false_r.
  - rewrite (testbit_small_high x k i) by lia. reflexivity.
Qed.
Lemma land_highmask : forall x k, (0 <= x < 2^64)%Z -> (0 <= k < 64)%Z ->
  Z.land x (2^64 - 2^k) = (x - x mod 2^k)%Z.
Proof.
  intros x k Hx Hk. rewrite <- (zb_shr_shl x k) by lia.
  replace (2^64 - 2^k)%Z with (Z.shiftl (Z.ones (64 - k)) k).
  2:{ rewrite Z.shiftl_mul_pow2, Z.ones_equiv by lia. rewrite Z.mul_pred_l, <- Z.pow_add_r by lia. replace (64 - k + k)%Z with 64%Z by lia. lia. }
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i k).
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - k + k)%Z with i by lia.
    destruct (Z.lt_ge_cases i 64).
    + rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry. apply (testbit_small_high x 64 i); lia.
Qed.
Lemma land_bit63 : forall x, (0 <= x < 2^64)%Z -> Z.land x 9223372036854775808 = (x - x mod 2^63)%Z.
Proof. intros x Hx. change 9223372036854775808%Z with (2^64 - 2^63)%Z. apply land_highmask; lia. Qed.
Lemma land_m63 : forall x, Z.land x 9223372036854775807 = (x mod 2^63)%Z.
Proof. intros. change 9223372036854775807%Z with (2^63 - 1)%Z. apply zb_land_mask. lia. Qed.
Lemma land_m48 : forall x, Z.land x 281474976710655 = (x mod 2^48)%Z.
Proof. intros. change 281474976710655%Z with (2^48 - 1)%Z. apply zb_land_mask. lia. Qed.
Lemma land_m16 : forall x, Z.land x 65535 = (x mod 2^16)%Z.
Proof. intros. change 65535%Z with (2^16 - 1)%Z. apply zb_land_mask. lia. Qed.
