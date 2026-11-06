(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_nn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_frexpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
Module F_rscan_lib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_frexpl.F_fmt_fp_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


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


End CeilWrap.
(* [comment removed for export] *)
Ltac show_goal := match goal with |- ?g => idtac g end.
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.
Ltac mlia2 := rewrite ?land_W64 in *; Z.div_mod_to_equations; lia.
Ltac decb := repeat match goal with
  | |- context [Z.ltb ?a ?b] => first [replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; mlia2) | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; mlia2)]
  | |- context [Z.leb ?a ?b] => first [replace (Z.leb a b) with true by (symmetry; apply Z.leb_le; mlia2) | replace (Z.leb a b) with false by (symmetry; apply Z.leb_gt; mlia2)]
  | |- context [Z.eqb ?a ?b] => first [replace (Z.eqb a b) with true by (symmetry; apply Z.eqb_eq; mlia2) | replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; mlia2)]
  end.
Ltac brs K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
  repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
  first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac]; try (exfalso; lia).
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
End F_rscan_lib.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_memchr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_shgetc_proofs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_mem4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_str3.
Module F_shgetc_proofs2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_musl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_frexpl.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_proofs.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_proofs.F_shgetc.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_mem4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_str3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_proofs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition uflow_postA (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p off : Z) (txt : list Z) (shend : Z) (shl shc canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (uflow_res txt off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(q - 2432, q); (Fp, Fp + 232)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' (q - 2432) (q)
    /\ rw_cells bsegs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) (Z_to_bv 64 M64) (T + p) shend shl shc)
    /\ bytes_at bsegs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition uflow_stmtA : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p off rpos rend shend : Z) (txt pre post : list Z) (mode shl shc canary : word),
  rw_cells bsegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
  (mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
  rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
  bytes_at bsegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk bsegs m (q - UFLOW_XD) (q) -> (4096 <= q - UFLOW_XD)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - UFLOW_XD \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - UFLOW_XD)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  MRT m -> (alloc_ceiling + 64 <= q - UFLOW_XD)%Z -> (q + 64 <= 2^47 - 1)%Z ->
  app_range T (zlength txt) -> shadow_ok m T (p + 1) ->
  evt bsegs (uflow_postA ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p off txt shend shl shc canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 UFLOW) fc None m (seg_rom bsegs)).

Lemma uflow_spec : uflow_stmtA.
Proof.
  unfold uflow_stmtA. intros until canary. intros FC Hmode TXT Hp Hoff BY [SSP1 SSP2] T0 T1 Rrp Rre Rsh SEP3 ST SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1 MI.
  intros MR CEIL Q47 ART SOT.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. pose proof AINTRIN_STACK_val as AIS. unfold UFLOW_XD in *.
  pose proof (munch_refl [(q - 2432, q); (Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof TXT as TXT'. destruct TXT' as (Htxt & NZ & BYT & AL & L256).
  pose proof (rw_cells_bound _ _ _ _ FC) as B. cbn [cells_size csize Nat.add ss_cells] in B.
  assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length.
  unfold UFLOW, got_ssp, ssp_guard, M64 in *. unfold zlength in *. pose_word_ranges.
  pose proof (app_range_lt47 _ _ ART) as TB.
  assert (WAPP : Forall app_iv [(q - 2432, q); (Fp, Fp + 232)]%Z).
  { apply Forall_cons; [apply app_iv_stack; lia|]. apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil]. }
  assert (WMRT : Forall mrt_iv_ok [(q - 2432, q); (Fp, Fp + 232)]%Z).
  { apply Forall_cons; [apply mrt_iv_ok_stack; lia|]. apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil]. }
  zs. carve_frame 64%nat ST.
  do 6 zs.
  zs. zs. zs. zs. zs.
  pose proof toread_spec as TRS. unfold toread_stmt in TRS.
  destruct (stk_split _ _ _ (q - 80)%Z _ ST ltac:(lia)) as [ST1 ST2].
  assert (LT3 : length txt = (length pre + S (length post))%nat) by (rewrite Htxt, length_app; reflexivity).
  zs. callw (eapply TRS; [hyp | exact Hmode | lia | lia | lia | lia | lia | replace (q + -64 - 16)%Z with (q - 80)%Z by lia; exact ST2 | lia | lia | lia | lia | lia | hyp]).
  rename POST into FC1. rename PC into ST2. replace (q + -64 - 16)%Z with (q - 80)%Z in ST2 by lia. unfold ss_cells, w0, STRING_READ in FC1.
  (* [comment removed for export] *)
  lazymatch goal with FR' : rw_cells _ ?mc (q + -64)%Z (CB 16 ?bs :: ?rest) |- _ =>
    pose proof (rw_cells_split_CB bsegs mc (q + -64)%Z [] 16 bs rest [15; 1]%nat FR' eq_refl) as FR2; clear FR'; cbn [mk_CB_cells app] in FR2;
    pose proof (proj1 (F_fwritex.rw_cells_app bsegs mc (q + -64)%Z [_] _) FR2) as [J15 FR3]; clear FR2;
    pose proof (proj1 (F_fwritex.rw_cells_app bsegs mc _ [_] _) FR3) as [DC0 FR]; clear FR3 end.
  cbn [cells_size csize Nat.add] in DC0, FR.
  lazymatch type of DC0 with rw_cells _ _ ?a _ => replace a with (q + -49)%Z in DC0 by lia end.
  lazymatch type of FR with rw_cells _ _ ?a _ => replace a with (q + -48)%Z in FR by lia end.
  destruct (rw_cells_CB1 _ _ _ DC0) as [dj DC]. clear DC0.
  zs. zs. br K0.
  zs. zs. zs. zs. zs.
  pose proof (stk_merge _ _ _ _ _ ST1 ST2 ltac:(lia)) as ST3. clear ST1 ST2.
  pose proof sread_spec as SRS. unfold sread_stmtA, STRING_READ, SREAD_XD in SRS.
  zs. replace (ret_pc (Z_to_bv 64 631612)) with (Z_to_bv 64 631612) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MR1 : MRT mm) by (eapply MRT_munch; [exact MR| exact MU| exact WMRT]);
    assert (SOT1 : shadow_ok mm T (p + 1)) by (eapply shadow_ok_munch_app; [exact SOT| exact MU| lia| eapply app_range_sub; [exact ART| lia| lia| lia]| exact WAPP]);
    assert (SOD1 : shadow_ok mm (q + -49) 1) by (destruct MR1 as (_ & SZ & _); apply (stack_shadow_zero_shadow_ok _ _ _ SZ); lia)
  end.
  callw (eapply SRS with (off := off) (pre := pre) (post := post);
    [unfold ss_cells, w0; hyp | exact TXT | exact Hp | exact Hoff | hyp | replace (q + -64 + 15)%Z with (q + -49)%Z by lia; exact DC | lia | lia | lia | lia | lia
    | lia | unfold zlength; lia | unfold zlength; lia
    | replace (q + -64 - 2368)%Z with (q - 2432)%Z by lia; exact ST3 | lia | lia | lia | lia | lia | unfold zlength; lia | lia | lia | hyp
    | exact MR1 | lia | lia | unfold zlength; exact ART | exact SOT1
    | right; unfold highmem_range, KHIGHMEM_BEG, KHIGHMEM_END; lia | apply wr_range_ok_high; lia | exact SOD1 ]).
  clear MR1 SOT1 SOD1.
  rename PC into ST. replace (q + -64 - 2368)%Z with (q - 2432)%Z in ST by lia. rename PC1 into DC2. rename POST into BY3. rename PC0 into FC2.
  assert (Rch : (0 <= znth txt off < 256)%Z).
  { destruct (Z.lt_ge_cases off (Z.of_nat (length txt))).
    - apply (proj1 (Forall_forall _ _) BYT). apply Shgetc_lemmas.znth_In'. unfold zlength. lia.
    - rewrite znth_ge by (unfold zlength; lia). lia. }
  unfold sread_len, uflow_res in *. destruct (Z.ltb_spec0 off p).
  - zs. br K1. zs. cbv beta. rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt off)) by lia.
    do 3 zs. br K2; try (exfalso; apply K2; reflexivity).
    do 8 zs.
    release_frame J15 ST (q + -49)%Z. release_frame DC2 ST (q + -48)%Z. release_frame FR ST q.
    apply evt_done. unfold uflow_postA, uflow_res, sread_len, UFLOW_XD. replace (off <? p) with true by (symmetry; apply Z.ltb_lt; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [hyp|]. split; [exact ST|].
    split; [exact FC2|]. split; [exact BY3|]. split; [exact SSP1 | exact SSP2].
  - zs. br K1.
    do 3 zs. br K2; try (exfalso; apply K2; reflexivity).
    do 8 zs.
    release_frame J15 ST (q + -49)%Z. release_frame DC2 ST (q + -48)%Z. release_frame FR ST q.
    apply evt_done. unfold uflow_postA, uflow_res, sread_len, UFLOW_XD. replace (off <? p) with false by (symmetry; apply Z.ltb_ge; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [hyp|]. split; [exact ST|].
    split; [exact FC2|]. split; [exact BY3|]. split; [exact SSP1 | exact SSP2].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.
End F_shgetc_proofs2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module F_shgetc_proofs3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_musl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_frexpl.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_proofs.F_shgetc_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_proofs.F_shgetc.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_mem4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_str3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_proofs F_shgetc_proofs2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shgetc_postA (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p : Z) (f : shfile) (txt : list Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (sh_getc f))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(q - 2464, q); (Fp, Fp + 232)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' (q - 2464) q
    /\ rw_cells bsegs m' Fp (rf_cells T p true (snd (sh_getc f)) ssJ)
    /\ bytes_at bsegs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition shgetc_stmtA : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (f : shfile) (txt pre post : list Z) (canary : word),
  rw_cells bsegs m Fp (rf_cells T p w f ssJ) ->
  sh_stdio f = true -> sh_n f = p -> sh_buf f = txt ->
  sh_rpos f = (if w then p else 0%Z) -> (w = false -> sh_cnt0 f = 0%Z /\ sh_shlim_neg f = false) -> (0 <= sh_cnt0 f <= sh_rpos f)%Z ->
  rtext T txt pre post -> p = zlength pre -> bytes_at bsegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk bsegs m (q - SHGETC_XD) q -> (4096 <= q - SHGETC_XD)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - SHGETC_XD \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - SHGETC_XD)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  MRT m -> (alloc_ceiling + 64 <= q - SHGETC_XD)%Z -> (q + 64 <= 2^47 - 1)%Z ->
  app_range T (zlength txt) -> shadow_ok m T (p + 1) ->
  evt bsegs (shgetc_postA ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SHGETC) fc None m (seg_rom bsegs)).

Lemma shgetc_spec : shgetc_stmtA.
Proof.
  unfold shgetc_stmtA. intros until canary. intros FC ST0 Hn Hbuf Hrp Hw Hc0 TXT Hp BY [SSP1 SSP2] T0 T1 SEP3 ST SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1 MI.
  intros MR CEIL Q47 ART SOT.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. pose proof AINTRIN_STACK_val as AIS. unfold SHGETC_XD in *.
  pose proof (app_range_lt47 _ _ ART) as TB.
  assert (WAPP : Forall app_iv [(q - 2464, q); (Fp, Fp + 232)]%Z).
  { apply Forall_cons; [apply app_iv_stack; lia|]. apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil]. }
  assert (WMRT : Forall mrt_iv_ok [(q - 2464, q); (Fp, Fp + 232)]%Z).
  { apply Forall_cons; [apply mrt_iv_ok_stack; lia|]. apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil]. }
  pose proof (munch_refl [(q - 2464, q); (Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof TXT as TXT'. (nelim TXT' 5%nat; intros Htxt NZ BYT AL L256).
  assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length.
  assert (LT3 : length txt = (length pre + S (length post))%nat) by (rewrite Htxt, length_app; reflexivity).
  destruct f as [buf rpos cnt0 n st sn]. cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg] in *. subst st n buf.
  unfold rf_cells, rf_rend in FC. cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg] in FC.
  assert (J4 : length (j_pad0 ssJ) = 4%nat /\ length (j_pad1 ssJ) = 4%nat) by (split; reflexivity).
  cbn [ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
  pose proof (rw_cells_bound _ _ _ _ FC) as B. cbn [cells_size csize Nat.add] in B.
  unfold SHGETC, got_ssp, ssp_guard, STRING_READ, M64 in *. unfold zlength in *.
  assert (Roff : (0 <= rpos <= p)%Z) by (destruct w; subst rpos; lia).
  zs. carve_frame 32%nat ST.
  do 10 zs.
  (* [comment removed for export] *)
  assert (EOFT : forall m1 (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) j8 she shl shc cnt,
    cnt = (p - cnt0)%Z ->
    mem_inv bsegs m1 -> munch [(q - 2464, q); (Fp, Fp + 232)]%Z m m1 -> wmono bsegs m m1 ->
    stk bsegs m1 (q - 2464) (q + -32) ->
    rw_cells bsegs m1 (q + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra] ->
    rw_cells bsegs m1 Fp (rf_cells_raw T p true (mkSh txt p cnt0 p true true) ssJ she shl shc) ->
    bytes_at bsegs m1 T (zbytes txt) -> rw_cells bsegs m1 664456 [C8 (Z_to_bv 64 6277552)] -> rw_cells bsegs m1 6277552 [C8 canary] ->
    sh_getc {| sh_buf := txt; sh_rpos := rpos; sh_cnt0 := cnt0; sh_n := p; sh_stdio := true; sh_shlim_neg := sn |} = ((-1)%Z, mkSh txt p cnt0 p true true) ->
    evt bsegs (shgetc_postA ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p
                 {| sh_buf := txt; sh_rpos := rpos; sh_cnt0 := cnt0; sh_n := p; sh_stdio := true; sh_shlim_neg := sn |} txt canary m)
      (MS (mkR x1 (Z_to_bv 64 (q + -32)) gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 cnt) (Z_to_bv 64 T) (Z_to_bv 64 (T + p)) x12 x13 x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x97430) fc None m1 (seg_rom bsegs))).
  { clear FC MI MU WM ST FR BY SSP1 SSP2.
    intros m1 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 j8 she shl shc cnt Ecnt MI MU WM ST FR FC BY SSP1 SSP2 EG. subst cnt.
    unfold rf_cells_raw, rf_rend in FC.
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
    do 11 zs.
    release_frame FR ST q.
    apply evt_done. unfold shgetc_postA. rewrite EG. cbn [fst snd].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split. { unfold rf_cells, rf_rend. cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale].
             unfold STRING_READ, M64. replace (- cnt0)%Z with (p - cnt0 + (T - (T + p)))%Z by lia. hyp. }
    split; [exact BY|]. unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2]. }
  destruct sn.
  - (* [comment removed for export] *)
    assert (Ew : w = true) by (destruct w; [reflexivity | destruct (Hw eq_refl) as [_ X]; discriminate X]). subst w. cbn in Hrp. subst rpos.
    replace (if true then 18446744073709551615%Z else 0%Z) with 18446744073709551615%Z in * by reflexivity.
    replace (if true then (T + p)%Z else T) with (T + p)%Z in * by reflexivity.
    zs. br K1; try (exfalso; clear -K1; lia).
    zs. br K2.
    eapply EOFT; try hyp; try lia.
    all: try (unfold sh_getc; cbn [sh_stdio sh_rpos sh_n negb sh_buf sh_cnt0]; rewrite Z.eqb_refl; reflexivity).
    all: unfold rf_cells_raw, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale];
         unfold STRING_READ, M64; hyp.
  - (* [comment removed for export] *)
    replace (if false then 18446744073709551615%Z else 0%Z) with 0%Z in * by reflexivity.
    pose proof uflow_spec as UFS. unfold uflow_stmtA, got_ssp, ssp_guard, UFLOW, UFLOW_XD in UFS.
    destruct w.
    + (* [comment removed for export] *)
      cbn in Hrp. subst rpos.
      replace (if true then (T + p)%Z else T) with (T + p)%Z in * by reflexivity.
      zs. br K1; try (exfalso; clear -K1; lia).
      zs. zs.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MR1 : MRT mm) by (eapply MRT_munch; [exact MR| exact MU| exact WMRT]);
        assert (SOT1 : shadow_ok mm T (p + 1)) by (eapply shadow_ok_munch_app; [exact SOT| exact MU| lia| eapply app_range_sub; [exact ART| unfold zlength in *; lia| lia| lia]| exact WAPP]) end.
      callw (eapply UFS with (off := p) (pre := pre) (post := post) (p := p);
        [ unfold ss_cells, w0, zero4, STRING_READ, M64; hyp
        | right; reflexivity | exact TXT | exact Hp | | hyp | unfold ssp_cells, got_ssp, ssp_guard; split; hyp | | | | | | 
        | replace (q + -32 - 2432)%Z with (q - 2464)%Z by lia; hyp | | | | | | | | | | hyp
        | exact MR1 | lia | lia | unfold zlength; exact ART | exact SOT1 ]; unfold zlength; lia).
      clear MR1 SOT1.
      rename PC into ST. replace (q + -32 - 2432)%Z with (q - 2464)%Z in ST by lia. rename PC0 into FC. clear BY SSP1 SSP2. rename PC1 into BY. destruct POST as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
      unfold uflow_res, sread_len in *. replace (p <? p) with false in * by (symmetry; apply Z.ltb_irrefl).
      replace (T + p + 0)%Z with (T + p)%Z in FC by lia. unfold ss_cells, w0, zero4 in FC.
      zs. br K2; try (exfalso; clear -K2; lia).
      zs. zs.
      eapply EOFT; try hyp; try lia.
      all: try (unfold sh_getc; cbn [sh_stdio sh_rpos sh_n negb sh_buf sh_cnt0]; rewrite Z.eqb_refl; reflexivity).
      all: unfold rf_cells_raw, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale];
           unfold STRING_READ, M64 in *; hyp.
    + (* [comment removed for export] *)
      destruct (Hw eq_refl) as [Ec0 _]. subst rpos cnt0.
      replace (if false then (T + p)%Z else T) with T in * by reflexivity.
      assert (Rch : (0 <= znth txt 0 < 256)%Z).
      { destruct (Z.lt_ge_cases 0 (Z.of_nat (length txt))).
        - apply (proj1 (Forall_forall _ _) BYT). apply Shgetc_lemmas.znth_In'. unfold zlength. lia.
        - rewrite znth_ge by (unfold zlength; lia). lia. }
      zs. br K1; try (exfalso; clear -K1; lia).
      zs. zs.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MR1 : MRT mm) by (eapply MRT_munch; [exact MR| exact MU| exact WMRT]);
        assert (SOT1 : shadow_ok mm T (p + 1)) by (eapply shadow_ok_munch_app; [exact SOT| exact MU| lia| eapply app_range_sub; [exact ART| unfold zlength in *; lia| lia| lia]| exact WAPP]) end.
      callw (eapply UFS with (off := 0%Z) (pre := pre) (post := post) (p := p);
        [ rewrite (Z.add_0_r T); unfold ss_cells, w0, zero4, STRING_READ, M64; hyp
        | right; reflexivity | exact TXT | exact Hp | | hyp | unfold ssp_cells, got_ssp, ssp_guard; split; hyp | | | | | | 
        | replace (q + -32 - 2432)%Z with (q - 2464)%Z by lia; hyp | | | | | | | | | | hyp
        | exact MR1 | lia | lia | unfold zlength; exact ART | exact SOT1 ]; unfold zlength; lia).
      clear MR1 SOT1.
      rename PC into ST. replace (q + -32 - 2432)%Z with (q - 2464)%Z in ST by lia. rename PC0 into FC. clear BY SSP1 SSP2. rename PC1 into BY. destruct POST as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
      unfold uflow_res, sread_len in *. unfold ss_cells, w0, zero4 in FC.
      destruct (Z.ltb_spec0 0 p).
      * (* [comment removed for export] *)
        replace (T + 0 + 1)%Z with (T + 1)%Z in FC by lia.
        zs. br K2; try (exfalso; clear -K2 Rch; lia).
        do 5 zs. br K3; try (exfalso; clear -K3; lia).
        do 5 zs. zs. br K4; try (exfalso; clear -K4; lia).
        do 5 zs.
        release_frame FR ST q.
        apply evt_done. unfold shgetc_postA. unfold sh_getc. cbn [sh_stdio sh_rpos sh_n negb sh_buf sh_cnt0 fst snd].
        replace (0 =? p) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb fst snd sh_stdio sh_rpos sh_n sh_buf sh_cnt0 sh_shlim_neg].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [hyp|]. split; [exact ST|].
        split. { unfold rf_cells, rf_rend. cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale].
                 unfold STRING_READ, M64 in *. hyp_cells. }
        split; [exact BY|]. unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
      * (* [comment removed for export] *)
        assert (Ep : p = 0%Z) by lia.
        replace (0 <? p) with false in * by (symmetry; apply Z.ltb_ge; lia).
        replace (T + 0 + 0)%Z with (T + p)%Z in FC by lia.
        zs. br K2; try (exfalso; clear -K2; lia).
        zs. zs.
        replace (T + 0 + 0)%Z with (T + p)%Z by lia.
        eapply EOFT; try hyp; try lia.
        all: try (unfold sh_getc; cbn [sh_stdio sh_rpos sh_n negb sh_buf sh_cnt0]; replace (0 =? p) with true by (symmetry; apply Z.eqb_eq; lia); rewrite <- Ep; reflexivity).
        all: rewrite <- ?Ep; unfold rf_cells_raw, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale];
             unfold STRING_READ, M64 in *; hyp.
Qed.

End CeilWrap.
(* [comment removed for export] *)
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.
End F_shgetc_proofs3.

(* [comment removed for export] *)
Module F_rfile.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_musl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_frexpl.F_fmt_fp_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_proofs.F_shgetc F_rscan_lib F_shgetc_proofs3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Definition RFJ (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
  sh_ok T txt f /\ (-1 <= c < 256)%Z /\ (0 <= sh_cnt0 f <= sh_rpos f)%Z /\
  (sh_shlim_neg f = false -> sh_cnt0 f + kmin <= sh_rpos f)%Z /\
  (sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
  (sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
                        (w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ J = ssJ)%Z.

Section RF.
  Variables (T : Z) (txt : list Z) (p : Z) (J : rfj).
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) txt.
  Hypothesis Hp : 0 <= p < zlength txt.
  Hypothesis Hnul : znth txt p = 0.
  Hypothesis T0 : 4096 <= T.
  Hypothesis T1 : T + 2^41 <= 2^63.

  Notation RFI := (RFJ T txt p true J).

  Lemma RFI_ok : forall kmin c f, RFI kmin c f -> sh_ok T txt f.
  Proof. intros kmin c f (OK & _). exact OK. Qed.

  Lemma RFI_rpos : forall kmin c f, RFI kmin c f -> 0 <= sh_rpos f <= p + 1.
  Proof.
    intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
    destruct (sh_stdio f) eqn:ES; [destruct (SS eq_refl) as (N1 & N2 & _); lia | destruct (NS eq_refl) as (N1 & N2 & N3); lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rf_getc_fast : forall kmin c f, RFI kmin c f ->
    T + sh_rpos f <> rf_rend T p true f ->
    sh_getc f = (znth txt (sh_rpos f), mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)).
  Proof.
    intros kmin c f (OK & Rc & CC & KM & NS & SS) NE. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
    unfold rf_rend in NE. unfold sh_getc. rewrite Hbuf.
    destruct (sh_stdio f) eqn:ES; cbn [negb].
    - destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & N5). rewrite N1.
      destruct (Z.eqb_spec (sh_rpos f) p) as [E|NE']; [exfalso; lia|]. reflexivity.
    - reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rf_getc_fast_lt : forall kmin c f, RFI kmin c f -> c <> 0 ->
    T + sh_rpos f <> rf_rend T p true f -> 0 <= sh_rpos f < zlength txt.
  Proof.
    intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc NE. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
    unfold rf_rend in NE. destruct (sh_stdio f) eqn:ES.
    - destruct (SS eq_refl) as (N1 & N2 & N3 & _). lia.
    - destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rf_getc_slow : forall kmin c f, RFI kmin c f ->
    T + sh_rpos f = rf_rend T p true f ->
    sh_stdio f = true /\ J = ssJ /\ sh_n f = p /\ sh_rpos f = p /\ 0 <= sh_cnt0 f <= sh_rpos f.
  Proof.
    intros kmin c f (OK & Rc & CC & KM & NS & SS) E. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
    unfold rf_rend in E. destruct (sh_stdio f) eqn:ES.
    - destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & N5). repeat split; try assumption; unfold M64 in E; lia.
    - exfalso. unfold M64 in E. lia.
  Qed.

  Ltac crush := repeat progress (repeat split; try reflexivity; try discriminate; try assumption; try lia;
                                 try lazymatch goal with |- (_ -> _) => intro end).

  Lemma RFI_getc : forall kmin c f, RFI kmin c f -> c <> 0 -> RFI (kmin + 1) (fst (sh_getc f)) (snd (sh_getc f)).
  Proof.
    intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst). unfold zlength in *.
    assert (R0 : forall i, 0 <= i < Z.of_nat (length txt) -> 0 <= znth txt i < 256).
    { intros i Hi. apply (proj1 (Forall_forall _ _) BYT). apply Shgetc_lemmas.znth_In'. unfold zlength. lia. }
    destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf.
    unfold RFJ, sh_getc, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
    destruct st; cbn [negb].
    - destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & N5). subst n.
      destruct (Z.eqb_spec rpos p) as [E|NE]; cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
      + unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
      + pose proof (R0 rpos ltac:(lia)).
        assert (SN : sn = false) by (destruct sn; [specialize (N3 eq_refl); lia | reflexivity]). subst sn. specialize (KM eq_refl).
        unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
    - destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). subst sn. cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
      pose proof (R0 rpos ltac:(lia)). specialize (KM eq_refl).
      unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
      all: destruct (Z.eq_dec rpos p) as [Ep|]; [|lia]; exfalso; subst rpos; rewrite Hnul in *; lia.
  Qed.

  Lemma RFI_unget : forall kmin c f, RFI kmin c f -> 1 <= kmin -> RFI (kmin - 1) c (sh_unget f).
  Proof.
    intros kmin c f (OK & Rc & CC & KM & NS & SS) Hk. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
    destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf.
    unfold RFJ, sh_unget, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
    destruct sn; cbn [negb sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
    - destruct st.
      + destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & N5). specialize (N3 eq_refl). crush.
      + destruct (NS eq_refl) as (N1 & _). discriminate N1.
    - specialize (KM eq_refl). destruct st.
      + destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & N5). crush.
      + destruct (NS eq_refl) as (N1 & N2 & N3). crush.
  Qed.

  (* [comment removed for export] *)
  Lemma rf_unget_shlim : forall f, (if sh_shlim_neg f then M64 else 0) = (if sh_shlim_neg (sh_unget f) then M64 else 0).
  Proof. intros [b r c n st sn]. unfold sh_unget. cbn. destruct sn; reflexivity. Qed.
  Lemma rf_unget_eq : forall f, sh_shlim_neg f = false ->
    sh_unget f = mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f).
  Proof. intros [b r c0 n st sn] H. cbn in H. subst sn. reflexivity. Qed.
  Lemma rf_unget_nop : forall f, sh_shlim_neg f = true -> sh_unget f = f.
  Proof. intros [b r c0 n st sn] H. cbn in H. subst sn. reflexivity. Qed.
End RF.
(* [comment removed for export] *)

Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scan_ax (m : word -> option byte) (q depth Fp T : Z) (txt : list Z) (p : Z) : Prop :=
  MRT m /\ (alloc_ceiling + 64 <= q - depth)%Z /\ (q + 64 <= 2^47 - 1)%Z /\ app_range T (zlength txt) /\ shadow_ok m T (p + 1).

(* [comment removed for export] *)
Definition scan_iv_ok (iv : Z * Z) : Prop := (KHIGHMEM_BEG <= fst iv)%Z \/ (0x1e4000 <= fst iv /\ snd iv <= 0x7fff8000)%Z.

Lemma scan_ax_xfer : forall m0 m q d q' d' Fp T txt p W,
  scan_ax m0 q d Fp T txt p -> munch W m0 m -> Forall scan_iv_ok W ->
  (q - d <= q' - d')%Z -> (q' <= q)%Z -> (0 <= p)%Z -> (p + 1 <= zlength txt)%Z ->
  scan_ax m q' d' Fp T txt p.
Proof.
  intros m0 m q d q' d' Fp T txt p W (MR & CE & Q47 & AR & SO) MU HW Hd Hq Hp0 Hp1.
  assert (HM : Forall mrt_iv_ok W).
  { eapply Forall_impl; [| exact HW]. intros [u v] [H|[H1 H2]]; [apply mrt_iv_ok_high; exact H| apply mrt_iv_ok_mid; assumption]. }
  assert (HA : Forall app_iv W).
  { eapply Forall_impl; [| exact HW]. intros [u v] [H|[H1 H2]]; [right; exact H| left; exact H2]. }
  split; [| split; [| split; [| split]]].
  - eapply MRT_munch; [exact MR| exact MU| exact HM].
  - lia.
  - lia.
  - exact AR.
  - eapply shadow_ok_munch_app; [exact SO| exact MU| lia| | exact HA]. eapply app_range_sub; [exact AR| lia| lia| lia].
Qed.

Lemma scan_ax_here : forall m q d q' d' Fp T txt p,
  scan_ax m q d Fp T txt p -> (q - d <= q' - d')%Z -> (q' <= q)%Z -> scan_ax m q' d' Fp T txt p.
Proof. intros m q d q' d' Fp T txt p (MR & CE & Q47 & AR & SO) Hd Hq. split; [exact MR| split; [lia| split; [lia| split; [exact AR| exact SO]]]]. Qed.

(* [comment removed for export] *)
Lemma shgetc_callJ : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (J : rfj) (kmin c : Z) (f : shfile) (txt pre post : list Z) (canary : word),
  rw_cells bsegs m Fp (rf_cells T p true f J) ->
  RFJ T txt p true J kmin c f ->
  (T + sh_rpos f = rf_rend T p true f)%Z ->
  rtext T txt pre post -> p = zlength pre -> bytes_at bsegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk bsegs m (q - 2464) q -> (4096 <= q - 2464)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 2464 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 2464)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv bsegs m ->
  scan_ax m q 2464 Fp T txt p ->
  evt bsegs (shgetc_postA ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SHGETC) fc None m (seg_rom bsegs)).
Proof.
  intros until canary. intros FC RJ SLOW TXT Hp BY SSP T0 T1 SEP ST SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1 MI (MR & CEIL & Q47 & ART & SOT).
  pose proof RJ as RJ'. destruct RJ' as (OK & Rc & CC & KM & NS & SS).
  assert (Hp2 : (0 <= p < zlength txt)%Z).
  { destruct TXT as (Htxt & _ & _ & _ & _). subst p txt. unfold zlength. rewrite length_app. cbn. lia. }
  destruct (rf_getc_slow T txt p J Hp2 T1 kmin c f RJ SLOW) as (ST0 & EJ & Hn & Hrp & Hc0).
  subst J.
  eapply shgetc_spec with (w := true) (pre := pre) (post := post); try eassumption; try (unfold SHGETC_XD; lia).
  all: try (destruct OK as (Hbuf & _); exact Hbuf).
  all: try (cbn; exact Hrp).
  all: try (intros X; discriminate X).
Qed.


End CeilWrap.
End F_rfile.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs CJ_iface AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat StrFun FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_memcpy F_memchr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_frexpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_frexpl.F_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_shgetc_proofs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_proofs.F_shgetc.
Import F_rscan_lib.
Import F_rfile.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac step ::= step2. Local Ltac stepz ::= step2.
Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.

  (* [comment removed for export] *)
Local Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Local Ltac brsf K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
    repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
    first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac].
Local Ltac br10 K := brf K; [ exfalso; lia | ].
Local Ltac br01 K := brf K; [ | exfalso; lia ].
  (* [comment removed for export] *)
Local Ltac zsimp_in_w H :=
    try (match type of H with
         | context [v_sltu _ _] => idtac | context [v_slt _ _] => idtac
         | context [v_sltiu _ _] => idtac | context [v_slti _ _] => idtac end;
         rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H);
    try (match type of H with context [zxb] => cbv delta [zxb] in H end);
    zb_fold_lits_in H;
    repeat match type of H with
    | context [bv_unsigned (Z_to_bv 64 ?e)] => zs_wrap_in e H
    | _ => progress (zs_idioms_in H)
    end; zb_fold_lits_in H.
Local Ltac brfw K := if_cases K; rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in K;
    unfold bv_eqb, bv_ltu, bv_lts, bv_leu in K; fold_lit_ux_in K; zsimp_in_w K; zify_bool K;
    try (rewrite ?signed_of_Z in K by lia).
(* [comment removed for export] *)
Local Ltac lia_goal_g P := lazymatch P with
  | (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
  | (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
  | @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
  | ?A /\ ?B => lia_goal_g A; lia_goal_g B | ?A \/ ?B => lia_goal_g A; lia_goal_g B | ?A -> ?B => lia_goal_g B | ~ _ => idtac
  | ?A <-> ?B => lia_goal_g A; lia_goal_g B | False => idtac | True => idtac
  end.
Local Ltac glia := lazymatch goal with |- ?G => lia_goal_g G end; lia.
Definition SCANEXP : Z := 0x991fc.
Definition SCANEXP_DEPTH : Z := 2544.   (* [comment removed for export] *)

Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
Proof using . intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. split; intros H; Z.div_mod_to_equations; lia. Qed.
Lemma isdigitc_t : forall c, (-2^31 < c < 2^31)%Z -> (48 <= c <= 57)%Z -> isdigitc c = true.
Proof using . intros. apply (proj2 (isdigitc_iff c ltac:(lia))). lia. Qed.
Lemma isdigitc_f : forall c, (-2^31 < c < 2^31)%Z -> ~ (48 <= c <= 57)%Z -> isdigitc c = false.
Proof using . intros c Hc H. destruct (isdigitc c) eqn:E; [|reflexivity]. exfalso. apply H. apply (proj1 (isdigitc_iff c Hc)). exact E. Qed.

(* [comment removed for export] *)
Definition scanexp_tail (fuelc : nat) (neg c : Z) (f : shfile) : option (shfile * Z) :=
  if negb (isdigitc c) then Some (sh_unget f, LLONG_MIN_) else
  match scanexp_l1_loop fuelc (0%Z, c, f) with
  | None => None
  | Some (x, c, f) =>
    match scanexp_l2_loop fuelc (x, c, f) with
    | None => None
    | Some (y, c, f) =>
      match scanexp_l3_loop fuelc (c, f) with
      | None => None
      | Some (c, f) => Some (sh_unget f, if nz neg then (- y)%Z else y)
      end end end.

Lemma scanexp_eq : forall fuelc f pok,
  scanexp fuelc f pok =
  (let '(c, f) := sh_getc f in
   let '(neg, c, f) :=
     (if ((c =? 43) || (c =? 45))%Z then
        let neg := b2z (c =? 45)%Z in
        let '(c, f) := sh_getc f in
        let f := if negb (isdigitc c) && nz pok then sh_unget f else f in (neg, c, f)
      else (0%Z, c, f)) in
   scanexp_tail fuelc neg c f).
Proof using .
  intros fuelc f pok. unfold scanexp, scanexp_tail.
  destruct (sh_getc f) as [c1 f1].
  destruct (if ((c1 =? 43) || (c1 =? 45))%Z then _ else _) as [[neg c2] f2]. reflexivity.
Qed.

Definition scanexp_rpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p : Z) (J : rfj) (txt : list Z) (canary : word) (fR : shfile) (e10 : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' k' c',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e10) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' (q - SCANEXP_DEPTH) q
    /\ rw_cells bsegs m' Fp (rf_cells T p true fR J)
    /\ RFJ T txt p true J k' c' fR /\ (1 <= k')%Z
    /\ bytes_at bsegs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition scanexp_rstmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z),
  scanexp fuelc f0 pok = Some (fR, e10) ->
  rw_cells bsegs m Fp (rf_cells T p true f0 J) -> RFJ T txt p true J kmin0 c0 f0 -> (1 <= kmin0)%Z -> c0 <> 0%Z ->
  (sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre) ->
  Forall (fun c => 0 <= c < 256)%Z txt -> (0 <= p < zlength txt)%Z -> znth txt p = 0%Z ->
  bytes_at bsegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk bsegs m (q - SCANEXP_DEPTH) q -> (4096 <= q - SCANEXP_DEPTH)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= pok <= 1)%Z -> (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv bsegs m ->
  (sh_stdio f0 = true -> scan_ax m q SCANEXP_DEPTH Fp T txt p) ->     (* [comment removed for export] *)
  evt bsegs (scanexp_rpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p J txt canary fR e10 m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCANEXP) fc None m (seg_rom bsegs)).

Section Scanexp.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
            (Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z).
  Hypothesis HM : scanexp fuelc f0 pok = Some (fR, e10).
  Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
  Hypothesis Hp : (0 <= p < zlength txt)%Z.
  Hypothesis Hnul : znth txt p = 0%Z.
  Hypothesis T0 : (4096 <= T)%Z.
  Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
  Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
  Hypothesis SPLO : (4096 <= q - SCANEXP_DEPTH)%Z.
  Hypothesis SPF : (q <= Fp)%Z.
  Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
  Hypothesis SPT : (T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z.
  Hypothesis SG1 : (ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z.
  Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
  Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
  Hypothesis Hpok : (0 <= pok <= 1)%Z.
  Hypothesis Q0 : (0 <= q)%Z.
  Hypothesis Q1 : (q < 2^63)%Z.
  (* [comment removed for export] *)
  Local Ltac sec_tier := solve [ rewrite ?zbytes_length; let HI := fresh "HI" in pose proof I as HI;
                                 clear - HI Hp T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1;
                                 unfold zlength, SCANEXP_DEPTH, got_ssp, ssp_guard, sf_hide in *; Zify.zify; xlia zchecker ].
  Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | sec_tier | tlia | split; [ tlia | exact I ] ].
  Hypothesis AXS : sh_stdio f0 = true -> scan_ax m0 q SCANEXP_DEPTH Fp T txt p.   (* [comment removed for export] *)

  Notation POST := (scanexp_rpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p J txt canary fR e10 m0).
  Notation SPv := (Z_to_bv 64 (q + -80)).
  Notation RFJ' := (RFJ T txt p true J).
  Definition frame (j8 : list byte) : list cell := [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Definition finv (m : word -> option byte) (j8 : list byte) : Prop :=
    mem_inv bsegs m /\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m0 m /\ wmono bsegs m0 m
    /\ rw_cells bsegs m (q + -80) (frame j8) /\ stk bsegs m (q - SCANEXP_DEPTH) (q + -80)
    /\ bytes_at bsegs m T (zbytes txt) /\ ssp_cells m canary.
  Ltac dest_finv H := (nelim H 7%nat; intros MI MU WM FR ST BY [SSP1 SSP2]); unfold frame in FR; unfold SCANEXP_DEPTH in MU, ST;
    unfold got_ssp, ssp_guard in SSP1, SSP2;
    try (let LTX := fresh "LTX" in assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length; unfold zlength in * ).
  Ltac mk_finv := unfold finv, frame, SCANEXP_DEPTH, ssp_cells, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.

  (* [comment removed for export] *)
  Lemma stdio_getc : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
  Proof using . intros f. unfold sh_getc. destruct (sh_stdio f); cbn [negb]; [destruct (_ =? _); reflexivity | reflexivity]. Qed.
  Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
  Proof using . intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma L_ret : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c fX,
    finv m j8 -> rw_cells bsegs m Fp (rf_cells T p true fX J) -> RFJ' k c fX -> (1 <= k)%Z -> fX = fR ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 e10) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x9943c) fc None m (seg_rom bsegs)).
  Proof using pre.
    intros until fX. intros FI FC RJ Hk EX. subst fX. dest_finv FI. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. unfold got_ssp, ssp_guard in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
    do 12 zs.
    release_frame FR ST q.
    apply evt_done. unfold scanexp_rpost, SCANEXP_DEPTH. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact FC|]. split; [exact RJ|]. split; [exact Hk|]. split; [exact BY | split; [exact SSP1 | exact SSP2]].
  Qed.

  Ltac unfold_fc FC := unfold rf_cells, rf_rend in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

  (* [comment removed for export] *)
  Lemma L_end : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (v neg : Z),
    finv m j8 -> rw_cells bsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
    (0 <= neg <= 1)%Z -> (-2^63 <= v < 2^63)%Z ->
    fR = sh_unget f -> e10 = (if nz neg then - v else v)%Z ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 v) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x99420) fc None m (seg_rom bsegs)).
  Proof using Hp SEP SG1 SG2 SG3 SPF SPT T0 T1 pre.
    intros until neg. intros FI FC RJ Hk Rneg Rv HfR He.
    pose proof FI as FI'. dest_finv FI'. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. unfold got_ssp, ssp_guard in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
    pose proof RJ as RJ2. (nelim RJ2 6%nat; intros OK Rc CC KM NS SS). (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst).
    assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia). unfold M64 in RR.
    pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
    destruct (sh_shlim_neg f) eqn:SN.
    - (* [comment removed for export] *)
      rewrite (rf_unget_nop f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
      zs. zs. br01 K1.
      zs. brf K2.
      + assert (Ee : e10 = v) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia). rewrite <- Ee.
        eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
        unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
      + zs. assert (Ee : e10 = (- v)%Z) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia).
        replace (Z_to_bv 64 (0 - Z.land v 18446744073709551615)%Z) with (Z_to_bv 64 e10) by (apply Z_to_bv_eqm; rewrite Ee, land_W64; Z.div_mod_to_equations; lia).
        eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
        unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
    - (* [comment removed for export] *)
      rewrite (rf_unget_eq f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
      zs. zs. br10 K1.
      zs. zs. zs.
      zs. brf K2.
      + assert (Ee : e10 = v) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia). rewrite <- Ee.
        eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
        unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
      + zs. assert (Ee : e10 = (- v)%Z) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia).
        replace (Z_to_bv 64 (0 - Z.land v 18446744073709551615)%Z) with (Z_to_bv 64 e10) by (apply Z_to_bv_eqm; rewrite Ee, land_W64; Z.div_mod_to_equations; lia).
        eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
        unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
  Qed.

  (* [comment removed for export] *)
  Lemma L_ND : forall m j8 (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
    finv m j8 -> rw_cells bsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
    fR = sh_unget f -> e10 = LLONG_MIN_ ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x992e4) fc None m (seg_rom bsegs)).
  Proof using Hp SEP SG1 SG2 SG3 SPF SPT T0 T1 pre.
    intros until f. intros FI FC RJ Hk HfR He.
    pose proof FI as FI'. dest_finv FI'. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. unfold got_ssp, ssp_guard in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
    pose proof RJ as RJ2. (nelim RJ2 6%nat; intros OK Rc CC KM NS SS). (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst).
    assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia). unfold M64 in RR.
    pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
    destruct (sh_shlim_neg f) eqn:SN.
    - rewrite (rf_unget_nop f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
      zs. zs. zs. zs. br01 K1.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 e10) by (rewrite He; apply Z_to_bv_eqm; vm_compute; reflexivity).
      eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
      unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
    - rewrite (rf_unget_eq f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
      zs. zs. zs. zs. br10 K1.
      zs. zs. zs. zs.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 e10) by (rewrite He; apply Z_to_bv_eqm; vm_compute; reflexivity).
      eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
      unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
  Qed.

  Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.
  Ltac unfold_fc2 FC := unfold rf_cells in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
  (* [comment removed for export] *)
  Ltac post_getc :=
    match goal with H : ssp_cells ?m' _ |- _ =>
      repeat match goal with H2 : rw_cells _ _ 664456 _ |- _ => clear H2 | H2 : rw_cells _ _ 6277552 _ |- _ => clear H2 end;
      destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end;
    match goal with H : stk _ ?m' (q + -80 - 2464)%Z _ |- _ =>
      replace (q + -80 - 2464)%Z with (q - 2544)%Z in H by lia;
      try match goal with H2 : stk _ _ (q - 2544)%Z _ |- _ => tryif constr_eq H H2 then fail else clear H2 end end;
    repeat match goal with H : bytes_at _ ?m' T ?x, H2 : bytes_at _ ?m' T ?x |- _ => clear H2 end.
  (* [comment removed for export] *)
  Ltac fsx :=
    lazymatch goal with |- scan_ax ?mm _ _ _ _ _ _ =>
      match goal with S : sh_stdio f0 = true, MUx : munch _ m0 mm |- _ =>
        let X := fresh "AXc" in pose proof (AXS S) as X;
        let C := fresh "AXce" in pose proof (proj1 (proj2 X)) as C; unfold alloc_ceiling, sp_window_lo, stack_max_size, SCANEXP_DEPTH in C;
        eapply (scan_ax_xfer m0 mm _ _ _ _ Fp T txt p _ X MUx);
        [ unfold scan_iv_ok; repeat (apply Forall_cons; [cbn [fst snd]; unfold KHIGHMEM_BEG, alloc_ceiling, sp_window_lo, stack_max_size; lia|]); apply Forall_nil
        | unfold SCANEXP_DEPTH; lia | lia | lia | unfold zlength in *; lia ]
      end end.
  (* [comment removed for export] *)
  Ltac site_facts FC RJ k c f :=
    unfold SCANEXP_DEPTH in SPLO, SPT, SG1; unfold got_ssp, ssp_guard in SG1, SG2, SG3;
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
    pose proof RJ as RJ2; (nelim RJ2 6%nat; intros OK Rc CC KM NS SS); (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst);
    assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
    pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.

  (* [comment removed for export] *)
  Lemma L_L3 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (y neg cX : Z) fX,
    finv m j8 -> rw_cells bsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z ->
    scanexp_l3_loop n (sh_getc f) = Some (cX, fX) ->
    fR = sh_unget fX -> e10 = (if nz neg then - y else y)%Z -> (0 <= neg <= 1)%Z -> (-2^63 <= y < 2^63)%Z ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 10) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x99400) fc None m (seg_rom bsegs)).
  Proof using AXS BYT Hnul Hp Q1 SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT ST0 T0 T1.
    induction n as [|n IH]; [intros; discriminate|].
    intros until fX. intros FI FC RJ Hk Hst Hc HL HfR He Rneg Ry.
    pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
    pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
    rewrite (surjective_pairing (sh_getc f)) in HL. cbn [scanexp_l3_loop scanexp_l3_body] in HL.
    assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by ((nelim RJ1 3%nat; intros _ R _); exact R).
    assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x19' x21' x22' x23' x28' x29' x30' x31' : word) x1',
      finv m2 j8' -> rw_cells bsegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
      evt bsegs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10' x11' x12' x13' x14' x15' x16' x17'
                 (Z_to_bv 64 10) x19' (Z_to_bv 64 neg) x21' x22' x23' s8 s9 s10 s11 x28' x29' x30' x31')
            F (Z_to_bv 64 0x99400) fc None m2 (seg_rom bsegs))).
    { intros Hd. intros. rewrite (isdigitc_t (fst (sh_getc f))) in HL by lia.
      eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try glia. }
    assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x21' x22' x23' x28' x29' x30' x31' : word) x1',
      finv m2 j8' -> rw_cells bsegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
      evt bsegs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10' x11' x12' x13' x14' x15' x16' x17'
                 x18' x19' (Z_to_bv 64 neg) x21' x22' x23' s8 s9 s10 s11 x28' x29' x30' x31')
            F (Z_to_bv 64 0x99420) fc None m2 (seg_rom bsegs))).
    { intros Hd. intros. rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. injection HL as E1 E2. subst cX fX.
      eapply L_end with (k := (k + 1)%Z); try eassumption; try glia. }
    clear IH HL.
    pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
    destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
    - (* [comment removed for export] *)
      pose proof FC as FC0. unfold_fc2 FC.
      zs. zs. zs. br K.
      (nelim (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) 5%nat; intros STD EJ Hn Hrp Hc0).
      assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
      zs. zs. callw (eapply shgetc_callJ;
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
        | plia | plia | plia | replace (q + -80 - 2464)%Z with (q - 2544)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI | fsx ]).
      post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
      zs. fixw2. zs. brfw K2.
      + (* [comment removed for export] *) eapply ND; [mlia2 | mk_finv | exact FC].
      + eapply DIG; [mlia2 | mk_finv | exact FC].
    - (* [comment removed for export] *)
      pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Shgetc_lemmas.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
      unfold_fc2 FC.
      zs. zs. zs. br10 K.
      zs. zs.
      pose proof (u8ro_read bsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Shgetc_lemmas.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
      zs. cbv beta. rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
      zs. fixw2. zs. brfw K2.
      + eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
      + eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
  Qed.

  Definition LM : Z := 92233720368547758.
  Lemma LM_eq : Z.quot LLONG_MAX_ 100 = LM. Proof using . reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma L_L2 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) x1 k c f (y neg y2 c2 : Z) f2 n3 cX fX,
    finv m j8 -> rw_cells bsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z -> (0 <= y < LM)%Z ->
    scanexp_l2_loop n (y, c, f) = Some (y2, c2, f2) ->
    scanexp_l3_loop n3 (c2, f2) = Some (cX, fX) ->
    fR = sh_unget fX -> e10 = (if nz neg then - y2 else y2)%Z -> (0 <= neg <= 1)%Z ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 9) (Z_to_bv 64 c) (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x9938c) fc None m (seg_rom bsegs)).
  Proof using AXS BYT Hnul Hp Q1 SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT ST0 T0 T1.
    induction n as [|n IH]; [intros; discriminate|].
    intros until fX. intros FI FC RJ Hk Hst Hc Hy HL HL3 HfR He Rneg. pose proof Hy as Hy0. unfold LM in Hy.
    pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
    pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
    cbn [scanexp_l2_loop scanexp_l2_cond scanexp_l2_body] in HL. rewrite (isdigitc_t c), LM_eq in HL by lia.
    replace (y <? LM) with true in HL by (symmetry; apply Z.ltb_lt; exact (proj2 Hy0)). cbn [andb] in HL.
    rewrite (surjective_pairing (sh_getc f)) in HL.
    assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by ((nelim RJ1 3%nat; intros _ R _); exact R).
    set (y' := (10 * y + c - 48)%Z) in HL.
    assert (Ry' : (0 <= y' <= 10 * LM - 1)%Z) by (unfold y', LM in *; lia).
    assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x12' x13' x14' x15' x16' x17' x19' x23' x28' x29' x30' x31' : word) x1',
      finv m2 j8' -> rw_cells bsegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
      evt bsegs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y') (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 (fst (sh_getc f) - 48)) x12' x13' x14' x15' x16' x17'
                 (Z_to_bv 64 9) x19' (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23' s8 s9 s10 s11 x28' x29' x30' x31')
            F (Z_to_bv 64 0x993d8) fc None m2 (seg_rom bsegs))).
    { intros Hd. intros until x1'. intros FI2 FC2.
      pose proof FI2 as FI'. dest_finv FI'. unfold LM in *.
      zs. zs. brsf K.
      - eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try glia.
      - destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL.
        rewrite LM_eq in HL. replace (y' <? LM) with false in HL by (symmetry; apply Z.ltb_ge; unfold LM; lia). rewrite Bool.andb_false_r in HL.
        injection HL as E1 E2 E3. subst y2 c2 f2.
        destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_t (fst (sh_getc f))) in HL3 by lia.
        zs. zs. br10 K2; try (exfalso; mlia2). zs. zs.
        eapply L_L3 with (k := (k + 1)%Z); try eassumption; unfold LM in *; try glia. }
    assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x12' x13' x14' x15' x16' x17' x18' x19' x23' x28' x29' x30' x31' : word) x1',
      finv m2 j8' -> rw_cells bsegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
      evt bsegs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y') x10' (Z_to_bv 64 (fst (sh_getc f) - 48)) x12' x13' x14' x15' x16' x17'
                 x18' x19' (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23' s8 s9 s10 s11 x28' x29' x30' x31')
            F (Z_to_bv 64 0x993e0) fc None m2 (seg_rom bsegs))).
    { intros Hd. intros until x1'. intros FI2 FC2.
      destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL.
      rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. cbn [andb] in HL. injection HL as E1 E2 E3. subst y2 c2 f2.
      destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_f (fst (sh_getc f))) in HL3 by lia.
      injection HL3 as E4 E5. subst cX fX.
      pose proof FI2 as FI'. dest_finv FI'.
      zs. zs. brfw K2; try (exfalso; mlia2).
      eapply L_end with (k := (k + 1)%Z); try eassumption; unfold LM in *; try glia. }
    clear IH HL HL3.
    pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
    destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
    - (* [comment removed for export] *)
      pose proof FC as FC0. unfold_fc2 FC.
      zs. zs. zs. br K.
      (nelim (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) 5%nat; intros STD EJ Hn Hrp Hc0).
      assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
      zs. zs. callw (eapply shgetc_callJ;
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
        | plia | plia | plia | replace (q + -80 - 2464)%Z with (q - 2544)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI | fsx ]).
      post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
      zs. zs. zs. fixw2. zs.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 y') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small y) by lia; lia).
      let v := getreg 11%Z in replace v with (Z_to_bv 64 (fst (sh_getc f) - 48)) by reflexivity.
      zs. brfw K2.
      + (* [comment removed for export] *) eapply ND; [mlia2 | mk_finv | exact FC].
      + eapply DIG; [mlia2 | mk_finv | exact FC].
    - (* [comment removed for export] *)
      pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Shgetc_lemmas.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
      unfold_fc2 FC.
      zs. zs. zs. br10 K.
      zs. zs.
      pose proof (u8ro_read bsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Shgetc_lemmas.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
      zs. cbv beta. rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
      zs. zs. zs. fixw2. zs.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 y') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small y) by lia; lia).
      let v := getreg 11%Z in replace v with (Z_to_bv 64 (znth txt (sh_rpos f) - 48)) by reflexivity.
      zs. brfw K2.
      + eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
      + zs. eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
  Qed.

  Definition IM : Z := 214748364.
  Lemma IM_eq : Z.quot INT_MAX_ 10 = IM. Proof using . reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma L_L1 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) x1 k c f (x neg xv c1 : Z) f1 n2 y2 c2 f2 n3 cX fX,
    finv m j8 -> rw_cells bsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z -> (0 <= x < IM)%Z ->
    scanexp_l1_loop n (x, c, f) = Some (xv, c1, f1) ->
    scanexp_l2_loop n2 (xv, c1, f1) = Some (y2, c2, f2) ->
    scanexp_l3_loop n3 (c2, f2) = Some (cX, fX) ->
    fR = sh_unget fX -> e10 = (if nz neg then - y2 else y2)%Z -> (0 <= neg <= 1)%Z ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 x) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 c) x19 (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x99320) fc None m (seg_rom bsegs)).
  Proof using AXS BYT Hnul Hp Q1 SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT ST0 T0 T1.
    induction n as [|n IH]; [intros; discriminate|].
    intros until fX. intros FI FC RJ Hk Hst Hc Hx HL HL2 HL3 HfR He Rneg. pose proof Hx as Hx0. unfold IM in Hx.
    pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
    pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
    cbn [scanexp_l1_loop scanexp_l1_cond scanexp_l1_body] in HL. rewrite (isdigitc_t c), IM_eq in HL by lia.
    replace (x <? IM) with true in HL by (symmetry; apply Z.ltb_lt; exact (proj2 Hx0)). cbn [andb] in HL.
    rewrite (surjective_pairing (sh_getc f)) in HL.
    assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by ((nelim RJ1 3%nat; intros _ R _); exact R).
    set (x' := (10 * x + c - 48)%Z) in HL.
    assert (Rx' : (0 <= x' < 2^31)%Z) by (unfold x' in *; lia).
    assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x18' x28' x29' x30' x31' : word) x1',
      finv m2 j8' -> rw_cells bsegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
      evt bsegs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 x') (Z_to_bv 64 (fst (sh_getc f) - 48)) x11' x12' x13' x14' x15' x16' x17'
                 x18' (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28' x29' x30' x31')
            F (Z_to_bv 64 0x99370) fc None m2 (seg_rom bsegs))).
    { intros Hd. intros until x1'. intros FI2 FC2.
      pose proof FI2 as FI'. dest_finv FI'. unfold IM in *.
      zs. zs. brsf K.
      - eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try glia.
      - destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l1_loop scanexp_l1_cond] in HL.
        rewrite IM_eq in HL. replace (x' <? IM) with false in HL by (symmetry; apply Z.ltb_ge; unfold IM; lia). rewrite Bool.andb_false_r in HL.
        injection HL as E1 E2 E3. subst xv c1 f1.
        zs. zs. br10 K2; try (exfalso; mlia2). zs. zs. zs.
        eapply L_L2 with (k := (k + 1)%Z); try eassumption; unfold LM; try glia. }
    assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x18' x19' x28' x29' x30' x31' : word) x1',
      finv m2 j8' -> rw_cells bsegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
      evt bsegs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 x') (Z_to_bv 64 (fst (sh_getc f) - 48)) x11' x12' x13' x14' x15' x16' x17'
                 x18' x19' (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28' x29' x30' x31')
            F (Z_to_bv 64 0x99378) fc None m2 (seg_rom bsegs))).
    { intros Hd. intros until x1'. intros FI2 FC2.
      destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l1_loop scanexp_l1_cond] in HL.
      rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. cbn [andb] in HL. injection HL as E1 E2 E3. subst xv c1 f1.
      destruct n2 as [|n2']; [discriminate HL2|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL2.
      rewrite (isdigitc_f (fst (sh_getc f))) in HL2 by lia. cbn [andb] in HL2. injection HL2 as E4 E5 E6. subst y2 c2 f2.
      destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_f (fst (sh_getc f))) in HL3 by lia.
      injection HL3 as E7 E8. subst cX fX.
      pose proof FI2 as FI'. dest_finv FI'.
      zs. zs. brfw K2; try (exfalso; mlia2).
      eapply L_end with (k := (k + 1)%Z); try eassumption; try glia. }
    clear IH HL HL2 HL3.
    pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
    destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
    - (* [comment removed for export] *)
      pose proof FC as FC0. unfold_fc2 FC.
      zs. zs. zs. br K.
      (nelim (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) 5%nat; intros STD EJ Hn Hrp Hc0).
      assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
      zs. zs. callw (eapply shgetc_callJ;
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
        | plia | plia | plia | replace (q + -80 - 2464)%Z with (q - 2544)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI | fsx ]).
      post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
      zs. zs. zs. zs. fixw2. zs. fixw2.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 x') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small x) by lia; lia).
      let v := getreg 10%Z in replace v with (Z_to_bv 64 (fst (sh_getc f) - 48)) by reflexivity.
      zs. brfw K2.
      + (* [comment removed for export] *) eapply ND; [mlia2 | mk_finv | exact FC].
      + eapply DIG; [mlia2 | mk_finv | exact FC].
    - (* [comment removed for export] *)
      pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Shgetc_lemmas.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
      unfold_fc2 FC.
      zs. zs. zs. br10 K.
      zs. zs.
      pose proof (u8ro_read bsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Shgetc_lemmas.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
      zs. cbv beta. rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
      zs. zs. zs. fixw2. zs. fixw2.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 x') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small x) by lia; lia).
      let v := getreg 10%Z in replace v with (Z_to_bv 64 (znth txt (sh_rpos f) - 48)) by reflexivity.
      zs. brfw K2.
      + eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
      + zs. eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
  Qed.

  (* [comment removed for export] *)
  Lemma L_E4 : forall m j8 (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (neg : Z),
    finv m j8 -> rw_cells bsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z ->
    scanexp_tail fuelc neg c f = Some (fR, e10) -> (0 <= neg <= 1)%Z ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 (Z_to_bv 64 (c - 58)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 c) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x992dc) fc None m (seg_rom bsegs)).
  Proof using AXS BYT Hnul Hp Q1 SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT ST0 T0 T1.
    intros until neg. intros FI FC RJ Hk Hst Hc HT Rneg.
    pose proof FI as FI'. dest_finv FI'. unfold scanexp_tail in HT.
    zs. zs. brfw K.
    - (* [comment removed for export] *)
      rewrite (isdigitc_t c) in HT by mlia2. cbn [negb] in HT.
      destruct (scanexp_l1_loop fuelc (0%Z, c, f)) as [[[xv c1] f1]|] eqn:HL1; [|discriminate HT].
      destruct (scanexp_l2_loop fuelc (xv, c1, f1)) as [[[y2 c2] f2]|] eqn:HL2; [|discriminate HT].
      destruct (scanexp_l3_loop fuelc (c2, f2)) as [[cX fX]|] eqn:HL3; [|discriminate HT].
      injection HT as E1 E2.
      zs. fixw2. zs. zs. zs. brfw K2; try (exfalso; mlia2).
      zs. zs. zs.
      eapply L_L1 with (k := k); try eassumption; unfold IM; try glia; try mlia2. all: symmetry; assumption.
    - (* [comment removed for export] *)
      rewrite (isdigitc_f c) in HT by mlia2. cbn [negb] in HT. injection HT as E1 E2.
      eapply L_ND; try eassumption; try glia. all: symmetry; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma L_C4 : forall m j8 (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (neg : Z),
    finv m j8 -> rw_cells bsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (3 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z ->
    scanexp_tail fuelc neg c (if negb (isdigitc c) && nz pok then sh_unget f else f) = Some (fR, e10) ->
    (0 <= neg <= 1)%Z -> pok <> 0%Z ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) (Z_to_bv 64 (c - 58)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 c) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x992bc) fc None m (seg_rom bsegs)).
  Proof using AXS BYT Hnul Hp Hpok Q1 SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT ST0 T0 T1.
    intros until neg. intros FI FC RJ Hk Hst Hc HT Rneg Hpk.
    replace (nz pok) with true in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [lia|reflexivity]).
    pose proof FI as FI'. dest_finv FI'.
    zs. zs. brfw K.
    - (* [comment removed for export] *)
      rewrite (isdigitc_t c) in HT by mlia2. cbn [negb andb] in HT.
      eapply L_E4; try eassumption; try glia.
    - (* [comment removed for export] *)
      rewrite (isdigitc_f c) in HT by mlia2. cbn [negb andb] in HT.
      site_facts FC RJ k c f.
      pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
      pose proof (stdio_unget f) as Hstu. rewrite Hst in Hstu.
      destruct (sh_shlim_neg f) eqn:SN.
      + rewrite (rf_unget_nop f SN) in *. unfold_fc2 FC. rewrite SN in FC. unfold M64 in FC.
        zs. zs. br01 K1. 
        eapply L_ND with (k := (k - 1)%Z); try eassumption; try glia.
        all: try (unfold scanexp_tail in HT; rewrite (isdigitc_f c) in HT by mlia2; cbn [negb] in HT; injection HT as E1 E2; symmetry; assumption).
        unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
      + rewrite (rf_unget_eq f SN) in *. unfold_fc2 FC. rewrite SN in FC. unfold M64 in FC.
        zs. zs. br10 K1.
        zs. zs. zs. zs.
        eapply L_ND with (k := (k - 1)%Z); try eassumption; try glia.
        all: try (unfold scanexp_tail in HT; rewrite (isdigitc_f c) in HT by mlia2; cbn [negb] in HT; injection HT as E1 E2; symmetry; assumption).
        1: mk_finv.
        unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
  Qed.

  (* [comment removed for export] *)
  Lemma L_SGN : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
    finv m j8 -> rw_cells bsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (c = 43 \/ c = 45)%Z ->
    scanexp_tail fuelc (b2z (c =? 45)%Z) (fst (sh_getc f))
        (if negb (isdigitc (fst (sh_getc f))) && nz pok then sh_unget (snd (sh_getc f)) else snd (sh_getc f)) = Some (fR, e10) ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 c) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x9926c) fc None m (seg_rom bsegs)).
  Proof using AXS BYT Hnul Hp Hpok Q1 SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT ST0 T0 T1.
    intros until f. intros FI FC RJ Hk Hst Hc HT.
    pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
    pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
    assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by ((nelim RJ1 3%nat; intros _ R _); exact R).
    assert (Rneg : (0 <= b2z (c =? 45)%Z <= 1)%Z) by (unfold b2z; destruct (c =? 45)%Z; lia).
    pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
    destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
    - (* [comment removed for export] *)
      pose proof FC as FC0. unfold_fc2 FC.
      zs. zs. zs. zs. br K.
      (nelim (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) 5%nat; intros STD EJ Hn Hrp Hc0).
      assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
      zs. zs. callw (eapply shgetc_callJ;
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
        | plia | plia | plia | replace (q + -80 - 2464)%Z with (q - 2544)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI | fsx ]).
      post_getc. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H; rename H into FC end.
      zs. zs. zs. fixw2.
      let v := getreg 20%Z in replace v with (Z_to_bv 64 (b2z (c =? 45)%Z)) by (destruct Hc as [-> | ->]; reflexivity).
      zs. brf K2.
      + (* [comment removed for export] *) eapply L_E4 with (k := (k + 1)%Z); try eassumption; try glia. 1: mk_finv.
        replace (nz pok) with false in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [reflexivity|mlia2]). rewrite Bool.andb_false_r in HT. exact HT.
      + eapply L_C4 with (k := (k + 1)%Z); try eassumption; try glia; try mlia2. mk_finv.
    - (* [comment removed for export] *)
      pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Shgetc_lemmas.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
      unfold_fc2 FC.
      zs. zs. zs. zs. br10 K.
      zs. zs.
      pose proof (u8ro_read bsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Shgetc_lemmas.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
      zs. cbv beta. rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
      zs. zs. fixw2.
      let v := getreg 20%Z in replace v with (Z_to_bv 64 (b2z (c =? 45)%Z)) by (destruct Hc as [-> | ->]; reflexivity).
      zs. brf K2.
      + (* [comment removed for export] *) eapply L_C4 with (k := (k + 1)%Z); try eassumption; try glia; try mlia2.
        1: mk_finv. unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
      + zs. eapply L_E4 with (k := (k + 1)%Z); try eassumption; try glia.
        1: mk_finv. 1: unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
        replace (nz pok) with false in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [reflexivity|mlia2]). rewrite Bool.andb_false_r in HT. exact HT.
  Qed.

  (* [comment removed for export] *)
  Lemma L_6c : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
    finv m j8 -> rw_cells bsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z -> c <> 43%Z ->
    (c = 45%Z -> scanexp_tail fuelc (b2z (c =? 45)%Z) (fst (sh_getc f))
        (if negb (isdigitc (fst (sh_getc f))) && nz pok then sh_unget (snd (sh_getc f)) else snd (sh_getc f)) = Some (fR, e10)) ->
    (c <> 45%Z -> scanexp_tail fuelc 0%Z c f = Some (fR, e10)) ->
    evt bsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 c) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x99264) fc None m (seg_rom bsegs)).
  Proof using AXS BYT Hnul Hp Hpok Q1 SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT ST0 T0 T1.
    intros until f. intros FI FC RJ Hk Hst Hc H43 H45 Hother.
    pose proof FI as FI'. dest_finv FI'.
    zs. zs. brfw K.
    - (* [comment removed for export] *)
      zs. zs. fixw2. zs.
      eapply L_E4 with (k := k) (neg := 0%Z); try eassumption; try glia. apply Hother. mlia2.
    - eapply L_SGN with (k := k); try eassumption; try glia. 1: right; mlia2. apply H45. mlia2.
  Qed.

  Lemma L_main : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rw_cells bsegs m0 Fp (rf_cells T p true f0 J) -> RFJ' kmin0 c0 f0 -> (1 <= kmin0)%Z -> c0 <> 0%Z ->
    bytes_at bsegs m0 T (zbytes txt) -> ssp_cells m0 canary ->
    stk bsegs m0 (q - SCANEXP_DEPTH) q -> mem_inv bsegs m0 ->
    evt bsegs POST
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SCANEXP) fc None m0 (seg_rom bsegs)).
  Proof using AXS BYT HM Hnul Hp Hpok Q1 SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT ST0 T0 T1.
    intros until t6. intros FC RJ Hk Hc0nz BY [SSP1 SSP2] ST MI.
    pose proof (munch_refl [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m0) as MU. pose proof (wmono_refl bsegs m0) as WM.
    unfold SCANEXP, SCANEXP_DEPTH in *. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length. unfold zlength in *.
    pose proof HM as HT. rewrite scanexp_eq, (surjective_pairing (sh_getc f0)) in HT. cbn beta iota zeta in HT.
    pose proof (RFI_getc T txt p J BYT Hp Hnul kmin0 c0 f0 RJ Hc0nz) as RJ1.
    pose proof (stdio_getc f0) as Hst1.
    assert (Rc' : (-1 <= fst (sh_getc f0) < 256)%Z) by ((nelim RJ1 3%nat; intros _ R _); exact R).
    (* [comment removed for export] *)
    assert (JS : forall m2 j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1,
      finv m2 j8 -> rw_cells bsegs m2 Fp (rf_cells T p true (snd (sh_getc f0)) J) ->
      (fst (sh_getc f0) = 43 \/ fst (sh_getc f0) = 45)%Z ->
      evt bsegs POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (fst (sh_getc f0))) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9926c) fc None m2 (seg_rom bsegs))).
    { intros until x1. intros FI2 FC2 H4345.
      eapply L_SGN with (k := (kmin0 + 1)%Z); try eassumption; try glia.
      replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with true in HT
        by (symmetry; destruct H4345 as [E|E]; rewrite E; reflexivity).
      rewrite (surjective_pairing (sh_getc (snd (sh_getc f0)))) in HT. cbn beta iota zeta in HT. exact HT. }
    assert (J6 : forall m2 j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1,
      finv m2 j8 -> rw_cells bsegs m2 Fp (rf_cells T p true (snd (sh_getc f0)) J) ->
      (fst (sh_getc f0) <> 43)%Z ->
      evt bsegs POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (fst (sh_getc f0))) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x99264) fc None m2 (seg_rom bsegs))).
    { intros until x1. intros FI2 FC2 H43.
      eapply L_6c with (k := (kmin0 + 1)%Z); try eassumption; try glia.
      - intros E45. replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with true in HT
          by (symmetry; rewrite E45; reflexivity).
        rewrite (surjective_pairing (sh_getc (snd (sh_getc f0)))) in HT. cbn beta iota zeta in HT. exact HT.
      - intros N45. replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with false in HT
          by (symmetry; apply Bool.orb_false_intro; apply Z.eqb_neq; assumption).
        cbn beta iota zeta in HT. exact HT. }
    site_facts FC RJ kmin0 c0 f0.
    zs. carve_frame 80%nat ST.
    do 9 zs.
    zs.
    destruct (Z.eq_dec (T + sh_rpos f0) (rf_rend T p true f0)) as [SLOW|FAST].
    - (* [comment removed for export] *)
      pose proof FC as FC0. unfold_fc2 FC.
      zs. zs. zs. zs. br K.
      (nelim (rf_getc_slow T txt p J Hp T1 kmin0 c0 f0 RJ SLOW) 5%nat; intros STD EJ Hn Hrp Hc0).
      destruct (ST0 STD) as [TXT Hpre].
      zs. zs. callw (eapply shgetc_callJ;
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
        | plia | plia | plia | replace (q + -80 - 2464)%Z with (q - 2544)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI | fsx ]).
      post_getc. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H; rename H into FC end.
      zs. zs. zs. brfw K2.
      + eapply JS; [mk_finv | exact FC | left; mlia2].
      + eapply J6; [mk_finv | exact FC | mlia2].
    - (* [comment removed for export] *)
      pose proof (rf_getc_fast_lt T txt p J Hp kmin0 c0 f0 RJ ltac:(lia) FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp kmin0 c0 f0 RJ FAST) in *. cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f0)) ltac:(apply Shgetc_lemmas.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
      unfold_fc2 FC.
      zs. zs. zs. zs. br10 K.
      zs. zs.
      pose proof (u8ro_read bsegs _ T (zbytes txt) (sh_rpos f0) _ _ BY (Shgetc_lemmas.zbytes_nth txt (sh_rpos f0) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
      zs. cbv beta. rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt (sh_rpos f0))) by lia. clear RDb.
      zs. zs. brf K2.
      + eapply J6; [mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells | mlia2].
      + zs. eapply JS; [mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells | left; mlia2].
  Qed.
End Scanexp.

Lemma scanexp_rspec : scanexp_rstmt.
Proof using .
  unfold scanexp_rstmt. intros.
  eapply L_main; eassumption.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.
