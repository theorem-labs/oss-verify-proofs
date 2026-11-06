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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
Module F_rscan_lib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
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
End F_rscan_lib.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_strnlen.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_shgetc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I Require IImgU.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_scanexp.
From Ltac2 Require Ltac2.
Module F_shgetc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_shgetc_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_shgetc_B.U_sread_spec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

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

Module H4S.
  Import Ltac2.
  Ltac2 prune_share () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_share1 () : unit := Control.enter prune_share.
End H4S.
Local Ltac h4_prune_share := ltac2:(H4S.prune_share1 ()).
Local Ltac share_tier := solve [ sf_unhide; h4_prune_share; Zify.zify; xlia zchecker ].
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | share_tier | tlia | split; [ tlia | exact I ] ].


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
  (* [comment removed for export] *)
Local Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Local Ltac br10 K := brf K; [ exfalso; lia | ].
Local Ltac br01 K := brf K; [ | exfalso; lia ].
(* [comment removed for export] *)
Local Ltac lia_goal_g P := lazymatch P with
  | (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
  | (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
  | @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
  | ?A /\ ?B => lia_goal_g A; lia_goal_g B | ?A \/ ?B => lia_goal_g A; lia_goal_g B | ?A -> ?B => lia_goal_g B | ~ _ => idtac
  | ?A <-> ?B => lia_goal_g A; lia_goal_g B | False => idtac | True => idtac
  end.
Local Ltac glia := lazymatch goal with |- ?G => lia_goal_g G end; lia.
Definition uflow_res (txt : list Z) (off p : Z) : Z := if (off <? p)%Z then znth txt off else -1.

Definition uflow_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p off : Z) (txt : list Z) (shend : Z) (shl shc canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (uflow_res txt off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 128, q); (Fp, Fp + 232)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' (q - 128) (q)
    /\ rw_cells usegs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) (Z_to_bv 64 M64) (T + p) shend shl shc)
    /\ bytes_at usegs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition uflow_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p off rpos rend shend : Z) (txt pre post : list Z) (mode shl shc canary : word),
  rw_cells usegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
  (mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
  rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
  bytes_at usegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk usegs m (q - 128) (q) -> (4096 <= q - 128)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 128 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 128)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv usegs m ->
  evt usegs (uflow_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p off txt shend shl shc canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 UFLOW) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shgetc_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p : Z) (f : shfile) (txt : list Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (sh_getc f))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 160, q); (Fp, Fp + 232)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' (q - 160) q
    /\ rw_cells usegs m' Fp (rf_cells T p true (snd (sh_getc f)) ssJ)
    /\ bytes_at usegs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition shgetc_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (f : shfile) (txt pre post : list Z) (canary : word),
  rw_cells usegs m Fp (rf_cells T p w f ssJ) ->
  sh_stdio f = true -> sh_n f = p -> sh_buf f = txt ->
  sh_rpos f = (if w then p else 0%Z) -> (w = false -> sh_cnt0 f = 0%Z /\ sh_shlim_neg f = false) -> (0 <= sh_cnt0 f <= sh_rpos f)%Z ->
  rtext T txt pre post -> p = zlength pre -> bytes_at usegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk usegs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 160 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 160)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv usegs m ->
  evt usegs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SHGETC) fc None m (seg_rom usegs)).
#[export] Instance U_uflow_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc.uflow_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc.uflow_spec_c_ok.
#[export] Instance U_shgetc_spec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc.shgetc_spec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_shgetc.shgetc_spec_c_ok.
End F_shgetc.

(* [comment removed for export] *)
Module F_rfile.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls F_shgetc F_rscan_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c F_shgetc.U_uflow_spec_c F_shgetc.U_shgetc_spec_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


(* [comment removed for export] *)
Definition RFJ (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
  sh_ok T txt f /\ (-1 <= c < 256)%Z /\ (0 <= sh_cnt0 f <= sh_rpos f)%Z /\
  (sh_shlim_neg f = false -> sh_cnt0 f + kmin <= sh_rpos f)%Z /\
  (sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
  (sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
                        (w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ J = ssJ)%Z.
(* [comment removed for export] *)

Open Scope bv_scope.
#[export] Instance U_shgetc_callJ_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_rfile.shgetc_callJ_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.G_rfile.shgetc_callJ_c_ok.
End F_rfile.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat StrFun FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_strnlen.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.
Import F_shgetc.
Import F_rscan_lib.
Import F_rfile.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_strnlen.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.
#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_strnlen.F_memchr.U_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_letf2_callv0_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fixunstfsi_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatsitf_callp_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_floatunsitf_callfix_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_extenddftf2_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_multf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_divtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_addtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_subtf3_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_frexpl_callq_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_signbitl_callv_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fmt_fp_lib.F_fmt_fp_calls.U_fpclassifyl_callv_c F_shgetc.U_uflow_spec_c F_shgetc.U_shgetc_spec_c F_rfile.U_shgetc_callJ_c.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.

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
(* [comment removed for export] *)
Local Ltac step ::= step2. Local Ltac stepz ::= step2.
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
Definition SCANEXP : Z := 0x20664.
Definition SCANEXP_DEPTH : Z := 240.

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

Definition scanexp_rpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p : Z) (J : rfj) (txt : list Z) (canary : word) (fR : shfile) (e10 : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' k' c',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e10) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' (q - SCANEXP_DEPTH) q
    /\ rw_cells usegs m' Fp (rf_cells T p true fR J)
    /\ RFJ T txt p true J k' c' fR /\ (1 <= k')%Z
    /\ bytes_at usegs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition scanexp_rstmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z),
  scanexp fuelc f0 pok = Some (fR, e10) ->
  rw_cells usegs m Fp (rf_cells T p true f0 J) -> RFJ T txt p true J kmin0 c0 f0 -> (1 <= kmin0)%Z -> c0 <> 0%Z ->
  (sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre) ->
  Forall (fun c => 0 <= c < 256)%Z txt -> (0 <= p < zlength txt)%Z -> znth txt p = 0%Z ->
  bytes_at usegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk usegs m (q - SCANEXP_DEPTH) q -> (4096 <= q - SCANEXP_DEPTH)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= pok <= 1)%Z -> (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv usegs m ->
  evt usegs (scanexp_rpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p J txt canary fR e10 m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCANEXP) fc None m (seg_rom usegs)).
#[export] Instance U_scanexp_rspec_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.scanexp_rspec_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_scanexp.scanexp_rspec_c_ok.
