(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import PropExec SeqExec StepTac.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma testbit_high : forall n a k, 0 <= n -> 0 <= a < 2^n -> n <= k -> Z.testbit a k = false.
Proof. intros. eapply Z_testbit_high; eauto. Qed.

Lemma testbit_pow2 : forall n k, 0 <= n -> 0 <= k -> Z.testbit (2^n) k = (n =? k).
Proof.
  intros n k Hn Hk. rewrite <- (Z.shiftl_1_l n), Z.shiftl_spec by lia.
  destruct (Z.eqb_spec n k) as [->|Hne].
  - rewrite Z.sub_diag. reflexivity.
  - destruct (Z.lt_ge_cases (k - n) 0) as [Hl|Hg].
    + apply Z.testbit_neg_r. lia.
    + rewrite Z.bits_above_log2; [reflexivity | lia |]. apply Z.log2_lt_pow2; [lia|].
      apply Z.lt_le_trans with (2^1)%Z; [simpl; lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
Lemma testbit_add_high : forall a m k, 0 <= a < 2^32 -> 0 <= m -> 0 <= k < 32 ->
  Z.testbit (a + 2^32 * m) k = Z.testbit a k.
Proof.
  intros a m k Ha Hm Hk.
  rewrite <- (Z.lxor_spec a (2^32 * m) k) || idtac.
  assert (Hd : Z.land a (2^32 * m) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32) as [Hl|Hg].
    - replace (2^32 * m) with (Z.shiftl m 32) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite (testbit_high 32 a i) by lia. reflexivity. }
  rewrite (Z.add_nocarry_lxor a (2^32 * m) Hd). rewrite Z.lxor_spec.
  replace (2^32 * m) with (Z.shiftl m 32) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.shiftl_spec_low by lia. apply xorb_false_r.
Qed.

Lemma testbit_add_high2 : forall a m k, 0 <= a < 2^32 -> 0 <= m -> 32 <= k ->
  Z.testbit (a + 2^32 * m) k = Z.testbit m (k - 32).
Proof.
  intros a m k Ha Hm Hk.
  assert (Hd : Z.land a (2^32 * m) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32) as [Hl|Hg].
    - replace (2^32 * m) with (Z.shiftl m 32) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite (testbit_high 32 a i) by lia. reflexivity. }
  rewrite (Z.add_nocarry_lxor a (2^32 * m) Hd). rewrite Z.lxor_spec.
  rewrite (testbit_high 32 a k) by lia.
  replace (2^32 * m) with (Z.shiftl m 32) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.shiftl_spec_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_ones_mod : forall x k, 0 <= x -> 0 <= k -> Z.land x (2^k - 1) = x mod 2^k.
Proof. intros x k Hx Hk. rewrite <- (Z.land_ones x k) by lia. unfold Z.ones. rewrite Z.shiftl_1_l. f_equal; lia. Qed.

(* [comment removed for export] *)
Lemma land_pagemask : forall x, 0 <= x < 2^64 -> Z.land x (2^64 - 4096) = x - x mod 4096.
Proof.
  intros x Hx. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec.
  assert (Em : 2^64 - 4096 = Z.shiftl (2^52 - 1) 12) by reflexivity. rewrite Em.
  assert (Ex : x - x mod 4096 = Z.shiftl (x / 2^12) 12).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. lia. }
  rewrite Ex.
  destruct (Z.lt_ge_cases k 12) as [Hl|Hg].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia.
    destruct (Z.lt_ge_cases k 64) as [Hl2|Hg2].
    + assert (Ht : Z.testbit (2^52 - 1) (k - 12) = true).
      { replace (2^52 - 1) with (Z.ones 52) by reflexivity. apply Z.ones_spec_low. lia. }
      rewrite Ht, andb_true_r. rewrite Z.div_pow2_bits by lia. f_equal. lia.
    + rewrite (testbit_high 64 x k) by lia.
      rewrite (testbit_high 52 (x / 2^12) (k - 12)); [reflexivity | lia | | lia].
      change (2^12) with 4096. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sc_extract : forall W, 0 <= W < 2^64 ->
  Z.shiftr ((Z.shiftl W 52) mod 2^64) 58 = (W / 64) mod 64.
Proof.
  intros W HW. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace (2^64) with (2^12 * 2^52) by reflexivity.
  rewrite Z.mul_mod_distr_r by lia.
  replace (2^58) with (2^6 * 2^52) by reflexivity.
  rewrite Z.div_mul_cancel_r by lia.
  change (2^12) with 4096. change (2^6) with 64. lia.
Qed.

(* [comment removed for export] *)
Lemma sc2_extract : forall W, 0 <= W -> Z.land (Z.shiftr W 5) 126 = 2 * ((W / 64) mod 64).
Proof.
  intros W HW. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec.
  replace (2 * ((W / 64) mod 64)) with (Z.shiftl ((W / 2^6) mod 2^6) 1)
    by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia).
  assert (E126 : 126 = Z.shiftl (Z.ones 6) 1) by reflexivity. rewrite E126.
  destruct (Z.lt_ge_cases k 1) as [Hl|Hg].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia.
    destruct (Z.lt_ge_cases (k - 1) 6) as [Hl6|Hg6].
    + rewrite Z.ones_spec_low, andb_true_r by lia.
      rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.ones_spec_low, andb_true_r by lia.
      rewrite !Z.div_pow2_bits by lia. f_equal. lia.
    + rewrite Z.ones_spec_high, andb_false_r by lia.
      rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.ones_spec_high, andb_false_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma swrap32_cases : forall a, 0 <= a < 2^32 ->
  (a < 2^31 /\ bv_swrap 32 a = a) \/ (2^31 <= a /\ bv_swrap 32 a = a - 2^32).
Proof.
  intros a Ha. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.lt_ge_cases a (2^31)) as [Hl|Hg].
  - left. split; [lia|]. rewrite Z.mod_small by lia. lia.
  - right. split; [lia|]. rewrite <- (Z.mod_unique (a + 2^31) (2^32) 1 (a + 2^31 - 2^32)); lia.
Qed.

Lemma u_lw_lo : forall a, 0 <= a < 2^31 -> bv_unsigned (v_lw (Z_to_bv 64 a)) = a.
Proof.
  intros a Ha. unfold v_lw. rewrite (u_Z2bv a) by lia.
  destruct (swrap32_cases a ltac:(lia)) as [[_ E]|[? _]]; [|lia]. rewrite E. apply u_Z2bv; lia.
Qed.

Lemma u_lw_hi : forall a, 2^31 <= a < 2^32 -> bv_unsigned (v_lw (Z_to_bv 64 a)) = a + 2^32 * (2^32 - 1).
Proof.
  intros a Ha. unfold v_lw. rewrite (u_Z2bv a) by lia.
  destruct (swrap32_cases a ltac:(lia)) as [[? _]|[_ E]]; [lia|]. rewrite E.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- (Z.mod_unique (a - 2^32) (2^64) (-1) (a + 2^32 * (2^32 - 1))); lia.
Qed.

Lemma u_sllw1 : forall idx, 0 <= idx <= 31 ->
  bv_unsigned (v_sllw (Z_to_bv 64 1) (Z_to_bv 64 idx)) =
  if idx =? 31 then 2^31 + 2^32 * (2^32 - 1) else 2^idx.
Proof.
  intros idx Hi. unfold v_sllw. rewrite (u_Z2bv 1), (u_Z2bv idx) by lia. rewrite Z.mod_small by lia.
  rewrite Z.shiftl_1_l.
  assert (Hp : 0 < 2^idx <= 2^31).
  { split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
  destruct (Z.eqb_spec idx 31) as [->|Hne].
  - destruct (swrap32_cases (2^31) ltac:(simpl; lia)) as [[? _]|[_ E]]; [simpl in *; lia|]. rewrite E.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    rewrite <- (Z.mod_unique (2^31 - 2^32) (2^64) (-1) (2^31 + 2^32 * (2^32 - 1))); lia.
  - assert (2^idx < 2^31) by (apply Z.pow_lt_mono_r; lia).
    destruct (swrap32_cases (2^idx) ltac:(lia)) as [[_ E]|[? _]]; [|lia]. rewrite E. apply u_Z2bv; lia.
Qed.

Lemma land_pow2_testbit : forall a n, 0 <= a -> 0 <= n ->
  Z.land a (2^n) = 0 <-> Z.testbit a n = false.
Proof.
  intros a n Ha Hn. split.
  - intros H. apply (f_equal (fun z => Z.testbit z n)) in H.
    rewrite Z.land_spec, Z.bits_0, testbit_pow2, Z.eqb_refl, andb_true_r in H by lia. exact H.
  - intros H. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0, testbit_pow2 by lia.
    destruct (Z.eqb_spec n k) as [<-|Hne]; [rewrite H; reflexivity | apply andb_false_r].
Qed.

(* [comment removed for export] *)
Lemma mask_test_clear : forall mask idx,
  0 <= mask < 2^32 -> 0 <= idx <= 31 -> Z.testbit mask idx = false ->
  v_and (v_lw (Z_to_bv 64 mask)) (v_sllw (Z_to_bv 64 1) (Z_to_bv 64 idx)) = Z_to_bv 64 0.
Proof.
  intros mask idx Hm Hi Hb. unfold v_and. f_equal.
  rewrite u_sllw1 by lia.
  apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eqb_spec idx 31) as [->|Hne].
  - (* [comment removed for export] *)
    assert (Hlo : mask < 2^31).
    { destruct (Z.lt_ge_cases mask (2^31)) as [|Hge]; [assumption|]. exfalso.
      assert (Ht : Z.testbit mask 31 = true); [|congruence].
      apply Z.testbit_true; [lia|].
      assert (E : mask / 2^31 = 1) by (symmetry; apply Z.div_unique with (r := mask - 2^31); lia). rewrite E. reflexivity. }
    rewrite u_lw_lo by lia.
    destruct (Z.lt_ge_cases k 31) as [Hl|Hg].
    + replace (Z.testbit (2^31 + 2^32 * (2^32 - 1)) k) with false; [apply andb_false_r|].
      symmetry. replace (2^31 + 2^32 * (2^32 - 1)) with (Z.shiftl (2^33 - 1) 31) by reflexivity.
      apply Z.shiftl_spec_low. lia.
    + rewrite (testbit_high 31 mask k) by lia. reflexivity.
  - assert (Hp : 0 < 2^idx < 2^31) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
    rewrite testbit_pow2 by lia.
    destruct (Z.eqb_spec idx k) as [<-|Hnk]; [|apply andb_false_r].
    rewrite andb_true_r.
    destruct (Z.lt_ge_cases mask (2^31)) as [Hlo|Hhi].
    + rewrite u_lw_lo by lia. exact Hb.
    + rewrite u_lw_hi by lia. rewrite testbit_add_high by lia. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_andi_Z : forall x m, 0 <= x < 2^64 -> 0 <= m < 2^64 ->
  v_andi (Z_to_bv 64 x) m = Z_to_bv 64 (Z.land x m).
Proof. intros x m Hx Hm. unfold v_andi. rewrite u_Z2bv by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma v_and_Z : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  v_and (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.land x y).
Proof. intros. unfold v_and. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma v_slli_Z : forall x k, 0 <= x -> 0 <= k -> x * 2^k < 2^64 ->
  v_slli (Z_to_bv 64 x) k = Z_to_bv 64 (x * 2^k).
Proof.
  intros x k Hx Hk Hb. unfold v_slli. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  rewrite u_Z2bv by nia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma v_srli_Z : forall x k, 0 <= x < 2^64 -> 0 <= k ->
  v_srli (Z_to_bv 64 x) k = Z_to_bv 64 (x / 2^k).
Proof. intros x k Hx Hk. unfold v_srli. rewrite u_Z2bv by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma v_mul_Z : forall x y, 0 <= x -> 0 <= y -> x < 2^64 -> y < 2^64 ->
  v_mul (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x * y).
Proof. intros. unfold v_mul. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma v_add_ZZ : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof. intros. unfold v_add. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma v_sub_ZZ : forall x y, 0 <= y <= x -> x < 2^64 ->
  v_sub (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof. intros. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma c_ltu_Z : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  c_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros. unfold c_ltu, bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_mod64 : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2^64).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_mod by lia. reflexivity. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
