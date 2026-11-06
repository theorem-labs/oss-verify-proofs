(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32.
Import ListNotations.
Local Open Scope Z_scope.

Lemma land_mod2p : forall a b n, 0 <= n -> (Z.land a b) mod 2^n = Z.land (a mod 2^n) (b mod 2^n).
Proof.
  intros a b n Hn. rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'. intros j Hj. rewrite !Z.land_spec.
  destruct (Z.testbit a j), (Z.testbit b j), (Z.testbit (Z.ones n) j); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mask_split : forall fr k, 0 <= fr < 2^32 -> 0 <= k < 32 ->
  Z.land fr (2 ^ (k + 1) - 1) = fr mod 2 ^ (k + 1) /\
  0 <= fr mod 2 ^ (k + 1) <= fr /\ fr mod 2 ^ (k + 1) < 2 ^ (k + 1) /\
  Z.land (fr mod 2 ^ (k + 1)) (fr - fr mod 2 ^ (k + 1)) = 0 /\
  Z.lor (fr mod 2 ^ (k + 1)) (fr - fr mod 2 ^ (k + 1)) = fr /\
  (forall j, 0 <= j -> Z.testbit (fr - fr mod 2 ^ (k + 1)) j = (Z.testbit fr j && (k + 1 <=? j))%bool) /\
  (forall j, 0 <= j -> Z.testbit (fr mod 2 ^ (k + 1)) j = (Z.testbit fr j && (j <? k + 1))%bool).
Proof.
  intros fr k Hfr Hk.
  assert (Hp : 0 < 2 ^ (k + 1)) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound fr (2 ^ (k + 1)) Hp) as Hm.
  pose proof (Z.mod_le fr (2 ^ (k + 1)) ltac:(lia) Hp) as Hle.
  assert (Hhi : fr - fr mod 2 ^ (k + 1) = (fr / 2 ^ (k + 1)) * 2 ^ (k + 1)) by (pose proof (Z.div_mod fr (2 ^ (k + 1)) ltac:(lia)); lia).
  assert (TH : forall j, 0 <= j -> Z.testbit (fr - fr mod 2 ^ (k + 1)) j = (Z.testbit fr j && (k + 1 <=? j))%bool).
  { intros j Hj. rewrite Hhi. destruct (Z.lt_ge_cases j (k + 1)) as [Hlt | Hge].
    - rewrite Z.mul_pow2_bits_low by lia. replace (k + 1 <=? j) with false by (symmetry; apply Z.leb_gt; lia). symmetry. apply andb_false_r.
    - rewrite Z.mul_pow2_bits, Z.div_pow2_bits by lia. replace (j - (k + 1) + (k + 1)) with j by lia.
      replace (k + 1 <=? j) with true by (symmetry; apply Z.leb_le; lia). symmetry. apply andb_true_r. }
  assert (TL : forall j, 0 <= j -> Z.testbit (fr mod 2 ^ (k + 1)) j = (Z.testbit fr j && (j <? k + 1))%bool).
  { intros j Hj. destruct (Z.lt_ge_cases j (k + 1)) as [Hlt | Hge].
    - rewrite Z.mod_pow2_bits_low by lia. replace (j <? k + 1) with true by (symmetry; apply Z.ltb_lt; lia). symmetry. apply andb_true_r.
    - rewrite Z.mod_pow2_bits_high by lia. replace (j <? k + 1) with false by (symmetry; apply Z.ltb_ge; lia). symmetry. apply andb_false_r. }
  split; [rewrite land_ones_low by lia; reflexivity|]. split; [lia|]. split; [lia|]. split; [| split; [| split; [exact TH | exact TL]]].
  - apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, TH, TL, Z.bits_0 by lia.
    destruct (Z.testbit fr j); [| reflexivity]. cbn [andb].
    destruct (Z.lt_ge_cases j (k + 1)) as [H | H].
    + rewrite (proj2 (Z.ltb_lt _ _) H), (proj2 (Z.leb_gt _ _) H). reflexivity.
    + rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.leb_le _ _) H). reflexivity.
  - apply Z.bits_inj'. intros j Hj. rewrite Z.lor_spec, TH, TL by lia.
    destruct (Z.testbit fr j); [| reflexivity]. cbn [andb].
    destruct (Z.lt_ge_cases j (k + 1)) as [H | H].
    + rewrite (proj2 (Z.ltb_lt _ _) H), (proj2 (Z.leb_gt _ _) H). reflexivity.
    + rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.leb_le _ _) H). reflexivity.
Qed.

Lemma v_subw_w32 : forall a b, v_subw (w32 a) (w32 b) = w32 (a - b).
Proof.
  intros a b. unfold v_subw. rewrite !u_w32. unfold w32. rewrite !swrap32_eq. f_equal.
  rewrite <- (Z.add_mod_idemp_l (sx32 a - sx32 b)) by lia.
  rewrite <- (Z.add_mod_idemp_l (a - b)) by lia. f_equal. f_equal. f_equal.
  rewrite Zminus_mod, !sx32_eqmod, <- Zminus_mod. reflexivity.
Qed.

Lemma w0_w32 : w0 = w32 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma act_mask_hi : forall fr k, 0 <= fr < 2^32 -> 0 <= k < 32 ->
  v_and (w32 fr) (v_subw w0 (w32 (2 ^ (k + 1)))) = w32 (fr - fr mod 2 ^ (k + 1)).
Proof.
  intros fr k Hfr Hk.
  assert (Hp : 0 < 2 ^ (k + 1) <= 2 ^ 32) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  pose proof (mask_split fr k Hfr Hk) as (_ & R1 & R2 & _ & _ & TH & _).
  assert (TB0 : forall j, 32 <= j -> Z.testbit fr j = false).
  { intros j Hj. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|].
    split; [lia|]. apply Z.lt_le_trans with (2^32); [lia | apply Z.pow_le_mono_r; lia]. }
  rewrite w0_w32, v_subw_w32. rewrite <- (w32_mod (0 - 2 ^ (k + 1))).
  pose proof (Z.mod_pos_bound (0 - 2 ^ (k + 1)) (2^32) ltac:(lia)) as Hq.
  rewrite v_and_w32 by lia. f_equal.
  apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, TH by lia.
  destruct (Z.eq_dec (k + 1) 32) as [E32 | N32].
  - rewrite E32. change (0 - 2^32) with (-1 * 2^32). rewrite Z.mod_mul, Z.bits_0 by lia.
    destruct (Z.testbit fr j) eqn:B; [| reflexivity]. cbn [andb]. symmetry. apply Z.leb_gt.
    destruct (Z.lt_ge_cases j 32) as [H | H]; [exact H|]. exfalso. rewrite (TB0 j H) in B. discriminate B.
  - replace ((0 - 2 ^ (k + 1)) mod 2 ^ 32) with (Z.ones (32 - (k + 1)) * 2 ^ (k + 1)).
    2:{ unfold Z.ones. rewrite Z.shiftl_1_l.
        assert (E : 2 ^ (32 - (k + 1)) * 2 ^ (k + 1) = 2 ^ 32) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        replace (0 - 2 ^ (k + 1)) with ((2^32 - 2 ^ (k + 1)) + (-1) * 2^32) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia. }
    destruct (Z.lt_ge_cases j (k + 1)) as [Hlt | Hge].
    + rewrite Z.mul_pow2_bits_low by lia. replace (k + 1 <=? j) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    + rewrite Z.mul_pow2_bits, Z.testbit_ones by lia. replace (k + 1 <=? j) with true by (symmetry; apply Z.leb_le; lia).
      replace (0 <=? j - (k + 1)) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
      destruct (Z.lt_ge_cases j 32) as [H | H].
      * rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
      * rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (TB0 j H). reflexivity.
Qed.

Lemma act_mask_lo : forall fr k, 0 <= fr < 2^32 -> 0 <= k < 32 ->
  bv_unsigned (v_and (w32 fr) (v_addi (w32 (2 ^ (k + 1))) (-1))) mod 2^32 = fr mod 2 ^ (k + 1).
Proof.
  intros fr k Hfr Hk.
  assert (Hp : 0 < 2 ^ (k + 1) <= 2 ^ 32) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  pose proof (mask_split fr k Hfr Hk) as (E1 & _).
  rewrite (w32_eq (2 ^ (k + 1))), v_addi_Z, <- (ZZ_mod (sx32 (2 ^ (k + 1)) + -1)), (w32_eq fr).
  pose proof (sx32_range fr) as Hs1. pose proof (Z.mod_pos_bound (sx32 (2 ^ (k + 1)) + -1) (2^64) ltac:(lia)) as Hs2.
  rewrite v_and_Z by lia.
  rewrite uZ by (split; [apply Z.land_nonneg; lia | pose proof (land_le_left (sx32 fr) ((sx32 (2 ^ (k + 1)) + -1) mod 2 ^ 64) ltac:(lia) ltac:(lia)); lia]).
  rewrite land_mod2p by lia. rewrite sx32_eqmod, (Z.mod_small fr) by lia.
  replace (((sx32 (2 ^ (k + 1)) + -1) mod 2 ^ 64) mod 2 ^ 32) with (2 ^ (k + 1) - 1); [exact E1|].
  rewrite Z.mod_mod_divide by (exists (2^32); reflexivity).
  rewrite <- Z.add_mod_idemp_l, sx32_eqmod by lia.
  destruct (Z.eq_dec (k + 1) 32) as [E32 | N32].
  - rewrite E32, Z.mod_same by lia. reflexivity.
  - assert (2 ^ (k + 1) < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia). rewrite !Z.mod_small by lia. lia.
Qed.
