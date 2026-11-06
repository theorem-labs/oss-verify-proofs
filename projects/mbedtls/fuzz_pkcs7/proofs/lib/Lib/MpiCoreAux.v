(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk CellsX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep. (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition sxz (u : Z) : Z := if u <? 2^31 then u else u + (2^64 - 2^32).

Lemma sxz_range : forall u, 0 <= u < 2^32 -> 0 <= sxz u < 2^64.
Proof. intros u Hu. unfold sxz. destruct (Z.ltb_spec u (2^31)); lia. Qed.

Lemma sxz_mod32 : forall u, 0 <= u < 2^32 -> sxz u mod 2^32 = u.
Proof.
  intros u Hu. unfold sxz. destruct (Z.ltb_spec u (2^31)). apply Z.mod_small; lia.
  replace (u + (2^64 - 2^32)) with (u + (2^32 - 1) * 2^32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Lemma sxz_ltb : forall u v, 0 <= u < 2^32 -> 0 <= v < 2^32 -> (sxz u <? sxz v) = (u <? v).
Proof.
  intros u v Hu Hv. unfold sxz.
  destruct (Z.ltb_spec u v); destruct (Z.ltb_spec u (2^31)); destruct (Z.ltb_spec v (2^31));
    first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.

Lemma sxz_eqb : forall u v, 0 <= u < 2^32 -> 0 <= v < 2^32 -> (sxz u =? sxz v) = (u =? v).
Proof.
  intros u v Hu Hv. unfold sxz.
  destruct (Z.eqb_spec u v); destruct (Z.ltb_spec u (2^31)); destruct (Z.ltb_spec v (2^31));
    first [apply Z.eqb_eq; lia | apply Z.eqb_neq; lia].
Qed.

Lemma swrap32_mod64 : forall z, (bv_swrap 32 z) mod 2^64 = sxz (z mod 2^32).
Proof.
  intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31).
  pose proof (Z.mod_pos_bound z (2^32) ltac:(lia)) as Hz.
  set (u := z mod 2^32) in *.
  replace ((z + 2^31) mod 2^32) with ((u + 2^31) mod 2^32)
    by (subst u; rewrite Zplus_mod_idemp_l; reflexivity).
  unfold sxz. destruct (Z.ltb_spec u (2^31)).
  - rewrite (Z.mod_small (u + 2^31)) by lia. replace (u + 2^31 - 2^31) with u by lia. apply Z.mod_small. lia.
  - replace (u + 2^31) with ((u - 2^31) + 1 * 2^32) by lia. rewrite Z.mod_add, (Z.mod_small (u - 2^31)) by lia.
    replace (u - 2^31 - 2^31) with ((u + (2^64 - 2^32)) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia.
    apply Z.mod_small. lia.
Qed.

Lemma bv_unsigned_sx32 : forall w : word, bv_unsigned (sx32 w) = sxz (bv_unsigned w mod 2^32).
Proof.
  intros w. unfold sx32. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64). apply swrap32_mod64.
Qed.

Lemma sxz_add_mod32 : forall u c, 0 <= u < 2^32 -> (sxz u + c) mod 2^32 = (u + c) mod 2^32.
Proof.
  intros u c Hu. unfold sxz. destruct (Z.ltb_spec u (2^31)); [reflexivity|].
  replace (u + (2^64 - 2^32) + c) with (u + c + (2^32 - 1) * 2^32) by lia. apply Z.mod_add. lia.
Qed.

Lemma sxz_add_mod32_r : forall x u, 0 <= u < 2^32 -> (x + sxz u) mod 2^32 = (x + u) mod 2^32.
Proof. intros x u Hu. rewrite (Z.add_comm x (sxz u)), sxz_add_mod32, Z.add_comm by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma core_add_carry : forall (wa wb : word) (c : Z), 0 <= c <= 1 ->
  0 <= Z.b2z (bv_swrap 32 (bv_swrap 32 (bv_unsigned (sx32 wa) + c) mod 18446744073709551616 + bv_unsigned (sx32 wb)) mod 18446744073709551616
              <? bv_swrap 32 (bv_unsigned (sx32 wa) + c) mod 18446744073709551616)
       + Z.b2z (bv_swrap 32 (bv_unsigned (sx32 wa) + c) mod 18446744073709551616 <? bv_unsigned (sx32 wa)) <= 1.
Proof.
  intros wa wb c Hc. change 18446744073709551616 with (2^64).
  pose proof (Z.mod_pos_bound (bv_unsigned wa) (2^32) ltac:(lia)) as Ra.
  pose proof (Z.mod_pos_bound (bv_unsigned wb) (2^32) ltac:(lia)) as Rb.
  rewrite !bv_unsigned_sx32. set (a := bv_unsigned wa mod 2^32) in *. set (b := bv_unsigned wb mod 2^32) in *.
  rewrite !swrap32_mod64. rewrite (sxz_add_mod32 a c) by lia.
  pose proof (Z.mod_pos_bound (a + c) (2^32) ltac:(lia)) as Rt. set (t := (a + c) mod 2^32) in *.
  rewrite (sxz_add_mod32_r (sxz t) b), (sxz_add_mod32 t b) by lia.
  pose proof (Z.mod_pos_bound (t + b) (2^32) ltac:(lia)) as Rt2.
  rewrite !sxz_ltb by lia.
  destruct (Z.ltb_spec t a); destruct (Z.ltb_spec ((t + b) mod 2^32) t); cbn [Z.b2z]; lia.
Qed.

(* [comment removed for export] *)
Lemma core_add_carry_u : forall (wa wb : word) (c : Z), 0 <= c <= 1 ->
  0 <= Z.b2z (bv_swrap 32 (bv_unsigned (sx32 wb) + bv_swrap 32 (bv_unsigned (sx32 wa) + c) mod 18446744073709551616) mod 18446744073709551616
              <? bv_unsigned (sx32 wb))
       + Z.b2z (bv_swrap 32 (bv_unsigned (sx32 wa) + c) mod 18446744073709551616 <? bv_unsigned (sx32 wa)) <= 1.
Proof.
  intros wa wb c Hc. change 18446744073709551616 with (2^64).
  pose proof (Z.mod_pos_bound (bv_unsigned wa) (2^32) ltac:(lia)) as Ra.
  pose proof (Z.mod_pos_bound (bv_unsigned wb) (2^32) ltac:(lia)) as Rb.
  rewrite !bv_unsigned_sx32. set (a := bv_unsigned wa mod 2^32) in *. set (b := bv_unsigned wb mod 2^32) in *.
  rewrite !swrap32_mod64. rewrite (sxz_add_mod32 a c) by lia.
  pose proof (Z.mod_pos_bound (a + c) (2^32) ltac:(lia)) as Rt. set (t := (a + c) mod 2^32) in *.
  rewrite (sxz_add_mod32_r (sxz b) t), (sxz_add_mod32 b t) by lia.
  pose proof (Z.mod_pos_bound (b + t) (2^32) ltac:(lia)) as Rt2.
  rewrite !sxz_ltb by lia.
  destruct (Z.ltb_spec t a); destruct (Z.ltb_spec ((b + t) mod 2^32) b); cbn [Z.b2z]; lia.
Qed.

(* [comment removed for export] *)
Lemma core_sub_borrow : forall (wa wb : word) (c : Z), 0 <= c <= 1 ->
  0 <= Z.b2z (bv_swrap 32 (bv_unsigned (sx32 wa) - c) mod 18446744073709551616 <? bv_unsigned (sx32 wb))
       + Z.b2z (bv_unsigned (sx32 wa) <? c) <= 1.
Proof.
  intros wa wb c Hc. change 18446744073709551616 with (2^64).
  pose proof (Z.mod_pos_bound (bv_unsigned wa) (2^32) ltac:(lia)) as Ra.
  pose proof (Z.mod_pos_bound (bv_unsigned wb) (2^32) ltac:(lia)) as Rb.
  rewrite !bv_unsigned_sx32. set (a := bv_unsigned wa mod 2^32) in *. set (b := bv_unsigned wb mod 2^32) in *.
  rewrite !swrap32_mod64.
  replace ((sxz a - c) mod 2^32) with ((a - c) mod 2^32)
    by (unfold sxz; destruct (Z.ltb_spec a (2^31)); [reflexivity|];
        replace (a + (2^64 - 2^32) - c) with (a - c + (2^32 - 1) * 2^32) by lia; symmetry; apply Z.mod_add; lia).
  pose proof (Z.mod_pos_bound (a - c) (2^32) ltac:(lia)) as Rt.
  rewrite sxz_ltb by lia.
  assert (E : (sxz a <? c) = (a <? c)).
  { unfold sxz. destruct (Z.ltb_spec a (2^31)); [reflexivity|]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. symmetry. apply Z.ltb_ge. lia. }
  rewrite E.
  destruct (Z.ltb_spec ((a - c) mod 2^32) b); destruct (Z.ltb_spec a c); cbn [Z.b2z]; lia.
Qed.

(* [comment removed for export] *)
Lemma swrap32_of_small : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite bv_swrap_small; [reflexivity|]. unfold bv_half_modulus, bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma flag_nz : forall A, 0 < A -> Z.b2z (0 <? A) = 1.
Proof. intros A HA. rewrite (proj2 (Z.ltb_lt 0 A) HA). reflexivity. Qed.

Lemma land_3_mod' : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_7_mod' : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma flag_al4_nz : forall A, A mod 4 = 0 -> 0 < A -> Z.land (Z.b2z (Z.land A 3 <? 1)) (Z.b2z (0 <? A)) = 1.
Proof. intros A HA HP. rewrite land_3_mod', HA, (proj2 (Z.ltb_lt 0 A) HP). reflexivity. Qed.
Lemma flag_al8_nz : forall A, A mod 8 = 0 -> 0 < A -> Z.land (Z.b2z (Z.land A 7 <? 1)) (Z.b2z (0 <? A)) = 1.
Proof. intros A HA HP. rewrite land_7_mod', HA, (proj2 (Z.ltb_lt 0 A) HP). reflexivity. Qed.

(* [comment removed for export] *)
Ltac ub_decide K :=
  rewrite ?unsigned_lit in K by lia;
  rewrite ?land_7_mod', ?land_3_mod' in K;
  rewrite ?Z.shiftr_div_pow2 in K by lia;
  change (2^61) with 2305843009213693952 in K; change (2^62) with 4611686018427387904 in K; change (2^63) with 9223372036854775808 in K;
  repeat match type of K with
  | context [?x <? ?y] =>
      first [ replace (x <? y) with true in K by (symmetry; apply Z.ltb_lt; lia)
            | replace (x <? y) with false in K by (symmetry; apply Z.ltb_ge; lia) ]
  | context [?x =? ?y] =>
      first [ replace (x =? y) with true in K by (symmetry; apply Z.eqb_eq; lia)
            | replace (x =? y) with false in K by (symmetry; apply Z.eqb_neq; lia) ]
  end;
  cbn [Z.b2z Z.land Z.lor Z.lxor negb andb orb Z.eqb Z.ltb Pos.land] in K.

Ltac ub_kill K := exfalso; ub_decide K; first [ lia | discriminate K | congruence ].

Lemma b2z_range : forall b, 0 <= Z.b2z b <= 1.
Proof. intros [|]; cbn; lia. Qed.
Lemma b2z_nonneg : forall b, 0 <= Z.b2z b. Proof. intros b; pose proof (b2z_range b); lia. Qed.
Lemma b2z_le_1 : forall b, Z.b2z b <= 1. Proof. intros b; pose proof (b2z_range b); lia. Qed.

(* [comment removed for export] *)
Lemma land_le_l : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof.
  intros a b Ha Hb.
  pose proof (Z.lor_ldiff_and a b) as E.
  pose proof (Z.add_lor_land (Z.ldiff a b) (Z.land a b)) as S.
  replace (Z.land (Z.ldiff a b) (Z.land a b)) with 0 in S
    by (symmetry; apply Z.bits_inj'; intros n Hn; rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0;
        destruct (Z.testbit a n), (Z.testbit b n); reflexivity).
  rewrite E in S. pose proof (Z.ldiff_nonneg a b) as D. lia.
Qed.

Lemma lor_ge_r : forall a b, 0 <= a -> 0 <= b -> b <= Z.lor a b.
Proof.
  intros a b Ha Hb. pose proof (Z.add_lor_land a b). pose proof (land_le_l a b Ha Hb). lia.
Qed.

Lemma lor_lt_pow2 : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros a b n Ha Hb. split. apply Z.lor_nonneg; lia.
  destruct (Z.eq_dec a 0) as [->|]. rewrite Z.lor_0_l. lia.
  destruct (Z.eq_dec b 0) as [->|]. rewrite Z.lor_0_r. lia.
  assert (0 <= n) by (destruct (Z.le_gt_cases 0 n); [lia|]; rewrite Z.pow_neg_r in Ha by lia; lia).
  assert (P : 0 < Z.lor a b).
  { pose proof (proj2 (Z.lor_nonneg a b) (conj (proj1 Ha) (proj1 Hb))).
    destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
  apply (proj1 (Z.log2_lt_pow2 (Z.lor a b) n P)) || apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n P)).
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Definition ct_mask (z : Z) : Z := if z =? 0 then 0 else 2^64 - 1.

Lemma ct_bool_tail : forall v, 0 <= v < 2^32 ->
  Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.lor ((0 - Z.shiftr v 1) mod 18446744073709551616)
                                                   ((0 - v) mod 18446744073709551616)))) 63)
  = Z_to_bv 64 (ct_mask v).
Proof.
  intros v Hv. unfold ct_mask. destruct (Z.eqb_spec v 0) as [->|NE].
  - vm_compute. reflexivity.
  - change 18446744073709551616 with (2^64).
    rewrite !Z.shiftr_div_pow2 by lia. change (2^1) with 2.
    pose proof (Z.mod_pos_bound (0 - v / 2) (2^64) ltac:(lia)) as Ra.
    set (a := (0 - v / 2) mod 2^64) in *.
    assert (Hb : (0 - v) mod 2^64 = 2^64 - v).
    { replace (0 - v) with ((2^64 - v) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    rewrite Hb.
    pose proof (lor_ge_r a (2^64 - v) ltac:(lia) ltac:(lia)) as L1.
    pose proof (lor_lt_pow2 a (2^64 - v) 64 ltac:(lia) ltac:(lia)) as L2.
    set (L := Z.lor a (2^64 - v)) in *.
    rewrite zb_signed. rewrite (unsigned_lit L) by (clear -L2; lia).
    destruct (Z.ltb_spec L (2^63)); [lia|].
    replace ((L - 2^64) / 2^63) with (-1) by (Z.div_mod_to_equations; lia).
    apply Z_to_bv_eqm. reflexivity.
Qed.

(* [comment removed for export] *)
Definition limbs_zero (ws : list word) (n : Z) : Prop :=
  forall i w, 0 <= i < n -> nth_error ws (Z.to_nat i) = Some w -> bv_unsigned w mod 2^32 = 0.

Lemma limbs_zero_0 : forall ws, limbs_zero ws 0.
Proof. intros ws i w Hi; lia. Qed.

Lemma lor_mod32 : forall x y, 0 <= x -> 0 <= y -> (Z.lor x y) mod 2^32 = Z.lor (x mod 2^32) (y mod 2^32).
Proof.
  intros x y Hx Hy. change (2^32) with (2^32). rewrite <- !(Z.land_ones _ 32) by lia. apply Z.land_lor_distr_l.
Qed.

(* [comment removed for export] *)
Lemma limbs_zero_step : forall ws i (w acc : word),
  0 <= i -> nth_error ws (Z.to_nat i) = Some w ->
  (bv_unsigned acc mod 2^32 = 0 <-> limbs_zero ws i) ->
  (Z.lor (bv_unsigned (sx32 w)) (bv_unsigned acc)) mod 2^32 = 0 <-> limbs_zero ws (i + 1).
Proof.
  intros ws i w acc Hi Hn IHz.
  pose proof (bv_unsigned_in_range 64 acc) as Ra. pose proof (bv_unsigned_in_range 64 (sx32 w)) as Rw. unfold bv_modulus in *.
  rewrite lor_mod32 by lia. rewrite Z.lor_eq_0_iff.
  rewrite bv_unsigned_sx32, sxz_mod32 by (apply Z.mod_pos_bound; lia).
  split.
  - intros [Hw Hacc] j wj Hj Hnj. destruct (Z.eq_dec j i) as [->|].
    + rewrite Hn in Hnj. inversion Hnj; subst. exact Hw.
    + apply (proj1 IHz Hacc j wj); [lia| exact Hnj].
  - intros Hz. split.
    + apply (Hz i w); [lia | exact Hn].
    + apply (proj2 IHz). intros j wj Hj Hnj. apply (Hz j wj); [lia| exact Hnj].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Notation srlw_z k s := (bv_swrap 32 (Z.shiftr (bv_wrap 32 s) k) mod 18446744073709551616) (only parsing).

Lemma srlw_z_eq : forall k s, 1 <= k -> srlw_z k s = Z.shiftr (s mod 2^32) k.
Proof.
  intros k s Hk. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32).
  pose proof (Z.mod_pos_bound s (2^32) ltac:(lia)) as R.
  assert (R2 : 0 <= Z.shiftr (s mod 2^32) k < 2^31).
  { rewrite Z.shiftr_div_pow2 by lia. split. apply Z.div_pos; lia.
    apply Z.div_lt_upper_bound. lia. apply (Z.lt_le_trans _ (2^32)). lia.
    replace (2^32) with (2^1 * 2^31) by reflexivity. apply Z.mul_le_mono_nonneg_r. lia. apply Z.pow_le_mono_r; lia. }
  rewrite swrap32_of_small by lia. apply Z.mod_small. lia.
Qed.

Definition smear_val (b : Z) : Z := if b =? 31 then 2^64 - 1 else 2^(b+1) - 1.

Definition smear_inv (b j s : Z) : Prop :=
  0 <= s < 2^64
  /\ (forall i, 0 <= i -> b + 1 - j <= i <= b -> Z.testbit s i = true)
  /\ (forall i, b < i < 32 -> Z.testbit s i = false)
  /\ (forall i, 32 <= i < 64 -> Z.testbit s i = (b =? 31)).

Lemma testbit_high_false : forall s i, 0 <= s < 2^64 -> 64 <= i -> Z.testbit s i = false.
Proof.
  intros s i Hs Hi. destruct (Z.eq_dec s 0) as [->|]. apply Z.bits_0.
  apply Z.bits_above_log2; [lia|]. apply (Z.le_lt_trans _ 63); [|lia].
  apply Z.lt_succ_r. change (Z.succ 63) with 64. apply Z.log2_lt_pow2; lia.
Qed.

Lemma smear_step : forall b j k s, 0 <= b <= 31 -> 1 <= j -> 1 <= k <= j ->
  smear_inv b j s -> smear_inv b (j + k) (Z.lor s (srlw_z k s)).
Proof.
  intros b j k s Hb Hj Hk (R & T1 & T0 & U).
  rewrite srlw_z_eq by lia.
  pose proof (Z.mod_pos_bound s (2^32) ltac:(lia)) as Rm.
  assert (Rs : 0 <= Z.shiftr (s mod 2^32) k < 2^64).
  { rewrite Z.shiftr_div_pow2 by lia. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound. lia. nia. }
  assert (BIT : forall i, 0 <= i -> Z.testbit (Z.lor s (Z.shiftr (s mod 2 ^ 32) k)) i
                                    = (Z.testbit s i || ((i + k <? 32) && Z.testbit s (i + k)))%bool).
  { intros i Hi. rewrite Z.lor_spec, Z.shiftr_spec, Z.testbit_mod_pow2 by lia. reflexivity. }
  split; [apply lor_lt_pow2; lia|]. split; [|split].
  - intros i Hi Hr. rewrite BIT by lia.
    destruct (Z.le_gt_cases (b + 1 - j) i).
    + rewrite T1 by lia. reflexivity.
    + rewrite (T1 (i + k)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite Bool.orb_true_r. reflexivity.
  - intros i Hi. rewrite BIT by lia. rewrite T0 by lia.
    destruct (Z.ltb_spec (i + k) 32); [| reflexivity]. rewrite T0 by lia. reflexivity.
  - intros i Hi. rewrite BIT by lia. rewrite U by lia.
    destruct (Z.ltb_spec (i + k) 32); [lia|]. rewrite Bool.andb_false_l, Bool.orb_false_r. reflexivity.
Qed.

Lemma testbit_split_high : forall l h n m, 0 <= n -> 0 <= m -> 0 <= l < 2^n ->
  Z.testbit (l + h * 2^n) (n + m) = Z.testbit h m.
Proof.
  intros l h n m Hn Hm Hl. replace (n + m) with (m + n) by lia. rewrite <- Z.div_pow2_bits by lia.
  f_equal. rewrite Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma testbit_split_low : forall l h n m, 0 <= n -> m < n -> 0 <= l < 2^n ->
  Z.testbit (l + h * 2^n) m = Z.testbit l m.
Proof.
  intros l h n m Hn Hm Hl. rewrite <- (Z.mod_pow2_bits_low (l + h * 2^n) n m) by lia.
  f_equal. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma smear_base : forall (w : word) x b, x = bv_unsigned w mod 2^32 -> x <> 0 -> b = Z.log2 x ->
  0 <= b <= 31 /\ smear_inv b 1 (bv_unsigned (sx32 w)).
Proof.
  intros w x b Hx Hnz Hb.
  pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)) as R. rewrite <- Hx in R.
  assert (Bb : 0 <= b <= 31).
  { subst b. split. apply Z.log2_nonneg. apply Z.lt_succ_r. change (Z.succ 31) with 32. apply Z.log2_lt_pow2; lia. }
  split; [exact Bb|].
  rewrite bv_unsigned_sx32, <- Hx.
  assert (TOP : Z.testbit x 31 = (b =? 31)).
  { destruct (Z.eqb_spec b 31). rewrite <- e, Hb. apply Z.bit_log2. lia. apply Z.bits_above_log2; lia. }
  assert (SX : sxz x = x + (if b =? 31 then Z.ones 32 else 0) * 2^32).
  { unfold sxz. destruct (Z.eqb_spec b 31) as [E|E].
    - assert (2^31 <= x) by (first [apply (proj2 (Z.log2_le_pow2 x 31 ltac:(lia))) | apply (proj1 (Z.log2_le_pow2 x 31 ltac:(lia)))]; lia).
      destruct (Z.ltb_spec x (2^31)); [lia|]. reflexivity.
    - assert (x < 2^31) by (first [apply (proj1 (Z.log2_lt_pow2 x 31 ltac:(lia))) | apply (proj2 (Z.log2_lt_pow2 x 31 ltac:(lia)))]; lia).
      destruct (Z.ltb_spec x (2^31)); [lia|lia]. }
  split. { apply sxz_range. lia. }
  rewrite SX. split; [|split].
  - intros i Hi Hr. assert (i = b) by lia. subst i.
    rewrite (testbit_split_low x _ 32 b) by lia. rewrite Hb. apply Z.bit_log2. lia.
  - intros i Hi. rewrite (testbit_split_low x _ 32 i) by lia. apply Z.bits_above_log2; lia.
  - intros i Hi. replace i with (32 + (i - 32)) by lia. rewrite (testbit_split_high x _ 32 (i - 32)) by lia.
    destruct (b =? 31). rewrite Z.testbit_ones_nonneg by lia. apply Z.ltb_lt. lia. apply Z.bits_0.
Qed.

Lemma smear_final : forall b j s, 0 <= b <= 31 -> b + 1 <= j -> smear_inv b j s -> s = smear_val b.
Proof.
  intros b j s Hb Hj (R & T1 & T0 & U). unfold smear_val.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.eqb_spec b 31) as [E|E].
  - replace (2^64 - 1) with (Z.ones 64) by reflexivity. rewrite Z.testbit_ones_nonneg by lia.
    destruct (Z.lt_ge_cases i 64).
    + rewrite (proj2 (Z.ltb_lt i 64)) by lia.
      destruct (Z.lt_ge_cases i 32). apply T1; lia. rewrite U by lia. first [reflexivity | apply Z.eqb_eq; exact E].
    + rewrite (proj2 (Z.ltb_ge i 64)) by lia. apply testbit_high_false; lia.
  - replace (2^(b+1) - 1) with (Z.ones (b + 1)) by (rewrite Z.ones_equiv; lia). rewrite Z.testbit_ones_nonneg by lia.
    destruct (Z.le_gt_cases i b).
    + rewrite (proj2 (Z.ltb_lt i (b+1))) by lia. apply T1; lia.
    + rewrite (proj2 (Z.ltb_ge i (b+1))) by lia.
      destruct (Z.lt_ge_cases i 32). apply T0; lia.
      destruct (Z.lt_ge_cases i 64). rewrite U by lia. first [reflexivity | apply Z.eqb_neq; exact E]. apply testbit_high_false; lia.
Qed.

(* [comment removed for export] *)
Lemma smear_chain : forall (w : word) x b, x = bv_unsigned w mod 2^32 -> x <> 0 -> b = Z.log2 x ->
  let X := bv_unsigned (sx32 w) in
  let s1 := Z.lor X (srlw_z 1 X) in let s2 := Z.lor s1 (srlw_z 2 s1) in
  let s3 := Z.lor s2 (srlw_z 4 s2) in let s4 := Z.lor s3 (srlw_z 8 s3) in
  Z.lor s4 (srlw_z 16 s4) = smear_val b /\ 0 <= b <= 31.
Proof.
  intros w x b Hx Hnz Hb. destruct (smear_base w x b Hx Hnz Hb) as [Bb I1].
  pose proof (smear_step b 1 1 _ Bb ltac:(lia) ltac:(lia) I1) as I2.
  pose proof (smear_step b 2 2 _ Bb ltac:(lia) ltac:(lia) I2) as I4.
  pose proof (smear_step b 4 4 _ Bb ltac:(lia) ltac:(lia) I4) as I8.
  pose proof (smear_step b 8 8 _ Bb ltac:(lia) ltac:(lia) I8) as I16.
  pose proof (smear_step b 16 16 _ Bb ltac:(lia) ltac:(lia) I16) as I32.
  split; [|exact Bb]. eapply smear_final; [exact Bb| |exact I32]. lia.
Qed.

(* [comment removed for export] *)
Lemma enum32 : forall (P : Z -> Prop), P 0 -> P 1 -> P 2 -> P 3 -> P 4 -> P 5 -> P 6 -> P 7 -> P 8 -> P 9 -> P 10 -> P 11 -> P 12 -> P 13 -> P 14 -> P 15 -> P 16 -> P 17 -> P 18 -> P 19 -> P 20 -> P 21 -> P 22 -> P 23 -> P 24 -> P 25 -> P 26 -> P 27 -> P 28 -> P 29 -> P 30 -> P 31 -> forall b, 0 <= b <= 31 -> P b.
Proof.
  intros P H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 b Hb.
  assert (E : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/ b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23 \/ b = 24 \/ b = 25 \/ b = 26 \/ b = 27 \/ b = 28 \/ b = 29 \/ b = 30 \/ b = 31) by lia.
  repeat (destruct E as [E|E]; [subst b; assumption|]). subst b; assumption.
Qed.

(* [comment removed for export] *)
Ltac get_x10 R := lazymatch R with TNode _ None (TNode _ (Some _) (TNode (TNode _ (Some ?x) _) (Some _) _)) => x end.

Lemma sxz_zero_iff : forall u, 0 <= u < 2^32 -> (sxz u = 0 <-> u = 0).
Proof. intros u Hu. unfold sxz. destruct (Z.ltb_spec u (2^31)); lia. Qed.

(* [comment removed for export] *)
Lemma evt_state_rw : forall segs P ms ms', ms = ms' -> evt segs P ms' -> evt segs P ms.
Proof. intros; subst; assumption. Qed.



Lemma swrap32_signed_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite bv_swrap_small; [reflexivity|]. unfold bv_half_modulus, bv_modulus. cbn. lia. Qed.

Lemma signed_lit_small : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  destruct (Z.lt_ge_cases z 0).
  - rewrite <- (Z.mod_add z 1 (2^64)) by lia. rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec (z + 1 * 2^64) (2^63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2^63)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u32arr_ro : forall segs m A ws, u32arr segs m A ws -> bytes_at segs m A (u32s ws).
Proof. intros segs m A ws [Hb _]. exact Hb. Qed.

Lemma u32ro_read : forall segs m A ws (i : Z) w a,
  bytes_at segs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 4 * i) ->
  ov_read_bytes segs m a 4 = Some (le4 w).
Proof.
  intros segs m A ws i w a Hb Hn Hi ->.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (4 * i)%Z with (Z.of_nat (4 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !app_length, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
  rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u32ro_bound : forall segs m A ws, bytes_at segs m A (u32s ws) -> 0 <= A /\ A + 4 * Z.of_nat (length ws) <= 2^64.
Proof. intros segs m A ws Hb. pose proof (bytes_at_bound _ _ _ _ Hb). rewrite u32s_length in H. lia. Qed.

Lemma u32ro_transport : forall segs W m m' A ws,
  bytes_at segs m A (u32s ws) -> munch W m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> bytes_at segs m' A (u32s ws).
Proof. intros segs W m m' A ws Hb MU Hd. eapply bytes_at_transport; eauto. rewrite u32s_length, Nat2Z.inj_mul. exact Hd. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition limb32 (ws : list word) (i : nat) : Z := bv_unsigned (nth i ws (Z_to_bv 64 0)) mod 2^32.
Definition lval (ws : list word) (n : Z) : Z := limbs_val (firstn (Z.to_nat n) ws).
(* [comment removed for export] *)
Definition w32 (w : word) : Z := bv_unsigned w mod 2^32.
Lemma w32_range : forall w, 0 <= w32 w < 2^32.
Proof. intros. unfold w32. apply Z.mod_pos_bound. lia. Qed.

Lemma limb32_range : forall ws i, 0 <= limb32 ws i < 2^32.
Proof. intros. unfold limb32. apply Z.mod_pos_bound. lia. Qed.

Lemma limb32_nth_error : forall ws i w, nth_error ws i = Some w -> limb32 ws i = w32 w.
Proof. intros ws i w H. unfold limb32, w32. rewrite (nth_error_nth _ _ _ H). reflexivity. Qed.

Lemma limb32_past : forall ws i, (length ws <= i)%nat -> limb32 ws i = 0.
Proof. intros ws i H. unfold limb32. rewrite nth_overflow by exact H. reflexivity. Qed.

Lemma limb32_upd_same : forall ws i v, (i < length ws)%nat -> limb32 (upd ws i v) i = w32 v.
Proof. intros. apply limb32_nth_error. apply nth_error_upd_same. assumption. Qed.

Lemma limb32_upd_other : forall ws i j v, i <> j -> limb32 (upd ws i v) j = limb32 ws j.
Proof.
  intros ws i j v Hij. unfold limb32.
  destruct (nth_error ws j) as [w|] eqn:E.
  - rewrite (nth_error_nth _ _ _ E). erewrite nth_error_nth; [reflexivity|]. rewrite nth_error_upd_other; assumption.
  - pose proof (proj1 (nth_error_None _ _) E). rewrite !nth_overflow; [reflexivity| lia | rewrite upd_length; lia].
Qed.

Lemma limbs_val_nonneg : forall ws, 0 <= limbs_val ws.
Proof. induction ws as [|w ws IH]; cbn; [lia|]. pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)). lia. Qed.

Lemma limbs_val_bound : forall ws, limbs_val ws < 2^(32 * Z.of_nat (length ws)).
Proof.
  induction ws as [|w ws IH]; cbn [limbs_val length]; [cbn; lia|].
  pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)).
  replace (32 * Z.of_nat (S (length ws))) with (32 + 32 * Z.of_nat (length ws)) by lia.
  rewrite Z.pow_add_r by lia. pose proof (limbs_val_nonneg ws). nia.
Qed.

Lemma limbs_val_app : forall a b, limbs_val (a ++ b) = limbs_val a + 2^(32 * Z.of_nat (length a)) * limbs_val b.
Proof.
  induction a as [|w a IH]; intros b; cbn [limbs_val app length].
  - cbn. lia.
  - rewrite IH. replace (32 * Z.of_nat (S (length a))) with (32 + 32 * Z.of_nat (length a)) by lia.
    rewrite Z.pow_add_r by lia. lia.
Qed.

Lemma lval_nonpos : forall ws n, n <= 0 -> lval ws n = 0.
Proof. intros ws n H. unfold lval. replace (Z.to_nat n) with 0%nat by lia. reflexivity. Qed.
Lemma lval_0 : forall ws, lval ws 0 = 0.
Proof. intros; apply lval_nonpos; lia. Qed.

Lemma firstn_S_snoc : forall {X} (l : list X) k (d : X),
  (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l d].
Proof.
  intros X l. induction l as [|x l IH]; intros [|k] d H; cbn in H |- *; try lia; [reflexivity|].
  rewrite (IH k d) by lia. reflexivity.
Qed.

Lemma lval_succ : forall ws i, 0 <= i -> lval ws (i + 1) = lval ws i + 2^(32 * i) * limb32 ws (Z.to_nat i).
Proof.
  intros ws i Hi. unfold lval. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length ws)) as [L|G].
  - rewrite (firstn_S_snoc ws (Z.to_nat i) (Z_to_bv 64 0) L), limbs_val_app. cbn [limbs_val].
    rewrite firstn_length_le by lia. replace (Z.of_nat (Z.to_nat i)) with i by lia. unfold limb32. lia.
  - rewrite !firstn_all2 by lia. rewrite limb32_past by lia. lia.
Qed.

Lemma lval_range : forall ws n, 0 <= n -> 0 <= lval ws n < 2^(32 * n).
Proof.
  intros ws n Hn. unfold lval. split; [apply limbs_val_nonneg|].
  eapply Z.lt_le_trans; [apply limbs_val_bound|]. apply Z.pow_le_mono_r; [lia|].
  rewrite firstn_length. lia.
Qed.

Lemma lval_ext : forall ws ws' n, firstn (Z.to_nat n) ws = firstn (Z.to_nat n) ws' -> lval ws n = lval ws' n.
Proof. intros ws ws' n E. unfold lval. rewrite E. reflexivity. Qed.

Lemma firstn_upd_ge : forall {X} (l : list X) j v k, (k <= j)%nat -> firstn k (upd l j v) = firstn k l.
Proof.
  intros X l. induction l as [|x l IH]; intros [|j] v [|k] H; cbn; try reflexivity; try lia.
  rewrite IH by lia. reflexivity.
Qed.
Lemma skipn_upd_lt : forall {X} (l : list X) j v k, (j < k)%nat -> skipn k (upd l j v) = skipn k l.
Proof.
  intros X l. induction l as [|x l IH]; intros [|j] v [|k] H; cbn; try reflexivity; try lia.
  rewrite IH by lia. reflexivity.
Qed.

Lemma lval_upd_ge : forall ws j v n, (Z.to_nat n <= j)%nat -> lval (upd ws j v) n = lval ws n.
Proof. intros. apply lval_ext. apply firstn_upd_ge. assumption. Qed.

Lemma limbs_val_split : forall ws n, 0 <= n -> n <= Z.of_nat (length ws) ->
  limbs_val ws = lval ws n + 2^(32 * n) * limbs_val (skipn (Z.to_nat n) ws).
Proof.
  intros ws n Hn Hl. unfold lval. rewrite <- (firstn_skipn (Z.to_nat n) ws) at 1.
  rewrite limbs_val_app, firstn_length_le by lia. replace (Z.of_nat (Z.to_nat n)) with n by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lval_zero_iff : forall ws n, 0 <= n ->
  lval ws n = 0 <-> (forall k, (k < Z.to_nat n)%nat -> limb32 ws k = 0).
Proof.
  intros ws n Hn. remember (Z.to_nat n) as m eqn:Em. replace n with (Z.of_nat m) by lia. clear n Hn Em.
  induction m as [|m IH].
  - rewrite lval_nonpos by lia. split; [intros _ k Hk; lia| reflexivity].
  - replace (Z.of_nat (S m)) with (Z.of_nat m + 1) by lia. rewrite lval_succ, Nat2Z.id by lia.
    pose proof (lval_range ws (Z.of_nat m) ltac:(lia)). pose proof (limb32_range ws m).
    assert (0 < 2 ^ (32 * Z.of_nat m)) by (apply Z.pow_pos_nonneg; lia).
    split.
    + intros E k Hk. assert (lval ws (Z.of_nat m) = 0 /\ limb32 ws m = 0) as [E1 E2] by nia.
      destruct (Nat.eq_dec k m) as [->|]; [exact E2|]. apply (proj1 IH E1). lia.
    + intros Hz. rewrite (proj2 IH) by (intros k Hk; apply Hz; lia). rewrite (Hz m) by lia. lia.
Qed.

Lemma pow2_32_succ : forall i, 0 <= i -> 2 ^ (32 * (i + 1)) = 2 ^ (32 * i) * 2^32.
Proof. intros. replace (32 * (i + 1)) with (32 * i + 32) by lia. rewrite Z.pow_add_r by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lval_add_step : forall xs xs' ys zs i c c', 0 <= i ->
  lval xs i + c * 2^(32*i) = lval ys i + lval zs i ->
  lval xs' i = lval xs i ->
  limb32 xs' (Z.to_nat i) + 2^32 * c' = limb32 ys (Z.to_nat i) + limb32 zs (Z.to_nat i) + c ->
  lval xs' (i+1) + c' * 2^(32*(i+1)) = lval ys (i+1) + lval zs (i+1).
Proof.
  intros xs xs' ys zs i c c' Hi INV EQ ST. rewrite !lval_succ, pow2_32_succ, EQ by lia.
  set (M := 2 ^ (32 * i)) in *. nia.
Qed.

Lemma lval_sub_step : forall xs xs' ys zs i c c', 0 <= i ->
  lval xs i - c * 2^(32*i) = lval ys i - lval zs i ->
  lval xs' i = lval xs i ->
  limb32 xs' (Z.to_nat i) - 2^32 * c' = limb32 ys (Z.to_nat i) - limb32 zs (Z.to_nat i) - c ->
  lval xs' (i+1) - c' * 2^(32*(i+1)) = lval ys (i+1) - lval zs (i+1).
Proof.
  intros xs xs' ys zs i c c' Hi INV EQ ST. rewrite !lval_succ, pow2_32_succ, EQ by lia.
  set (M := 2 ^ (32 * i)) in *. nia.
Qed.

Lemma lval_sub_int_step : forall xs xs' ys i c0 c c', 0 <= i ->
  lval xs i - c * 2^(32*i) = lval ys i - c0 ->
  lval xs' i = lval xs i ->
  limb32 xs' (Z.to_nat i) - 2^32 * c' = limb32 ys (Z.to_nat i) - c ->
  lval xs' (i+1) - c' * 2^(32*(i+1)) = lval ys (i+1) - c0.
Proof.
  intros xs xs' ys i c0 c c' Hi INV EQ ST. rewrite !lval_succ, pow2_32_succ, EQ by lia.
  set (M := 2 ^ (32 * i)) in *. nia.
Qed.

(* [comment removed for export] *)
Lemma Z_to_bv64_swrap32_mod32 : forall z, w32 (Z_to_bv 64 (bv_swrap 32 z)) = z mod 2^32.
Proof.
  intros z. unfold w32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite swrap32_mod64, sxz_mod32; [reflexivity|]. apply Z.mod_pos_bound. lia.
Qed.

Lemma core_add_exact : forall (wa wb : word) (c : Z), 0 <= c <= 1 ->
  w32 (Z_to_bv 64 (bv_swrap 32 (bv_swrap 32 (bv_unsigned (sx32 wa) + c) mod 18446744073709551616 + bv_unsigned (sx32 wb))))
  + 2^32 * (Z.b2z (bv_swrap 32 (bv_swrap 32 (bv_unsigned (sx32 wa) + c) mod 18446744073709551616 + bv_unsigned (sx32 wb)) mod 18446744073709551616
              <? bv_swrap 32 (bv_unsigned (sx32 wa) + c) mod 18446744073709551616)
            + Z.b2z (bv_swrap 32 (bv_unsigned (sx32 wa) + c) mod 18446744073709551616 <? bv_unsigned (sx32 wa)))
  = w32 wa + w32 wb + c.
Proof.
  intros wa wb c Hc. rewrite Z_to_bv64_swrap32_mod32. unfold w32. change 18446744073709551616 with (2^64).
  pose proof (Z.mod_pos_bound (bv_unsigned wa) (2^32) ltac:(lia)) as Ra.
  pose proof (Z.mod_pos_bound (bv_unsigned wb) (2^32) ltac:(lia)) as Rb.
  rewrite !bv_unsigned_sx32. set (a := bv_unsigned wa mod 2^32) in *. set (b := bv_unsigned wb mod 2^32) in *.
  rewrite !swrap32_mod64. rewrite (sxz_add_mod32 a c) by lia.
  pose proof (Z.mod_pos_bound (a + c) (2^32) ltac:(lia)) as Rt. set (t := (a + c) mod 2^32) in *.
  rewrite (sxz_add_mod32_r (sxz t) b), (sxz_add_mod32 t b) by lia.
  pose proof (Z.mod_pos_bound (t + b) (2^32) ltac:(lia)) as Rt2.
  rewrite !sxz_ltb by lia.
  assert (Et : t = a + c - (if a + c <? 2^32 then 0 else 2^32)).
  { subst t. destruct (Z.ltb_spec (a + c) (2^32)). rewrite Z.mod_small; lia.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  assert (Et2 : (t + b) mod 2^32 = t + b - (if t + b <? 2^32 then 0 else 2^32)).
  { destruct (Z.ltb_spec (t + b) (2^32)). rewrite Z.mod_small; lia.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  destruct (Z.ltb_spec (a + c) (2^32)); destruct (Z.ltb_spec (t + b) (2^32));
  destruct (Z.ltb_spec t a); destruct (Z.ltb_spec ((t + b) mod 2^32) t); cbn [Z.b2z]; lia.
Qed.

Lemma core_add_exact_u : forall (wa wb : word) (c : Z), 0 <= c <= 1 ->
  w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 wb) + bv_swrap 32 (bv_unsigned (sx32 wa) + c) mod 18446744073709551616)))
  + 2^32 * (Z.b2z (bv_swrap 32 (bv_unsigned (sx32 wb) + bv_swrap 32 (bv_unsigned (sx32 wa) + c) mod 18446744073709551616) mod 18446744073709551616
              <? bv_unsigned (sx32 wb))
            + Z.b2z (bv_swrap 32 (bv_unsigned (sx32 wa) + c) mod 18446744073709551616 <? bv_unsigned (sx32 wa)))
  = w32 wa + w32 wb + c.
Proof.
  intros wa wb c Hc. rewrite Z_to_bv64_swrap32_mod32. unfold w32. change 18446744073709551616 with (2^64).
  pose proof (Z.mod_pos_bound (bv_unsigned wa) (2^32) ltac:(lia)) as Ra.
  pose proof (Z.mod_pos_bound (bv_unsigned wb) (2^32) ltac:(lia)) as Rb.
  rewrite !bv_unsigned_sx32. set (a := bv_unsigned wa mod 2^32) in *. set (b := bv_unsigned wb mod 2^32) in *.
  rewrite !swrap32_mod64. rewrite (sxz_add_mod32 a c) by lia.
  pose proof (Z.mod_pos_bound (a + c) (2^32) ltac:(lia)) as Rt. set (t := (a + c) mod 2^32) in *.
  rewrite (sxz_add_mod32_r (sxz b) t), (sxz_add_mod32 b t) by lia.
  pose proof (Z.mod_pos_bound (b + t) (2^32) ltac:(lia)) as Rt2.
  rewrite !sxz_ltb by lia.
  assert (Et : t = a + c - (if a + c <? 2^32 then 0 else 2^32)).
  { subst t. destruct (Z.ltb_spec (a + c) (2^32)). rewrite Z.mod_small; lia.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  assert (Et2 : (b + t) mod 2^32 = b + t - (if b + t <? 2^32 then 0 else 2^32)).
  { destruct (Z.ltb_spec (b + t) (2^32)). rewrite Z.mod_small; lia.
    rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  destruct (Z.ltb_spec (a + c) (2^32)); destruct (Z.ltb_spec (b + t) (2^32));
  destruct (Z.ltb_spec t a); destruct (Z.ltb_spec ((b + t) mod 2^32) b); cbn [Z.b2z]; lia.
Qed.

Lemma core_sub_exact : forall (wa wb : word) (c : Z), 0 <= c <= 1 ->
  w32 (Z_to_bv 64 (bv_swrap 32 (bv_swrap 32 (bv_unsigned (sx32 wa) - c) mod 18446744073709551616 - bv_unsigned (sx32 wb))))
  - 2^32 * (Z.b2z (bv_swrap 32 (bv_unsigned (sx32 wa) - c) mod 18446744073709551616 <? bv_unsigned (sx32 wb))
            + Z.b2z (bv_unsigned (sx32 wa) <? c))
  = w32 wa - w32 wb - c.
Proof.
  intros wa wb c Hc. rewrite Z_to_bv64_swrap32_mod32. unfold w32. change 18446744073709551616 with (2^64).
  pose proof (Z.mod_pos_bound (bv_unsigned wa) (2^32) ltac:(lia)) as Ra.
  pose proof (Z.mod_pos_bound (bv_unsigned wb) (2^32) ltac:(lia)) as Rb.
  rewrite !bv_unsigned_sx32. set (a := bv_unsigned wa mod 2^32) in *. set (b := bv_unsigned wb mod 2^32) in *.
  rewrite !swrap32_mod64.
  replace ((sxz a - c) mod 2^32) with ((a - c) mod 2^32)
    by (unfold sxz; destruct (Z.ltb_spec a (2^31)); [reflexivity|];
        replace (a + (2^64 - 2^32) - c) with (a - c + (2^32 - 1) * 2^32) by lia; symmetry; apply Z.mod_add; lia).
  pose proof (Z.mod_pos_bound (a - c) (2^32) ltac:(lia)) as Rt. set (t := (a - c) mod 2^32) in *.
  rewrite sxz_ltb by lia.
  assert (E : (sxz a <? c) = (a <? c)).
  { unfold sxz. destruct (Z.ltb_spec a (2^31)); [reflexivity|]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. symmetry. apply Z.ltb_ge. lia. }
  rewrite E.
  replace ((sxz t - sxz b) mod 2^32) with ((t - b) mod 2^32).
  2:{ unfold sxz. destruct (Z.ltb_spec t (2^31)); destruct (Z.ltb_spec b (2^31)); try reflexivity.
      - replace (t - (b + (2^64 - 2^32))) with (t - b + (- (2^32 - 1)) * 2^32) by lia. symmetry; apply Z.mod_add; lia.
      - replace (t + (2^64 - 2^32) - b) with (t - b + (2^32 - 1) * 2^32) by lia. symmetry; apply Z.mod_add; lia.
      - f_equal. lia. }
  assert (Et : t = a - c + (if a <? c then 2^32 else 0)).
  { subst t. destruct (Z.ltb_spec a c). rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. rewrite Z.mod_small; lia. }
  assert (Et2 : (t - b) mod 2^32 = t - b + (if t <? b then 2^32 else 0)).
  { destruct (Z.ltb_spec t b). rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. rewrite Z.mod_small; lia. }
  destruct (Z.ltb_spec a c); destruct (Z.ltb_spec t b); cbn [Z.b2z]; lia.
Qed.

Lemma core_sub_int_exact : forall (wa : word) (c : Z), 0 <= c <= 2^31 ->
  w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (sx32 wa) - c)))
  - 2^32 * Z.b2z (bv_unsigned (sx32 wa) <? c)
  = w32 wa - c.
Proof.
  intros wa c Hc. rewrite Z_to_bv64_swrap32_mod32. unfold w32.
  pose proof (Z.mod_pos_bound (bv_unsigned wa) (2^32) ltac:(lia)) as Ra.
  rewrite !bv_unsigned_sx32. set (a := bv_unsigned wa mod 2^32) in *.
  replace ((sxz a - c) mod 2^32) with ((a - c) mod 2^32)
    by (unfold sxz; destruct (Z.ltb_spec a (2^31)); [reflexivity|];
        replace (a + (2^64 - 2^32) - c) with (a - c + (2^32 - 1) * 2^32) by lia; symmetry; apply Z.mod_add; lia).
  assert (E : (sxz a <? c) = (a <? c)).
  { unfold sxz. destruct (Z.ltb_spec a (2^31)); [reflexivity|]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. symmetry. apply Z.ltb_ge. lia. }
  rewrite E. destruct (Z.ltb_spec a c); cbn [Z.b2z].
  - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia.
  - rewrite Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint core_bitlen_rec (ws : list word) (r : nat) : Z :=
  match r with
  | O => 0
  | S r' => if limb32 ws r' =? 0 then core_bitlen_rec ws r' else 32 * Z.of_nat r' + Z.log2 (limb32 ws r') + 1
  end.
Definition core_bitlen (ws : list word) (n : Z) : Z := core_bitlen_rec ws (Z.to_nat n).

Lemma core_bitlen_rec_range : forall ws r, 0 <= core_bitlen_rec ws r <= 32 * Z.of_nat r.
Proof.
  induction r as [|r IH]; cbn [core_bitlen_rec]; [lia|].
  pose proof (limb32_range ws r) as R. destruct (Z.eqb_spec (limb32 ws r) 0); [lia|].
  pose proof (Z.log2_nonneg (limb32 ws r)).
  assert (Z.log2 (limb32 ws r) < 32) by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma core_bitlen_range : forall ws n, 0 <= n -> 0 <= core_bitlen ws n <= 32 * n.
Proof. intros. unfold core_bitlen. pose proof (core_bitlen_rec_range ws (Z.to_nat n)). lia. Qed.

(* [comment removed for export] *)
Lemma core_bitlen_rec_val : forall ws r,
  (core_bitlen_rec ws r = 0 /\ lval ws (Z.of_nat r) = 0)
  \/ (1 <= core_bitlen_rec ws r /\ 2^(core_bitlen_rec ws r - 1) <= lval ws (Z.of_nat r) < 2^(core_bitlen_rec ws r)).
Proof.
  induction r as [|r IH].
  - left. split; [reflexivity| apply lval_nonpos; lia].
  - cbn [core_bitlen_rec]. replace (Z.of_nat (S r)) with (Z.of_nat r + 1) by lia.
    rewrite lval_succ, Nat2Z.id by lia.
    pose proof (limb32_range ws r) as R. pose proof (lval_range ws (Z.of_nat r) ltac:(lia)) as LR.
    assert (Mp : 0 < 2 ^ (32 * Z.of_nat r)) by (apply Z.pow_pos_nonneg; lia).
    destruct (Z.eqb_spec (limb32 ws r) 0) as [E|NE].
    + rewrite E, Z.mul_0_r, Z.add_0_r. exact IH.
    + right. set (x := limb32 ws r) in *. destruct (Z.log2_spec x ltac:(lia)) as [L1 L2].
      pose proof (Z.log2_nonneg x) as L0. set (b := Z.log2 x) in *.
      replace (32 * Z.of_nat r + b + 1 - 1) with (32 * Z.of_nat r + b) by lia.
      rewrite Z.pow_add_r, (Z.pow_add_r 2 (32 * Z.of_nat r + b) 1), Z.pow_add_r by lia.
      change (2^1) with 2. rewrite Z.pow_succ_r in L2 by lia.
      set (M := 2 ^ (32 * Z.of_nat r)) in *. set (B := 2 ^ b) in *. split; [lia|]. nia.
Qed.

Lemma core_bitlen_val : forall ws n, 0 <= n ->
  (core_bitlen ws n = 0 /\ lval ws n = 0)
  \/ (1 <= core_bitlen ws n /\ 2^(core_bitlen ws n - 1) <= lval ws n < 2^(core_bitlen ws n)).
Proof.
  intros ws n Hn. unfold core_bitlen. pose proof (core_bitlen_rec_val ws (Z.to_nat n)) as H.
  rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma core_bitlen_zero_iff : forall ws n, 0 <= n -> core_bitlen ws n = 0 <-> lval ws n = 0.
Proof.
  intros ws n Hn. destruct (core_bitlen_val ws n Hn) as [[A B]|[A [B C]]]; [tauto|].
  assert (0 < 2 ^ (core_bitlen ws n - 1)) by (apply Z.pow_pos_nonneg; lia). split; intros; lia.
Qed.

(* [comment removed for export] *)
Lemma limbs_zero_lval : forall ws n, 0 <= n -> n <= Z.of_nat (length ws) -> (limbs_zero ws n <-> lval ws n = 0).
Proof.
  intros ws n Hn Hl. rewrite lval_zero_iff by lia. unfold limbs_zero. split.
  - intros H k Hk. destruct (nth_error ws k) as [w|] eqn:E; [| apply nth_error_None in E; lia].
    rewrite (limb32_nth_error _ _ _ E). unfold w32. apply (H (Z.of_nat k)); [lia|]. rewrite Nat2Z.id. exact E.
  - intros H i w Hi Hw. change (w32 w = 0). rewrite <- (limb32_nth_error _ _ _ Hw). apply H. lia.
Qed.

(* [comment removed for export] *)
Definition add_inv (xs : list word) (i c : Z) (ys zs : list word) : Prop :=
  lval xs i + c * 2^(32 * i) = lval ys i + lval zs i.
Definition sub_inv (xs : list word) (i c : Z) (ys zs : list word) : Prop :=
  lval xs i - c * 2^(32 * i) = lval ys i - lval zs i.
Definition sub_int_inv (xs : list word) (i c : Z) (ys : list word) (c0 : Z) : Prop :=
  lval xs i - c * 2^(32 * i) = lval ys i - c0.

Lemma add_inv_0 : forall xs ys zs, add_inv xs 0 0 ys zs.
Proof. intros. unfold add_inv. rewrite !lval_0. lia. Qed.
Lemma sub_inv_0 : forall xs ys zs, sub_inv xs 0 0 ys zs.
Proof. intros. unfold sub_inv. rewrite !lval_0. lia. Qed.
Lemma sub_int_inv_0 : forall xs ys c0, sub_int_inv xs 0 c0 ys c0.
Proof. intros. unfold sub_int_inv. rewrite !lval_0. lia. Qed.

Lemma add_inv_step : forall xs xs' ys zs i c c', 0 <= i -> add_inv xs i c ys zs -> lval xs' i = lval xs i ->
  limb32 xs' (Z.to_nat i) + 2^32 * c' = limb32 ys (Z.to_nat i) + limb32 zs (Z.to_nat i) + c ->
  add_inv xs' (i + 1) c' ys zs.
Proof. intros. unfold add_inv in *. eapply lval_add_step; eauto. Qed.
Lemma sub_inv_step : forall xs xs' ys zs i c c', 0 <= i -> sub_inv xs i c ys zs -> lval xs' i = lval xs i ->
  limb32 xs' (Z.to_nat i) - 2^32 * c' = limb32 ys (Z.to_nat i) - limb32 zs (Z.to_nat i) - c ->
  sub_inv xs' (i + 1) c' ys zs.
Proof. intros. unfold sub_inv in *. eapply lval_sub_step; eauto. Qed.
Lemma sub_int_inv_step : forall xs xs' ys i c0 c c', 0 <= i -> sub_int_inv xs i c ys c0 -> lval xs' i = lval xs i ->
  limb32 xs' (Z.to_nat i) - 2^32 * c' = limb32 ys (Z.to_nat i) - c ->
  sub_int_inv xs' (i + 1) c' ys c0.
Proof. intros. unfold sub_int_inv in *. eapply lval_sub_int_step; eauto. Qed.

(* [comment removed for export] *)
Definition same_from {T} (i : nat) (l l0 : list T) : Prop := forall k, (i <= k)%nat -> nth_error l k = nth_error l0 k.

Lemma same_from_refl : forall {T} i (l : list T), same_from i l l.
Proof. intros T i l k Hk. reflexivity. Qed.
Lemma same_from_weaken : forall {T} i j (l l0 : list T), same_from i l l0 -> (i <= j)%nat -> same_from j l l0.
Proof. intros T i j l l0 H Hij k Hk. apply H. lia. Qed.
Lemma same_from_upd : forall {T} i (l l0 : list T) v, same_from i l l0 -> same_from (S i) (upd l i v) l0.
Proof. intros T i l l0 v H k Hk. rewrite nth_error_upd_other by lia. apply H. lia. Qed.
Lemma same_from_skipn : forall {T} i (l l0 : list T), same_from i l l0 -> length l = length l0 -> skipn i l = skipn i l0.
Proof.
  intros T i l l0 H L. apply nth_error_ext. intros k. rewrite !nth_error_skipn. apply H. lia.
Qed.
Lemma same_from_limb32 : forall i (l l0 : list word) k w, same_from i l l0 -> (i <= k)%nat ->
  nth_error l k = Some w -> limb32 l0 k = w32 w.
Proof. intros i l l0 k w H Hk E. apply limb32_nth_error. rewrite <- (H k Hk). exact E. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u32arr_app : forall segs m A xs ys,
  u32arr segs m A (xs ++ ys) <-> u32arr segs m A xs /\ u32arr segs m (A + 4 * Z.of_nat (length xs)) ys.
Proof.
  intros segs m A xs ys. unfold u32arr. rewrite u32s_app, app_length, bytes_at_app, u32s_length.
  rewrite Nat2Z.inj_add, Z.mul_add_distr_l.
  rewrite (wr_at_app segs m A (4 * Z.of_nat (length xs)) (4 * Z.of_nat (length ys))) by lia.
  replace (Z.of_nat (4 * length xs)) with (4 * Z.of_nat (length xs)) by lia. tauto.
Qed.

Lemma u32arr_cells : forall segs m A xs,
  u32arr segs m A xs -> rw_cells segs m A [CB (4 * length xs)%nat (u32s xs)].
Proof.
  intros segs m A xs [Hb Hw]. rewrite <- (u32s_length xs). apply rw_cells_of_u8arr. split; [exact Hb|].
  rewrite u32s_length. replace (Z.of_nat (4 * length xs)) with (4 * Z.of_nat (length xs)) by lia. exact Hw.
Qed.

Lemma u32arr_of_cells : forall segs m A n bs xs,
  rw_cells segs m A [CB n bs] -> bs = u32s xs -> u32arr segs m A xs.
Proof.
  intros segs m A n bs xs H ->. apply u8arr_of_rw_cells in H. destruct H as [Hb Hw]. split; [exact Hb|].
  rewrite u32s_length in Hw. replace (4 * Z.of_nat (length xs)) with (Z.of_nat (4 * length xs)) by lia. exact Hw.
Qed.

Lemma u32s_repeat0 : forall k, u32s (repeat (Z_to_bv 64 0) k) = repeat (Z_to_bv 8 0) (4 * k).
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat u32s flat_map]. change (flat_map le4 (repeat (Z_to_bv 64 0) k)) with (u32s (repeat (Z_to_bv 64 0) k)).
  rewrite IH. replace (4 * S k)%nat with (S (S (S (S (4 * k)))))%nat by lia. cbn [repeat].
  assert (E : le4 (Z_to_bv 64 0) = [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) by (vm_compute; reflexivity).
  rewrite E. reflexivity.
Qed.

Lemma limbs_val_repeat0 : forall k, limbs_val (repeat (Z_to_bv 64 0) k) = 0.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [repeat limbs_val]. rewrite IH. vm_compute. reflexivity. Qed.

Lemma firstn_repeat' : forall {T} (x : T) j k, firstn j (repeat x k) = repeat x (Nat.min j k).
Proof. intros T x j. induction j as [|j IH]; intros [|k]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma lval_repeat0_app : forall k tl n, n <= Z.of_nat k -> lval (repeat (Z_to_bv 64 0) k ++ tl) n = 0.
Proof.
  intros k tl n Hn. unfold lval. rewrite firstn_app, repeat_length. replace (Z.to_nat n - k)%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r, firstn_repeat'. apply limbs_val_repeat0.
Qed.

(* [comment removed for export] *)
Definition lseg (ws : list word) (i n : Z) : Z := lval (skipn (Z.to_nat i) ws) (n - i).

Lemma lval_split : forall ws i n, 0 <= i <= n -> lval ws n = lval ws i + 2^(32 * i) * lseg ws i n.
Proof.
  intros ws i n Hi. unfold lseg, lval.
  rewrite <- (firstn_skipn (Z.to_nat i) (firstn (Z.to_nat n) ws)) at 1.
  rewrite limbs_val_app, firstn_firstn, firstn_length, skipn_firstn_comm.
  replace (Nat.min (Z.to_nat i) (Z.to_nat n)) with (Z.to_nat i) by lia.
  replace (Z.to_nat n - Z.to_nat i)%nat with (Z.to_nat (n - i)) by lia.
  destruct (Nat.le_gt_cases (Z.to_nat i) (length ws)) as [L|G].
  - rewrite Nat.min_l by lia. rewrite Z2Nat.id by lia. reflexivity.
  - rewrite Nat.min_r by lia. rewrite skipn_all2 by lia. rewrite firstn_nil. cbn [limbs_val]. lia.
Qed.

Lemma lseg_empty : forall ws n, lseg ws n n = 0.
Proof. intros. unfold lseg. apply lval_nonpos. lia. Qed.

Lemma lseg_cons : forall ws i n, 0 <= i < n -> lseg ws i n = limb32 ws (Z.to_nat i) + 2^32 * lseg ws (i + 1) n.
Proof.
  intros ws i n Hi. unfold lseg.
  rewrite (lval_split (skipn (Z.to_nat i) ws) 1 (n - i)) by lia. unfold lseg.
  rewrite skipn_skipn. replace (Z.to_nat 1 + Z.to_nat i)%nat with (Z.to_nat (i + 1)) by lia.
  replace (n - i - 1) with (n - (i + 1)) by lia. change (2 ^ (32 * 1)) with (2^32).
  f_equal. replace 1 with (0 + 1) by lia. rewrite lval_succ, lval_0 by lia. cbn [Z.to_nat Z.mul Z.pow Z.pow_pos Pos.iter].
  unfold limb32. rewrite nth_skipn, Nat.add_0_r. lia.
Qed.

Lemma lseg_range : forall ws i n, i <= n -> 0 <= lseg ws i n < 2^(32 * (n - i)).
Proof. intros. unfold lseg. apply lval_range. lia. Qed.

(* [comment removed for export] *)
Lemma lval_ext_nth : forall ws ws' n, (forall k, (k < Z.to_nat n)%nat -> nth_error ws k = nth_error ws' k) -> lval ws n = lval ws' n.
Proof.
  intros ws ws' n H. remember (Z.to_nat n) as j eqn:Ej.
  assert (E : forall i, 0 <= i -> (Z.to_nat i <= j)%nat -> lval ws i = lval ws' i).
  { intros i Hi. remember (Z.to_nat i) as q eqn:Eq. replace i with (Z.of_nat q) by lia. clear i Hi Eq.
    induction q as [|q IH]; intros Hq. rewrite !lval_nonpos by lia; reflexivity.
    replace (Z.of_nat (S q)) with (Z.of_nat q + 1) by lia. rewrite !lval_succ, !Nat2Z.id by lia.
    rewrite IH by lia. f_equal. f_equal. unfold limb32.
    destruct (nth_error ws q) as [w|] eqn:E1.
    - rewrite (nth_error_nth _ _ _ E1). rewrite H in E1 by lia. rewrite (nth_error_nth _ _ _ E1). reflexivity.
    - pose proof E1 as E2. rewrite H in E2 by lia. apply nth_error_None in E1. apply nth_error_None in E2.
      rewrite !nth_overflow by lia. reflexivity. }
  destruct (Z.le_gt_cases 0 n). apply E; lia. rewrite !lval_nonpos by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lval_div_limbs : forall ws v0 n, 0 <= v0 <= n -> lval ws n / 2^(32 * v0) = lseg ws v0 n.
Proof.
  intros ws v0 n H. rewrite (lval_split ws v0 n) by lia.
  pose proof (lval_range ws v0 ltac:(lia)). assert (0 < 2 ^ (32 * v0)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma shr_step_arith : forall v1 x L R S T, 0 < v1 < 32 -> 0 <= x < 2^32 -> 0 <= L -> 0 <= R ->
  S = L + 2^32 * R -> T = S / 2^v1 ->
  x / 2^v1 + (L mod 2^v1) * 2^(32 - v1) + 2^32 * T = (x + 2^32 * S) / 2^v1.
Proof.
  intros v1 x L R S T Hv Hx HL HR -> ->.
  assert (P0 : 0 < 2^v1) by (apply Z.pow_pos_nonneg; lia).
  assert (Q0 : 0 < 2^(32 - v1)) by (apply Z.pow_pos_nonneg; lia).
  assert (PQ : 2^32 = 2^v1 * 2^(32 - v1)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite PQ. set (P := 2^v1) in *. set (Q := 2^(32 - v1)) in *.
  replace (x + P * Q * (L + P * Q * R)) with (x + (Q * L + P * Q * Q * R) * P) by lia.
  rewrite Z.div_add by lia.
  replace (L + P * Q * R) with (L + (Q * R) * P) by lia. rewrite Z.div_add by lia.
  pose proof (Z.div_mod L P ltac:(lia)). nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma testbit_false_high : forall a n j, 0 <= a < 2^n -> 0 <= n <= j -> Z.testbit a j = false.
Proof.
  intros a n j Ha Hj. apply Z.testbit_false; [lia|].
  rewrite Z.div_small; [reflexivity|]. split; [lia|]. eapply Z.lt_le_trans; [apply Ha|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma lor_disjoint_add : forall a b s, 0 <= s -> 0 <= a < 2^s -> 0 <= b -> Z.lor a (b * 2^s) = a + b * 2^s.
Proof.
  intros a b s Hs Ha Hb.
  assert (D : Z.land a (b * 2^s) = 0).
  { apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases j s).
    - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - rewrite (testbit_false_high a s j) by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. symmetry. apply Z.add_nocarry_lxor. exact D.
Qed.

Lemma w32_sx32 : forall w, bv_unsigned (sx32 w) = sxz (w32 w).
Proof. intros. unfold w32. apply bv_unsigned_sx32. Qed.

Lemma sxz_mul_mod32 : forall u c, 0 <= u < 2^32 -> 0 <= c -> (sxz u * c) mod 2^32 = (u * c) mod 2^32.
Proof.
  intros u c Hu Hc. unfold sxz. destruct (Z.ltb_spec u (2^31)); [reflexivity|].
  replace ((u + (2^64 - 2^32)) * c) with (u * c + ((2^32 - 1) * c) * 2^32) by lia. apply Z.mod_add. lia.
Qed.

Lemma mul_pow_mod32 : forall u v1, 0 < v1 < 32 -> 0 <= u ->
  (u * 2^(32 - v1)) mod 2^32 = (u mod 2^v1) * 2^(32 - v1).
Proof.
  intros u v1 Hv Hu.
  replace (2^32) with (2^v1 * 2^(32 - v1)) at 1 by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r; [reflexivity| |]; apply Z.pow_nonzero; lia.
Qed.

(* [comment removed for export] *)
Lemma shr_carry_bits : forall (w : word) v1, 0 < v1 < 32 ->
  w32 (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (sx32 w)) ((32 - v1) mod 32)))) = (w32 w mod 2^v1) * 2^(32 - v1).
Proof.
  intros w v1 Hv. rewrite Z_to_bv64_swrap32_mod32, Z.shiftl_mul_pow2, (Z.mod_small (32 - v1)), w32_sx32 by lia.
  pose proof (w32_range w). rewrite sxz_mul_mod32 by (try apply Z.pow_nonneg; lia). apply mul_pow_mod32; lia.
Qed.

(* [comment removed for export] *)
Lemma shr_limb_bits : forall (w r0w : word) (v1 C : Z), 0 < v1 < 32 -> 0 <= C < 2^v1 ->
  w32 r0w = C * 2^(32 - v1) ->
  w32 (Z_to_bv 64 (Z.lor (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (sx32 w))) (v1 mod 32)) mod 18446744073709551616)
                          (bv_unsigned r0w)))
  = w32 w / 2^v1 + C * 2^(32 - v1).
Proof.
  intros w r0w v1 C Hv HC HR. rewrite (Z.mod_small v1 32) by lia.
  rewrite (srlw_z_eq v1 (bv_unsigned (sx32 w))) by lia. rewrite w32_sx32, sxz_mod32 by (apply w32_range).
  pose proof (w32_range w) as W. pose proof (bv_unsigned_in_range 64 r0w) as R. unfold bv_modulus in R.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (P0 : 0 < 2^v1) by (apply Z.pow_pos_nonneg; lia).
  assert (Q0 : 0 < 2^(32 - v1)) by (apply Z.pow_pos_nonneg; lia).
  assert (PQ : 2^32 = 2^v1 * 2^(32 - v1)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (D : 0 <= w32 w / 2^v1 < 2^(32 - v1)).
  { split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; [lia|]. rewrite <- PQ. lia. }
  unfold w32 at 1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (Z.mod_small _ (2^64)).
  2:{ apply lor_lt_pow2; [|lia]. split; [lia|]. eapply Z.lt_trans; [apply D|]. apply Z.pow_lt_mono_r; lia. }
  rewrite lor_mod32 by lia. rewrite (Z.mod_small (w32 w / 2^v1)) by lia.
  change (bv_unsigned r0w mod 2^32) with (w32 r0w). rewrite HR. apply lor_disjoint_add; lia.
Qed.


(* [comment removed for export] *)
Lemma split3 : forall {T} (l : list T) a b, (a <= b)%nat -> (b <= length l)%nat ->
  l = firstn a l ++ (firstn (b - a) (skipn a l) ++ skipn b l)
  /\ length (firstn a l) = a /\ length (firstn (b - a) (skipn a l)) = (b - a)%nat.
Proof.
  intros T l a b Hab Hb. repeat split.
  - rewrite <- (firstn_skipn a l) at 1. f_equal.
    rewrite <- (firstn_skipn (b - a) (skipn a l)) at 1. f_equal. rewrite skipn_skipn. f_equal. lia.
  - rewrite firstn_length. lia.
  - rewrite firstn_length, skipn_length. lia.
Qed.

Lemma land_31_mod : forall x, Z.land x 31 = x mod 32.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma lval_ext_limb32 : forall ws ws' n, (forall k, (k < Z.to_nat n)%nat -> limb32 ws k = limb32 ws' k) -> lval ws n = lval ws' n.
Proof.
  intros ws ws' n H. destruct (Z.le_gt_cases 0 n) as [Hn|Hn]; [| rewrite !lval_nonpos by lia; reflexivity].
  remember (Z.to_nat n) as j eqn:Ej. replace n with (Z.of_nat j) by lia. clear n Hn Ej.
  induction j as [|j IH]. rewrite !lval_nonpos by lia; reflexivity.
  replace (Z.of_nat (S j)) with (Z.of_nat j + 1) by lia. rewrite !lval_succ, !Nat2Z.id by lia.
  rewrite IH, H by (intros; try apply H; lia). reflexivity.
Qed.

Lemma w32_of_sx32 : forall w, w32 (sx32 w) = w32 w.
Proof. intros. unfold w32 at 1. rewrite bv_unsigned_sx32. apply sxz_mod32. apply Z.mod_pos_bound. lia. Qed.


(* [comment removed for export] *)
Inductive locked (P : Prop) : Prop := lock : P -> locked P.
Arguments lock {P} _.
Lemma unlock : forall P : Prop, locked P -> P. Proof. intros P [p]. exact p. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lseg_snoc : forall ws a i, 0 <= a <= i -> lseg ws a (i + 1) = lseg ws a i + 2^(32 * (i - a)) * limb32 ws (Z.to_nat i).
Proof.
  intros ws a i H. unfold lseg. replace (i + 1 - a) with ((i - a) + 1) by lia. rewrite lval_succ by lia.
  f_equal. f_equal. unfold limb32. rewrite nth_skipn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma lseg_0_lval : forall ws n, lseg ws 0 n = lval ws n.
Proof. intros. unfold lseg. cbn [Z.to_nat skipn]. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma shl_step_arith : forall v1 x, 0 < v1 < 32 -> 0 <= x ->
  (x * 2^v1) mod 2^32 + 2^32 * (x / 2^(32 - v1)) = x * 2^v1.
Proof.
  intros v1 x Hv Hx.
  assert (P0 : 0 < 2^v1) by (apply Z.pow_pos_nonneg; lia).
  assert (Q0 : 0 < 2^(32 - v1)) by (apply Z.pow_pos_nonneg; lia).
  assert (PQ : 2^32 = 2^(32 - v1) * 2^v1) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite PQ at 1. rewrite Z.mul_mod_distr_r by lia. rewrite PQ.
  pose proof (Z.div_mod x (2^(32 - v1)) ltac:(lia)). nia.
Qed.

Lemma mul_pow_mod32' : forall u v1, 0 < v1 < 32 -> 0 <= u ->
  (u * 2^v1) mod 2^32 = (u mod 2^(32 - v1)) * 2^v1.
Proof.
  intros u v1 Hv Hu.
  replace (2^32) with (2^(32 - v1) * 2^v1) at 1 by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r; [reflexivity| |]; apply Z.pow_nonzero; lia.
Qed.

(* [comment removed for export] *)
Lemma shl_limb_bits : forall (w r0w : word) (v1 : Z), 0 < v1 < 32 -> w32 r0w < 2^v1 ->
  w32 (Z_to_bv 64 (Z.lor (bv_swrap 32 (Z.shiftl (bv_unsigned (sx32 w)) (v1 mod 32)) mod 18446744073709551616)
                          (bv_unsigned r0w)))
  = (w32 w * 2^v1) mod 2^32 + w32 r0w.
Proof.
  intros w r0w v1 Hv HR. rewrite (Z.mod_small v1 32) by lia.
  pose proof (w32_range w) as W. pose proof (w32_range r0w) as R0. pose proof (bv_unsigned_in_range 64 r0w) as R. unfold bv_modulus in R.
  rewrite swrap32_mod64, Z.shiftl_mul_pow2, w32_sx32 by lia.
  rewrite sxz_mul_mod32 by (try apply Z.pow_nonneg; lia).
  pose proof (Z.mod_pos_bound (w32 w * 2^v1) (2^32) ltac:(lia)) as MB.
  unfold w32 at 1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  pose proof (sxz_range ((w32 w * 2 ^ v1) mod 2 ^ 32) MB) as SR.
  rewrite (Z.mod_small _ (2^64)).
  2:{ apply lor_lt_pow2; lia. }
  rewrite lor_mod32 by lia. rewrite sxz_mod32 by lia. change (bv_unsigned r0w mod 2^32) with (w32 r0w).
  rewrite mul_pow_mod32' by lia. rewrite Z.lor_comm. rewrite lor_disjoint_add; [lia | lia | | ].
  - split; [lia|]. eapply Z.lt_le_trans; [exact HR|]. lia.
  - apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

(* [comment removed for export] *)
Lemma shl_carry_bits : forall (w : word) v1, 0 < v1 < 32 ->
  w32 (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (sx32 w))) ((32 - v1) mod 32)))) = w32 w / 2^(32 - v1).
Proof.
  intros w v1 Hv. rewrite (Z.mod_small (32 - v1) 32) by lia.
  rewrite Z_to_bv64_swrap32_mod32. unfold bv_wrap. change (bv_modulus 32) with (2^32).
  rewrite w32_sx32, sxz_mod32 by (apply w32_range). rewrite Z.shiftr_div_pow2 by lia.
  pose proof (w32_range w). assert (0 < 2^(32 - v1)) by (apply Z.pow_pos_nonneg; lia).
  apply Z.mod_small. split. apply Z.div_pos; lia.
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Lemma shl_phase1_value : forall xs0 zs n v0, 1 <= v0 < n ->
  (forall q, (q < Z.to_nat v0)%nat -> limb32 zs q = 0) ->
  (forall q, (Z.to_nat v0 <= q < Z.to_nat n)%nat -> limb32 zs q = limb32 xs0 (q - Z.to_nat v0)%nat) ->
  lval zs n = (lval xs0 n * 2^(32 * v0)) mod 2^(32 * n).
Proof.
  intros xs0 zs n v0 Hv HZ HP.
  rewrite (lval_split zs v0 n) by lia.
  rewrite (proj2 (lval_zero_iff zs v0 ltac:(lia))) by (intros; apply HZ; lia).
  rewrite (lval_split xs0 (n - v0) n) by lia.
  assert (M : 2 ^ (32 * n) = 2 ^ (32 * (n - v0)) * 2 ^ (32 * v0)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_add_distr_r.
  replace (2 ^ (32 * (n - v0)) * lseg xs0 (n - v0) n * 2 ^ (32 * v0)) with (lseg xs0 (n - v0) n * 2 ^ (32 * n)) by (rewrite M; lia).
  rewrite Z.mod_add by (apply Z.pow_nonzero; lia).
  rewrite Z.mod_small.
  2:{ pose proof (lval_range xs0 (n - v0) ltac:(lia)). rewrite M. split; [nia|]. apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg; lia| lia]. }
  rewrite Z.mul_comm. rewrite Z.add_0_l. f_equal. unfold lseg.
  apply lval_ext_limb32. intros k Hk. unfold limb32 at 1. rewrite nth_skipn. change (limb32 zs (Z.to_nat v0 + k) = limb32 xs0 k).
  rewrite HP by lia. f_equal. lia.
Qed.

Lemma shl_phase2_value : forall zs ys n v0 v1 r, 0 <= v0 <= n -> 0 <= v1 ->
  lval zs v0 = 0 -> lval ys v0 = lval zs v0 ->
  lseg ys v0 n + r * 2^(32 * (n - v0)) = lseg zs v0 n * 2^v1 ->
  lval ys n = (lval zs n * 2^v1) mod 2^(32 * n).
Proof.
  intros zs ys n v0 v1 r Hv Hv1 Z0 E0 INV.
  rewrite (lval_split ys v0 n), (lval_split zs v0 n), E0, Z0, !Z.add_0_l by lia.
  assert (M : 2 ^ (32 * n) = 2 ^ (32 * v0) * 2 ^ (32 * (n - v0))) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite M, <- Z.mul_assoc, Z.mul_mod_distr_l by (try apply Z.pow_nonzero; try apply Z.pow_nonneg; lia). f_equal.
  rewrite <- INV. rewrite Z.mod_add by (apply Z.pow_nonzero; lia). symmetry. apply Z.mod_small. apply lseg_range. lia.
Qed.

(* [comment removed for export] *)
Lemma shl_all_out : forall xs0 n cnt, 0 <= n -> 32 * n <= cnt -> 0 = (lval xs0 n * 2^cnt) mod 2^(32 * n).
Proof.
  intros xs0 n cnt Hn Hc. replace (2^cnt) with (2^(cnt - 32 * n) * 2^(32 * n)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_assoc, Z.mod_mul. reflexivity. apply Z.pow_nonzero; lia.
Qed.
