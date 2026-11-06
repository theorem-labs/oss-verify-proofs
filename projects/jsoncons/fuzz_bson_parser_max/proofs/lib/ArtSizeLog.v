(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import As0Tables.
Import ListNotations.
Import AsanTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma lor_range64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof.
  intros a b Ha Hb. split. apply Z.lor_nonneg; lia.
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|NZ]; [rewrite E; lia|].
  assert (Hl : Z.log2 (Z.lor a b) < 64).
  { rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
    - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
    - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  apply Z.log2_lt_pow2 in Hl; [exact Hl|]. pose proof (Z.lor_nonneg a b). lia.
Qed.

Lemma land_le_l : forall a b, 0 <= a -> Z.land a b <= a.
Proof.
  intros a b Ha. pose proof (Z.lor_ldiff_and a b) as E. pose proof (Z.add_lor_land (Z.ldiff a b) (Z.land a b)) as E2.
  rewrite E in E2.
  replace (Z.land (Z.ldiff a b) (Z.land a b)) with 0 in E2
    by (rewrite (Z.land_comm a b), Z.land_assoc, Z.land_ldiff, Z.land_0_l; reflexivity).
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; lia). lia.
Qed.

Lemma land_range64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b -> 0 <= Z.land a b < 2 ^ 64.
Proof. intros a b Ha Hb. pose proof (land_le_l a b ltac:(lia)). assert (0 <= Z.land a b) by (apply Z.land_nonneg; lia). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition smear1 (x : Z) : Z := Z.lor x (x / 2 ^ 1).
Definition smear2 (x : Z) : Z := let s := smear1 x in Z.lor s (s / 2 ^ 2).
Definition smear3 (x : Z) : Z := let s := smear2 x in Z.lor s (s / 2 ^ 4).
Definition smear4 (x : Z) : Z := let s := smear3 x in Z.lor s (s / 2 ^ 8).
Definition smear5 (x : Z) : Z := let s := smear4 x in Z.lor s (s / 2 ^ 16).
Definition smear (x : Z) : Z := let s := smear5 x in Z.lor s (s / 2 ^ 32).

(* [comment removed for export] *)
Definition sm_spec (x w s : Z) : Prop := forall i, 0 <= i -> (Z.testbit s i = true <-> exists j, i <= j <= i + w - 1 /\ Z.testbit x j = true).

Lemma sm_spec_0 : forall x, sm_spec x 1 x.
Proof. intros x i Hi. split; [intros H; exists i; split; [lia|exact H] | intros (j & Hj & H); replace i with j by lia; exact H]. Qed.

Lemma sm_spec_step : forall x w s, 0 < w -> sm_spec x w s -> sm_spec x (2 * w) (Z.lor s (s / 2 ^ w)).
Proof.
  intros x w s Hw P i Hi. rewrite Z.lor_spec, Z.div_pow2_bits by lia. rewrite Bool.orb_true_iff.
  rewrite (P i Hi), (P (i + w)%Z ltac:(lia)).
  split.
  - intros [(j & Hj & H)|(j & Hj & H)]; exists j; (split; [lia|exact H]).
  - intros (j & Hj & H). destruct (Z.lt_ge_cases j (i + w)) as [L|R].
    + left. exists j. split; [lia|exact H].
    + right. exists j. split; [lia|exact H].
Qed.

Lemma smear_spec : forall x, sm_spec x 64 (smear x).
Proof.
  intros x. unfold smear, smear5, smear4, smear3, smear2, smear1. cbv zeta.
  change 64 with (2 * 32). apply sm_spec_step; [lia|].
  change 32 with (2 * 16). apply sm_spec_step; [lia|].
  change 16 with (2 * 8). apply sm_spec_step; [lia|].
  change 8 with (2 * 4). apply sm_spec_step; [lia|].
  change 4 with (2 * 2) at 1. apply sm_spec_step; [lia|].
  change 2 with (2 * 1) at 1. apply sm_spec_step; [lia|]. apply sm_spec_0.
Qed.

Lemma smear_nonneg_aux : forall a k, 0 <= a -> 0 <= Z.lor a (a / 2 ^ k).
Proof. intros a k Ha. apply Z.lor_nonneg. split; [lia|]. destruct (Z.le_gt_cases 0 k). apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]. rewrite Z.pow_neg_r by lia. rewrite Z.div_0_r. lia. Qed.

Lemma smear_nonneg : forall x, 0 <= x -> 0 <= smear x.
Proof.
  intros x Hx. unfold smear, smear5, smear4, smear3, smear2, smear1. cbv zeta.
  repeat (apply smear_nonneg_aux). lia.
Qed.

Theorem smear_eq : forall x, 0 < x < 2 ^ 64 -> smear x = 2 ^ (Z.log2 x + 1) - 1.
Proof.
  intros x Hx. pose proof (smear_spec x) as P. pose proof (smear_nonneg x ltac:(lia)) as NN.
  assert (HL : 0 <= Z.log2 x) by (apply Z.log2_nonneg).
  assert (HL' : Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia).
  replace (2 ^ (Z.log2 x + 1) - 1) with (Z.ones (Z.log2 x + 1)) by (unfold Z.ones; rewrite Z.shiftl_1_l, <- Z.sub_1_r; reflexivity).
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.testbit_ones_nonneg by lia.
  destruct (Z.lt_ge_cases i (Z.log2 x + 1)) as [Lo|Hi'].
  - replace (i <? Z.log2 x + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    apply (proj2 (P i Hi)). exists (Z.log2 x). split; [lia|]. apply Z.bit_log2. lia.
  - replace (i <? Z.log2 x + 1) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (Z.testbit (smear x) i) eqn:E; [|reflexivity]. exfalso.
    apply (proj1 (P i Hi)) in E. destruct E as (j & Hj & Hb). rewrite Z.bits_above_log2 in Hb by lia. discriminate.
Qed.

Lemma smear_range64 : forall x, 0 < x < 2 ^ 64 -> 0 <= smear x < 2 ^ 64.
Proof.
  intros x Hx. rewrite smear_eq by lia. assert (HL' : Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). pose proof (Z.log2_nonneg x).
  split. assert (0 < 2 ^ (Z.log2 x + 1)) by (apply Z.pow_pos_nonneg; lia). lia.
  assert (2 ^ (Z.log2 x + 1) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition C55 : Z := 6148914691236517205.   (* [comment removed for export] *)
Definition C33 : Z := 3689348814741910323.   (* [comment removed for export] *)
Definition C0F : Z := 1085102592571150095.   (* [comment removed for export] *)
Definition C01 : Z := 72340172838076673.     (* [comment removed for export] *)
Definition slpop (y : Z) : Z :=
  let t2 := Z.land (y / 2 ^ 1) C55 in
  let t3 := y - t2 in
  let t7 := Z.land t3 C33 + Z.land (t3 / 2 ^ 2) C33 in
  let t9 := t7 + t7 / 2 ^ 4 in
  let t10 := Z.land t9 C0F in
  (t10 * C01) mod 2 ^ 64 / 2 ^ 56.

Definition slpop_ok (L : Z) : bool := slpop (2 ^ 64 - 1 - (2 ^ (L + 1) - 1)) =? 63 - L.
Lemma slpop_ok_all : forallb slpop_ok (zrange 0 64) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem slpop_tab : forall L, 0 <= L <= 63 -> slpop (2 ^ 64 - 1 - (2 ^ (L + 1) - 1)) = 63 - L.
Proof.
  intros L HL. assert (Hin : In L (zrange 0 64)) by (unfold zrange; apply in_ziota; lia).
  pose proof slpop_ok_all as H. rewrite forallb_forall in H. specialize (H L Hin). unfold slpop_ok in H. apply Z.eqb_eq in H. exact H.
Qed.

Definition lxor63_ok (a : Z) : bool := Z.lxor a 63 =? 63 - a.
Lemma lxor63_all : forallb lxor63_ok (zrange 0 64) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem lxor_63 : forall a, 0 <= a <= 63 -> Z.lxor a 63 = 63 - a.
Proof.
  intros a Ha. assert (Hin : In a (zrange 0 64)) by (unfold zrange; apply in_ziota; lia).
  pose proof lxor63_all as H. rewrite forallb_forall in H. specialize (H a Hin). unfold lxor63_ok in H. apply Z.eqb_eq in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma slpop_ranges : forall y, 0 <= y < 2 ^ 64 ->
  let t2 := Z.land (y / 2 ^ 1) C55 in
  let t3 := y - t2 in
  let t7 := Z.land t3 C33 + Z.land (t3 / 2 ^ 2) C33 in
  let t9 := t7 + t7 / 2 ^ 4 in
  let t10 := Z.land t9 C0F in
  0 <= t2 <= y / 2 ^ 1 /\ 0 <= y / 2 ^ 1 < 2 ^ 64 /\ 0 <= t3 < 2 ^ 64 /\ 0 <= t3 / 2 ^ 2 < 2 ^ 64 /\ 0 <= Z.land t3 C33 <= C33 /\ 0 <= Z.land (t3 / 2 ^ 2) C33 <= C33
  /\ 0 <= t7 < 2 ^ 63 /\ 0 <= t7 / 2 ^ 4 <= t7 /\ 0 <= t9 < 2 ^ 64 /\ 0 <= t10 < 2 ^ 64.
Proof.
  intros y Hy. cbv zeta. unfold C33, C55, C0F. change (2 ^ 1) with 2. change (2 ^ 2) with 4. change (2 ^ 4) with 16.
  pose proof (Z.div_mod y 2 ltac:(lia)). pose proof (Z.mod_pos_bound y 2 ltac:(lia)).
  set (y2 := y / 2) in *.
  assert (A : 0 <= Z.land y2 6148914691236517205 <= y2).
  { split. apply Z.land_nonneg; lia. apply land_le_l. lia. }
  set (t2 := Z.land y2 6148914691236517205) in *.
  pose proof (Z.div_mod (y - t2) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (y - t2) 4 ltac:(lia)).
  set (t34 := (y - t2) / 4) in *.
  assert (B1 : 0 <= Z.land (y - t2) 3689348814741910323 <= 3689348814741910323).
  { split. apply Z.land_nonneg; lia. rewrite Z.land_comm. apply land_le_l. lia. }
  assert (B2 : 0 <= Z.land t34 3689348814741910323 <= 3689348814741910323).
  { split. apply Z.land_nonneg; lia. rewrite Z.land_comm. apply land_le_l. lia. }
  set (t5 := Z.land (y - t2) 3689348814741910323) in *. set (t6 := Z.land t34 3689348814741910323) in *.
  pose proof (Z.div_mod (t5 + t6) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (t5 + t6) 16 ltac:(lia)).
  set (t8 := (t5 + t6) / 16) in *.
  assert (Cc : 0 <= Z.land (t5 + t6 + t8) 1085102592571150095 <= 1085102592571150095).
  { split. apply Z.land_nonneg; lia. rewrite Z.land_comm. apply land_le_l. lia. }
  lia.
Qed.
