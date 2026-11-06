(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec AsanNodesRP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AsanNodesRP.RPN.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma zbv_u : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. exact Hz. Qed.

Lemma v_addi_zbv : forall z i, (0 <= z < 2 ^ 64)%Z -> v_addi (Z_to_bv 64 z) i = Z_to_bv 64 (z + i).
Proof. intros z i Hz. unfold v_addi. rewrite zbv_u by exact Hz. reflexivity. Qed.

Lemma v_add_zbv : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b Ha Hb. unfold v_add. rewrite !zbv_u by assumption. reflexivity. Qed.

Lemma zbv_add1 : forall a, Z_to_bv 64 a + 1 = Z_to_bv 64 (a + 1).
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_unsigned (1 : word)) with 1%Z. change (bv_modulus 64) with (2 ^ 64)%Z.
  apply Zplus_mod_idemp_l.
Qed.

Lemma msb_scan_spec : forall n m acc,
  (fst (msb_scan m n acc) <= fst acc)%Z /\ (snd acc <= snd (msb_scan m n acc))%Z
  /\ forall j, (0 <= j < Z.of_nat n)%Z -> (fst (msb_scan m n acc) <= msb_val (4096 * (m + j)) <= snd (msb_scan m n acc))%Z.
Proof.
  induction n as [|n IH]; intros m acc; cbn [msb_scan].
  - split; [lia|]. split; [lia|]. intros j Hj. lia.
  - destruct (IH (m + 1)%Z (Z.min (fst acc) (msb_val (4096 * m)), Z.max (snd acc) (msb_val (4096 * m)))) as (A & B & C).
    cbn [fst snd] in A, B. split; [lia|]. split; [lia|].
    intros j Hj. destruct (Z.eq_dec j 0) as [->|Hj0].
    + rewrite Z.add_0_r. lia.
    + specialize (C (j - 1)%Z ltac:(lia)). replace (m + 1 + (j - 1))%Z with (m + j)%Z in C by lia. exact C.
Qed.

Lemma msb_res_w : forall x w, msb_res x w = msb_res x (Z_to_bv 64 0).
Proof. intros. reflexivity. Qed.

Lemma msb_range_sound : forall lo hi cmin cmax (x : word),
  msb_range lo hi = Some (cmin, cmax) ->
  (lo <= bv_unsigned x <= hi)%Z -> (bv_unsigned x mod 4096 = 0)%Z ->
  forall w, (cmin <= bv_unsigned (msb_res x w) <= cmax)%Z.
Proof.
  intros lo hi cmin cmax x H Hx Hal w. unfold msb_range in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate H] end.
  apply andb_prop in Hc as [Hc Hcap]. apply andb_prop in Hc as [Hlo Hm]. apply Z.leb_le in Hlo. apply Z.leb_le in Hm. apply Z.leb_le in Hcap.
  set (m0 := ((lo + 4095) / 4096)%Z) in *. set (m1 := (hi / 4096)%Z) in *.
  injection H as E.
  replace cmin with (fst (msb_scan (m0 + 1) (Z.to_nat (m1 - m0)) (msb_val (4096 * m0), msb_val (4096 * m0)))) by (rewrite E; reflexivity).
  replace cmax with (snd (msb_scan (m0 + 1) (Z.to_nat (m1 - m0)) (msb_val (4096 * m0), msb_val (4096 * m0)))) by (rewrite E; reflexivity).
  clear E.
  rewrite (msb_res_w x w). pose proof (bv_unsigned_in_range _ x) as Ux. change (bv_modulus 64) with (2 ^ 64)%Z in Ux.
  assert (Hxe : x = Z_to_bv 64 (4096 * (bv_unsigned x / 4096))).
  { apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)).
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_small; lia. }
  set (m := (bv_unsigned x / 4096)%Z) in *.
  assert (Hm01 : (m0 <= m <= m1)%Z).
  { subst m0 m1 m. split.
    - apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)).
      pose proof (Z.mul_div_le (lo + 4095) 4096 ltac:(lia)). nia.
    - apply Z.div_le_mono; lia. }
  replace (bv_unsigned (msb_res x (Z_to_bv 64 0))) with (msb_val (4096 * m)).
  2:{ unfold msb_val. rewrite <- Hxe. reflexivity. }
  destruct (msb_scan_spec (Z.to_nat (m1 - m0)) (m0 + 1)%Z (msb_val (4096 * m0), msb_val (4096 * m0))) as (A & B & C).
  cbn [fst snd] in A, B.
  destruct (Z.eq_dec m m0) as [->|Hne]; [lia|].
  specialize (C (m - m0 - 1)%Z ltac:(rewrite Z2Nat.id; lia)). replace (m0 + 1 + (m - m0 - 1))%Z with m in C by lia. exact C.
Qed.

Section MsbClosedForm.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Definition smearW (r18_0 : word) : word :=
  let r11_1 := v_srli r18_0 1 in
  let r11_2 := v_or r18_0 r11_1 in
  let r16_1 := v_srli r11_2 2 in
  let r11_3 := v_or r11_2 r16_1 in
  let r16_5 := v_srli r11_3 4 in
  let r11_4 := v_or r11_3 r16_5 in
  let r16_6 := v_srli r11_4 8 in
  let r11_5 := v_or r11_4 r16_6 in
  let r16_7 := v_srli r11_5 16 in
  let r11_6 := v_or r11_5 r16_7 in
  let r16_8 := v_srli r11_6 32 in
  v_or r11_6 r16_8.
Definition msb_tail (r11_7 : word) : word :=
  let r12_1 := v_lui 1431654400 in
  let r14_1 := v_lui 858992640 in
  let r15_1 := v_lui 252645376 in
  let r12_2 := v_addiw r12_1 (1365) in
  let r14_2 := v_addiw r14_1 (819) in
  let r15_2 := v_addiw r15_1 (-241) in
  let r16_2 := v_slli r12_2 32 in
  let r12_3 := v_add r12_2 r16_2 in
  let r16_3 := v_slli r14_2 32 in
  let r14_3 := v_add r14_2 r16_3 in
  let r16_4 := v_slli r15_2 32 in
  let r15_3 := v_add r15_2 r16_4 in
  let r11_8 := v_xori r11_7 (-1) in
  let r16_9 := v_srli r11_8 1 in
  let r12_4 := v_and r16_9 r12_3 in
  let r16_10 := v_lui 16842752 in
  let r11_9 := v_sub r11_8 r12_4 in
  let r12_5 := v_srli r11_9 2 in
  let r11_10 := v_and r11_9 r14_3 in
  let r12_6 := v_and r12_5 r14_3 in
  let r16_11 := v_addiw r16_10 (257) in
  let r11_11 := v_add r11_10 r12_6 in
  let r12_7 := v_srli r11_11 4 in
  let r11_12 := v_add r11_11 r12_7 in
  let r12_8 := v_slli r16_11 32 in
  let r11_13 := v_and r11_12 r15_3 in
  let r12_9 := v_add r16_11 r12_8 in
  let r11_14 := v_mul r11_13 r12_9 in
  v_srli r11_14 56.
Lemma msb_res_split : forall x w, msb_res x w = msb_tail (smearW x).
Proof. intros. reflexivity. Qed.

Definition smearZ (x : Z) : Z :=
  let s1 := Z.lor x (Z.shiftr x 1) in
  let s2 := Z.lor s1 (Z.shiftr s1 2) in
  let s3 := Z.lor s2 (Z.shiftr s2 4) in
  let s4 := Z.lor s3 (Z.shiftr s3 8) in
  let s5 := Z.lor s4 (Z.shiftr s4 16) in
  Z.lor s5 (Z.shiftr s5 32).

Lemma lor_bound64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [->|NZ]; [lia|].
  assert (P : 0 < Z.lor a b) by (pose proof (proj2 (Z.lor_nonneg a b) (conj (proj1 Ha) (proj1 Hb))); lia).
  apply Z.log2_lt_pow2; [exact P|]. rewrite Z.log2_lor by lia.
  destruct (Z.eq_dec a 0) as [->|NA]; destruct (Z.eq_dec b 0) as [->|NB]; cbn [Z.log2]; try lia.
  - rewrite Z.max_r by (apply Z.log2_nonneg). apply Z.log2_lt_pow2; lia.
  - rewrite Z.max_l by (apply Z.log2_nonneg). apply Z.log2_lt_pow2; lia.
  - apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.
Lemma shiftr_bound64 : forall a n, 0 <= a < 2 ^ 64 -> 0 <= n -> 0 <= Z.shiftr a n < 2 ^ 64.
Proof.
  intros a n Ha Hn. rewrite Z.shiftr_div_pow2 by exact Hn. split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with a; [|lia]. apply Z.div_le_upper_bound; [lia|]. pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn). nia.
Qed.
Lemma wu : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof. intros x. pose proof (bv_unsigned_in_range _ x) as U. change (bv_modulus 64) with (2 ^ 64) in U. exact U. Qed.
Lemma smear_step_u : forall (a : word) n, 0 <= n ->
  bv_unsigned (v_or a (v_srli a n)) = Z.lor (bv_unsigned a) (Z.shiftr (bv_unsigned a) n).
Proof.
  intros a n Hn. unfold v_or, v_srli. pose proof (wu a) as Ua.
  rewrite (zbv_u (Z.shiftr (bv_unsigned a) n)) by (apply shiftr_bound64; assumption).
  apply zbv_u. apply lor_bound64; [exact Ua | apply shiftr_bound64; assumption].
Qed.
Lemma smearW_Z : forall x, bv_unsigned (smearW x) = smearZ (bv_unsigned x).
Proof.
  intros x. unfold smearW, smearZ. cbv zeta.
  rewrite !smear_step_u by lia. reflexivity.
Qed.

Lemma smear_stage : forall s x w, 0 <= w ->
  (forall i, 0 <= i -> (Z.testbit s i = true <-> exists j, i <= j < i + w /\ Z.testbit x j = true)) ->
  forall i, 0 <= i -> (Z.testbit (Z.lor s (Z.shiftr s w)) i = true <-> exists j, i <= j < i + 2 * w /\ Z.testbit x j = true).
Proof.
  intros s x w Hw H i Hi. rewrite Z.lor_spec, Z.shiftr_spec by exact Hi. rewrite orb_true_iff.
  rewrite (H i Hi), (H (i + w) ltac:(lia)). split.
  - intros [(j & Hj & B)|(j & Hj & B)]; exists j; (split; [lia|exact B]).
  - intros (j & Hj & B). destruct (Z_lt_dec j (i + w)); [left|right]; exists j; (split; [lia|exact B]).
Qed.
Lemma smearZ_bits : forall x i, 0 <= i ->
  (Z.testbit (smearZ x) i = true <-> exists j, i <= j < i + 64 /\ Z.testbit x j = true).
Proof.
  intros x. unfold smearZ. cbv zeta.
  assert (H0 : forall i, 0 <= i -> (Z.testbit x i = true <-> exists j, i <= j < i + 1 /\ Z.testbit x j = true)).
  { intros i Hi. split; [intros B; exists i; split; [lia|exact B]|]. intros (j & Hj & B). replace i with j by lia. exact B. }
  pose proof (smear_stage _ x 1 ltac:(lia) H0) as H1. change (2 * 1) with 2 in H1.
  pose proof (smear_stage _ x 2 ltac:(lia) H1) as H2. change (2 * 2) with 4 in H2.
  pose proof (smear_stage _ x 4 ltac:(lia) H2) as H3. change (2 * 4) with 8 in H3.
  pose proof (smear_stage _ x 8 ltac:(lia) H3) as H4. change (2 * 8) with 16 in H4.
  pose proof (smear_stage _ x 16 ltac:(lia) H4) as H5. change (2 * 16) with 32 in H5.
  pose proof (smear_stage _ x 32 ltac:(lia) H5) as H6. change (2 * 32) with 64 in H6.
  exact H6.
Qed.
Lemma smearZ_ones : forall x, 1 <= x < 2 ^ 64 -> smearZ x = Z.ones (Z.log2 x + 1).
Proof.
  intros x Hx. apply Z.bits_inj'. intros i Hi.
  pose proof (Z.log2_nonneg x) as L0.
  assert (L64 : Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia).
  destruct (Z_le_dec i (Z.log2 x)) as [Hle|Hgt].
  - rewrite Z.ones_spec_low by lia. apply (proj2 (smearZ_bits x i Hi)).
    exists (Z.log2 x). split; [lia|]. apply Z.bit_log2. lia.
  - rewrite Z.ones_spec_high by lia.
    destruct (Z.testbit (smearZ x) i) eqn:E; [|reflexivity]. exfalso.
    apply (proj1 (smearZ_bits x i Hi)) in E. destruct E as (j & Hj & B).
    rewrite Z.bits_above_log2 in B by lia. discriminate.
Qed.

Definition msb_tab_ok : bool :=
  forallb (fun k => Z.eqb (bv_unsigned (msb_tail (Z_to_bv 64 (Z.ones (Z.of_nat k + 1))))) (63 - Z.of_nat k)) (seq 0 64).
Lemma msb_tab_ok_true : msb_tab_ok = true.
Proof. vm_compute. reflexivity. Qed.
Lemma msb_tail_ones : forall k, 0 <= k < 64 -> bv_unsigned (msb_tail (Z_to_bv 64 (Z.ones (k + 1)))) = 63 - k.
Proof.
  intros k Hk. pose proof msb_tab_ok_true as T. unfold msb_tab_ok in T. rewrite forallb_forall in T.
  specialize (T (Z.to_nat k) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in T by lia. apply Z.eqb_eq in T. exact T.
Qed.
Lemma msb_val_log2 : forall x, 1 <= x < 2 ^ 64 -> msb_val x = 63 - Z.log2 x.
Proof.
  intros x Hx. unfold msb_val. rewrite msb_res_split.
  pose proof (Z.log2_nonneg x) as L0.
  assert (L64 : Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia).
  assert (E : smearW (Z_to_bv 64 x) = Z_to_bv 64 (Z.ones (Z.log2 x + 1))).
  { apply bv_eq. rewrite smearW_Z. rewrite (zbv_u x) by lia. rewrite smearZ_ones by exact Hx.
    symmetry. apply zbv_u. rewrite Z.ones_equiv. split; [pose proof (Z.pow_pos_nonneg 2 (Z.log2 x + 1) ltac:(lia) ltac:(lia)); lia|].
    assert (2 ^ (Z.log2 x + 1) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia. }
  rewrite E. apply msb_tail_ones. lia.
Qed.

Lemma msb_rangeF_sound : forall lo hi cmin cmax (x : word),
  msb_rangeF lo hi = Some (cmin, cmax) ->
  (lo <= bv_unsigned x <= hi)%Z -> (bv_unsigned x mod 4096 = 0)%Z ->
  forall w, (cmin <= bv_unsigned (msb_res x w) <= cmax)%Z.
Proof.
  intros lo hi cmin cmax x H Hx Hal w. unfold msb_rangeF in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate H] end.
  apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hc Hcap]. apply andb_prop in Hc as [Hlo Hm].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hm. apply Z.ltb_lt in Hhi.
  set (m0 := ((lo + 4095) / 4096)%Z) in *. set (m1 := (hi / 4096)%Z) in *.
  injection H as <- <-.
  rewrite (msb_res_w x w). pose proof (wu x) as Ux.
  assert (Hxe : x = Z_to_bv 64 (bv_unsigned x)) by (symmetry; apply Z_to_bv_bv_unsigned).
  replace (bv_unsigned (msb_res x (Z_to_bv 64 0))) with (msb_val (bv_unsigned x)) by (unfold msb_val; rewrite <- Hxe; reflexivity).
  rewrite msb_val_log2 by lia.
  set (m := (bv_unsigned x / 4096)%Z).
  assert (Hxm : bv_unsigned x = 4096 * m) by (subst m; pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)); lia).
  assert (Hm01 : (m0 <= m <= m1)%Z).
  { subst m0 m1 m. split.
    - apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (bv_unsigned x) 4096 ltac:(lia)).
      pose proof (Z.mul_div_le (lo + 4095) 4096 ltac:(lia)). nia.
    - apply Z.div_le_mono; lia. }
  pose proof (Z.log2_le_mono (4096 * m0) (bv_unsigned x) ltac:(lia)).
  pose proof (Z.log2_le_mono (bv_unsigned x) (4096 * m1) ltac:(lia)).
  lia.
Qed.
End MsbClosedForm.
