(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Btauto.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import ZBridge.
Import ListNotations.
Open Scope Z_scope.

Definition smear64 (v : Z) : Z := (Z.lor (Z.lor (Z.lor (Z.lor (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2)) (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2) ≫ 4)) (Z.lor (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2)) (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2) ≫ 4) ≫ 8)) (Z.lor (Z.lor (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2)) (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2) ≫ 4)) (Z.lor (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2)) (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2) ≫ 4) ≫ 8) ≫ 16)) (Z.lor (Z.lor (Z.lor (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2)) (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2) ≫ 4)) (Z.lor (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2)) (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2) ≫ 4) ≫ 8)) (Z.lor (Z.lor (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2)) (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2) ≫ 4)) (Z.lor (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2)) (Z.lor (Z.lor v (v ≫ 1)) (Z.lor v (v ≫ 1) ≫ 2) ≫ 4) ≫ 8) ≫ 16) ≫ 32)).

Definition clz_swar (x : Z) : Z := ((Z.land ((Z.land ((Z.lxor x 18446744073709551615 - Z.land (Z.lxor x 18446744073709551615 ≫ 1) 6148914691236517205) mod 18446744073709551616) 3689348814741910323 + Z.land (((Z.lxor x 18446744073709551615 - Z.land (Z.lxor x 18446744073709551615 ≫ 1) 6148914691236517205) mod 18446744073709551616) ≫ 2) 3689348814741910323 + ((Z.land ((Z.lxor x 18446744073709551615 - Z.land (Z.lxor x 18446744073709551615 ≫ 1) 6148914691236517205) mod 18446744073709551616) 3689348814741910323 + Z.land (((Z.lxor x 18446744073709551615 - Z.land (Z.lxor x 18446744073709551615 ≫ 1) 6148914691236517205) mod 18446744073709551616) ≫ 2) 3689348814741910323) mod 18446744073709551616) ≫ 4) mod 18446744073709551616) 1085102592571150095 * 72340172838076673) mod 18446744073709551616).

Lemma testbit_lor_shiftr : forall a n i, 0 <= n -> 0 <= i ->
  Z.testbit (Z.lor a (Z.shiftr a n)) i = Z.testbit a i || Z.testbit a (i + n).
Proof. intros a n i Hn Hi. rewrite Z.lor_spec, Z.shiftr_spec by lia. reflexivity. Qed.

Definition window (v : Z) (w : Z) (S : Z) : Prop :=
  forall i, 0 <= i -> (Z.testbit S i = true <-> exists k, i <= k <= i + w /\ Z.testbit v k = true).

Lemma window_0 : forall v, 0 <= v -> window v 0 v.
Proof.
  intros v Hv i Hi. split.
  - intros H. exists i. split; [lia| exact H].
  - intros (k & Hk & H). replace i with k by lia. exact H.
Qed.

Lemma window_step : forall v w S, 0 <= w -> window v w S -> window v (2 * w + 1) (Z.lor S (Z.shiftr S (w + 1))).
Proof.
  intros v w S Hw W i Hi. rewrite testbit_lor_shiftr by lia. rewrite orb_true_iff. split.
  - intros [H|H].
    + apply (W i Hi) in H as (k & Hk & H). exists k. split; [lia| exact H].
    + apply (W (i + (w + 1)) ltac:(lia)) in H as (k & Hk & H). exists k. split; [lia| exact H].
  - intros (k & Hk & H). destruct (Z_lt_le_dec k (i + (w + 1))).
    + left. apply (W i Hi). exists k. split; [lia| exact H].
    + right. apply (W (i + (w + 1)) ltac:(lia)). exists k. split; [lia| exact H].
Qed.

Lemma smear64_window : forall v, 0 <= v -> window v 63 (smear64 v).
Proof.
  intros v Hv. unfold smear64.
  apply (window_step v 31); [lia|]. apply (window_step v 15); [lia|]. apply (window_step v 7); [lia|].
  apply (window_step v 3); [lia|]. apply (window_step v 1); [lia|]. apply (window_step v 0); [lia|]. apply window_0. exact Hv.
Qed.

Lemma testbit_high_false : forall v k j, 0 <= v < 2 ^ (j + 1) -> 0 <= j -> j < k -> Z.testbit v k = false.
Proof.
  intros v k j Hv Hj Hk. apply Z.testbit_false; [lia|].
  rewrite Z.div_small; [reflexivity|]. split; [lia|].
  eapply Z.lt_le_trans; [apply (proj2 Hv)|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma testbit_msb_true : forall v j, 0 <= j -> 2 ^ j <= v < 2 ^ (j + 1) -> Z.testbit v j = true.
Proof.
  intros v j Hj Hv. apply Z.testbit_true; [lia|].
  rewrite Z.pow_add_r, Z.pow_1_r in Hv by lia.
  replace (v / 2 ^ j) with 1; [reflexivity|]. apply Z.div_unique with (r := v - 2 ^ j); lia.
Qed.

Lemma smear64_pow : forall j v, 0 <= j <= 62 -> 2 ^ j <= v < 2 ^ (j + 1) -> smear64 v = Z.ones (j + 1).
Proof.
  intros j v Hj Hv. pose proof (smear64_window v ltac:(lia)) as W.
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_le_dec j n) as [Hjn|Hnj].
  - rewrite Z.ones_spec_high by lia.
    destruct (Z.testbit (smear64 v) n) eqn:E; [| reflexivity]. exfalso.
    apply (W n Hn) in E as (k & Hk & Hb). rewrite (testbit_high_false v k j) in Hb; [discriminate| lia| lia| lia].
  - rewrite Z.ones_spec_low by lia. apply (W n Hn). exists j. split; [lia|]. apply testbit_msb_true; lia.
Qed.

Lemma clz_swar_ones : forall j, 0 <= j <= 62 -> Z.shiftr (clz_swar (Z.ones (j + 1))) 56 = 63 - j.
Proof.
  intros j Hj.
  assert (C : forallb (fun j => Z.shiftr (clz_swar (Z.ones (j + 1))) 56 =? 63 - j)
                      (map (fun i => 0 + Z.of_nat i) (seq 0 63)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C j). rewrite Z.eqb_eq in C. apply C.
  apply in_map_iff. exists (Z.to_nat j). split; [lia|]. apply in_seq. lia.
Qed.

Lemma clz_swar_smear : forall j v, 0 <= j <= 62 -> 2 ^ j <= v < 2 ^ (j + 1) -> Z.shiftr (clz_swar (smear64 v)) 56 = 63 - j.
Proof. intros j v Hj Hv. rewrite (smear64_pow j v Hj Hv). apply clz_swar_ones. exact Hj. Qed.

Lemma lxor63_small : forall c, 0 <= c <= 63 -> Z.lxor c 63 = 63 - c.
Proof.
  intros c Hc.
  assert (C : forallb (fun c => Z.lxor c 63 =? 63 - c) (map (fun i => 0 + Z.of_nat i) (seq 0 64)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C c). rewrite Z.eqb_eq in C. apply C.
  apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
