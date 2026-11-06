(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asan12c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Open Scope Z_scope.

Definition smear (x : Z) : Z :=
  let s1 := Z.lor x (Z.shiftr x 1) in
  let s2 := Z.lor s1 (Z.shiftr s1 2) in
  let s3 := Z.lor s2 (Z.shiftr s2 4) in
  let s4 := Z.lor s3 (Z.shiftr s3 8) in
  let s5 := Z.lor s4 (Z.shiftr s4 16) in
  Z.lor s5 (Z.shiftr s5 32).

(* [comment removed for export] *)
Definition lz_G (sm : Z) : Z :=
  let y := Z.lxor sm 18446744073709551615 in
  let pt := y - Z.land (Z.shiftr y 1) 6148914691236517205 in
  let pu := Z.land (pt mod 18446744073709551616) 3689348814741910323 + Z.land (Z.shiftr (pt mod 18446744073709551616) 2) 3689348814741910323 in
  let pv := Z.land ((pu + Z.shiftr (pu mod 18446744073709551616) 4) mod 18446744073709551616) 1085102592571150095 in
  Z.shiftr ((pv mod 18446744073709551616 * 72340172838076673) mod 18446744073709551616) 56.

Definition lma_lz (x : Z) : Z := lz_G (smear x).

(* [comment removed for export] *)
Lemma testbit_lor_shiftr : forall s d i, 0 <= d -> 0 <= i ->
  Z.testbit (Z.lor s (Z.shiftr s d)) i = Z.testbit s i || Z.testbit s (i + d).
Proof. intros s d i Hd Hi. rewrite Z.lor_spec, Z.shiftr_spec by lia. reflexivity. Qed.

Section Smear.
  Variable x : Z.
  Hypothesis X0 : 0 < x.
  Hypothesis X64 : x < 2^64.
  Let j := Z.log2 x.

  Definition hi_clear (s : Z) : Prop := forall i, j < i -> Z.testbit s i = false.
  Definition lo_set (t : Z) (s : Z) : Prop := forall i, 0 <= i <= j -> j - i < t -> Z.testbit s i = true.

  Lemma step_hi : forall s d, 0 <= d -> hi_clear s -> hi_clear (Z.lor s (Z.shiftr s d)).
  Proof. intros s d Hd H i Hi. pose proof (Z.log2_nonneg x). unfold j in *. rewrite testbit_lor_shiftr by lia. rewrite !H by lia. reflexivity. Qed.
  Lemma step_lo : forall s t, 0 <= t -> lo_set t s -> lo_set (2 * t) (Z.lor s (Z.shiftr s t)).
  Proof.
    intros s t Ht H i Hi Hd. rewrite testbit_lor_shiftr by lia.
    destruct (Z.lt_ge_cases (j - i) t).
    - rewrite (H i) by lia. reflexivity.
    - rewrite (H (i + t)) by lia. apply orb_true_r.
  Qed.
  Lemma base_hi : hi_clear x.
  Proof. intros i Hi. apply Z.bits_above_log2; lia. Qed.
  Lemma base_lo : lo_set 1 x.
  Proof. intros i Hi Hd. replace i with j by lia. apply Z.bit_log2. exact X0. Qed.

  Lemma smear_ones : smear x = Z.ones (j + 1).
  Proof.
    pose proof (Z.log2_nonneg x) as J0.
    assert (J63 : j < 64) by (apply Z.log2_lt_pow2; lia).
    assert (HC : hi_clear (smear x)) by (unfold smear; repeat (apply step_hi; [lia|]); apply base_hi).
    assert (LS : lo_set 64 (smear x)).
    { unfold smear. change 64 with (2 * 32). apply step_lo; [lia|]. change 32 with (2 * 16). apply step_lo; [lia|].
      change 16 with (2 * 8). apply step_lo; [lia|]. change 8 with (2 * 4). apply step_lo; [lia|].
      change 4 with (2 * 2). apply step_lo; [lia|]. change 2 with (2 * 1). apply step_lo; [lia|]. apply base_lo. }
    apply Z.bits_inj'. intros i Hi.
    destruct (Z.le_gt_cases i j).
    - rewrite LS by lia. rewrite Z.ones_spec_low by lia. reflexivity.
    - rewrite HC by lia. rewrite Z.ones_spec_high by lia. reflexivity.
  Qed.
End Smear.

Lemma lma_lz_range : forall x, 0 < x < 2^64 -> 0 <= lma_lz x < 64.
Proof.
  intros x Hx. unfold lma_lz. rewrite smear_ones by lia.
  pose proof (Z.log2_nonneg x). assert (Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia).
  pose proof (zall_spec 0 63 (fun j => (0 <=? lz_G (Z.ones (j + 1))) && (lz_G (Z.ones (j + 1)) <? 64)) eq_refl (Z.log2 x) ltac:(lia)) as E.
  cbn beta in E. lia.
Qed.
