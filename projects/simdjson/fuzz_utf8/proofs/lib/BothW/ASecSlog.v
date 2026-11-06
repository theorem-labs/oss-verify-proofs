(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import ABase AModelFacts APrimFacts F_acache3 ASecFacts.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition slogT (j : Z) : bool := Z.eqb (cb_sm (4096 * j)) (smtbl (Z.log2 (4096 * j))).
Lemma slogT_all : forallb_range slogT 18 (Z.to_nat (131060 - 18 + 1)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition slclzT (l : Z) : bool :=
  let y := smtbl l in let k := cb_clzF y in ((34 <=? k) && (k <=? 47) && (0 <=? y) && (y <? 18446744073709551616))%bool.
Lemma slclzT_all : forallb_range slclzT 16 (Z.to_nat (28 - 16 + 1)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma log2_slog : forall z, 18 <= z <= 131060 -> 16 <= Z.log2 (4096 * z) <= 28.
Proof.
  intros z R. split.
  - change 16 with (Z.log2 73728). apply Z.log2_le_mono. lia.
  - change 28 with (Z.log2 536821760). apply Z.log2_le_mono. lia.
Qed.

Local Opaque cb_sm cb_clz cb_clzF.
Lemma slog_range : forall z, 18 <= z <= 131060 ->
  0 <= cb_sm (4096 * z) < 2^64 /\ 34 <= cb_clz (cb_sm (4096 * z)) <= 47.
Proof.
  intros z R.
  pose proof (forallb_range_spec slogT _ 18 slogT_all z ltac:(lia)) as H1. unfold slogT in H1. apply Z.eqb_eq in H1.
  pose proof (log2_slog z R) as L.
  pose proof (forallb_range_spec slclzT _ 16 slclzT_all (Z.log2 (4096 * z)) ltac:(lia)) as H2. unfold slclzT in H2. cbv zeta in H2.
  rewrite !Bool.andb_true_iff in H2. destruct H2 as [[[A B] C] D].
  apply Z.leb_le in A. apply Z.leb_le in B. apply Z.leb_le in C. apply Z.ltb_lt in D.
  rewrite cb_clzF_eq in A, B. rewrite H1. change (2 ^ 64) with 18446744073709551616. repeat split; assumption.
Qed.
Local Transparent cb_sm cb_clz cb_clzF.

Lemma slog_facts : forall ms, 73728 <= ms <= 536821760 -> ms mod 4096 = 0 ->
  0 <= cb_sm ms < 2^64 /\ 34 <= cb_clz (cb_sm ms) <= 47.
Proof.
  intros ms R M.
  assert (E : ms = 4096 * (ms / 4096)) by (Z.div_mod_to_equations; lia). rewrite E.
  apply slog_range. Z.div_mod_to_equations; lia.
Qed.
End CANSEC1.
