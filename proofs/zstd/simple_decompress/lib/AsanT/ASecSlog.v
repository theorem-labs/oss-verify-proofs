(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import ABase AModelFacts APrimFacts F_acache3 ASecFacts.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition slog_ok (j : Z) : bool :=
  let y := cb_sm (4096 * j) in let k := cb_clz y in (34 <=? k) && (k <=? 47) && (0 <=? y) && (y <? 18446744073709551616).
Lemma slog_ok_all : forallb_range slog_ok 18 (Z.to_nat (163845 - 18 + 1)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Opaque cb_sm cb_clz.
Local Strategy expand [slog_ok].
Lemma slog_ok_sound : forall z, slog_ok z = true -> 0 <= cb_sm (4096 * z) < 2^64 /\ 34 <= cb_clz (cb_sm (4096 * z)) <= 47.
Proof.
  intros z Hz. unfold slog_ok in Hz. cbv zeta in Hz.
  rewrite !Bool.andb_true_iff in Hz. destruct Hz as [[[H1 H2] H3] H4].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
  change (2^64) with 18446744073709551616. repeat split; assumption.
Qed.

Lemma slog_range : forall z, 18 <= z <= 163845 ->
  0 <= cb_sm (4096 * z) < 2^64 /\ 34 <= cb_clz (cb_sm (4096 * z)) <= 47.
Proof.
  exact (range_by_compute (fun j => 0 <= cb_sm (4096 * j) < 2^64 /\ 34 <= cb_clz (cb_sm (4096 * j)) <= 47) slog_ok 18 163845 slog_ok_sound slog_ok_all).
Qed.

Lemma slog_facts : forall ms, 73728 <= ms <= 671109120 -> ms mod 4096 = 0 ->
  0 <= cb_sm ms < 2^64 /\ 34 <= cb_clz (cb_sm ms) <= 47.
Proof.
  intros ms R M.
  assert (E : ms = 4096 * (ms / 4096)) by (Z.div_mod_to_equations; lia). rewrite E.
  apply slog_range. Z.div_mod_to_equations; lia.
Qed.
End CANSEC1.
