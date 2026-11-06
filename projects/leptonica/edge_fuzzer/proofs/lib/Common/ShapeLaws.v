(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import ShapeAlg.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_alt2_assoc : forall A B C : TSet, t_eq (t_alt2 (t_alt2 A B) C) (t_alt2 A (t_alt2 B C)).
Proof. intros A B C tr. unfold t_alt2. tauto. Qed.

(* [comment removed for export] *)
Lemma t_alt2_absorb : forall A B : TSet, t_eq (t_alt2 A (t_alt2 A B)) (t_alt2 A B).
Proof. intros A B tr. unfold t_alt2. tauto. Qed.

(* [comment removed for export] *)
Lemma t_alt3_as_alt2 : forall A B C : TSet,
  t_eq (t_alt2 A (t_alt2 B C)) (t_alt2 (t_alt2 A B) C).
Proof. intros A B C. apply t_eq_sym, t_alt2_assoc. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_alt2_emit_nil_l : forall (e : list event) (T : TSet),
  T [] -> t_eq (t_alt2 (t_emit e t_nil) (t_emit e T)) (t_emit e T).
Proof.
  intros e T H0 tr. unfold t_alt2, t_emit, t_nil. split.
  - intros [[Hp | (tr' & -> & ->)] | H].
    + left. exact Hp.
    + right. exists []. split; [reflexivity | exact H0].
    + exact H.
  - intros H. right. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_alt2_distr : forall (e : list event) (A B : TSet),
  t_eq (t_emit e (t_alt2 A B)) (t_alt2 (t_emit e A) (t_emit e B)).
Proof.
  intros e A B tr. unfold t_emit, t_alt2. split.
  - intros [Hp | (tr' & -> & [HA | HB])].
    + left. left. exact Hp.
    + left. right. exists tr'. auto.
    + right. right. exists tr'. auto.
  - intros [[Hp | (tr' & -> & HA)] | [Hp | (tr' & -> & HB)]].
    + left. exact Hp.
    + right. exists tr'. auto.
    + left. exact Hp.
    + right. exists tr'. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bv_and_255_lit : forall c, (0 <= c < 256)%Z ->
  bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) = Z_to_bv 64 c.
Proof.
  intros c Hc. apply bv_eq.
  rewrite bv_and_unsigned, !Z_to_bv_unsigned.
  rewrite !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma exit_leaf_eq : forall (ch : word) c fs, (0 <= c < 256)%Z ->
  t_eq (t_emit (map (WriteEv ch) []) (t_exit (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) fs))
       (t_exit (Z_to_bv 64 c) fs).
Proof.
  intros ch c fs Hc. rewrite bv_and_255_lit by exact Hc. cbn [map].
  apply t_emit_nil_eq. unfold t_exit. apply t_emit_has_nil.
Qed.
