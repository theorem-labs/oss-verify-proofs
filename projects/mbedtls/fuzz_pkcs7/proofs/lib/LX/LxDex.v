(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Ltac1 Constr Std Control Array List Option Int Bool Fresh Ident.
#[global] Set Default Proof Mode "Classic".

Lemma dex_elim_1 : forall (A1 : Type) (P : A1 -> Prop) (G : Prop),
  (forall x1, P x1 -> G) -> (exists x1, P x1) -> G.
Proof. intros A1 P G K H. destruct H as [x1 H]. exact (K x1 H). Qed.
Lemma dex_elim_2 : forall (A1 A2 : Type) (P : A1 -> A2 -> Prop) (G : Prop),
  (forall x1 x2, P x1 x2 -> G) -> (exists x1 x2, P x1 x2) -> G.
Proof. intros A1 A2 P G K H. destruct H as [x1 H]. exact (dex_elim_1 A2 (P x1) G (K x1) H). Qed.
Lemma dex_elim_3 : forall (A1 A2 A3 : Type) (P : A1 -> A2 -> A3 -> Prop) (G : Prop),
  (forall x1 x2 x3, P x1 x2 x3 -> G) -> (exists x1 x2 x3, P x1 x2 x3) -> G.
Proof. intros A1 A2 A3 P G K H. destruct H as [x1 H]. exact (dex_elim_2 A2 A3 (P x1) G (K x1) H). Qed.
Lemma dex_elim_4 : forall (A1 A2 A3 A4 : Type) (P : A1 -> A2 -> A3 -> A4 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4, P x1 x2 x3 x4 -> G) -> (exists x1 x2 x3 x4, P x1 x2 x3 x4) -> G.
Proof. intros A1 A2 A3 A4 P G K H. destruct H as [x1 H]. exact (dex_elim_3 A2 A3 A4 (P x1) G (K x1) H). Qed.
Lemma dex_elim_5 : forall (A1 A2 A3 A4 A5 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 -> G) -> (exists x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5) -> G.
Proof. intros A1 A2 A3 A4 A5 P G K H. destruct H as [x1 H]. exact (dex_elim_4 A2 A3 A4 A5 (P x1) G (K x1) H). Qed.
Lemma dex_elim_6 : forall (A1 A2 A3 A4 A5 A6 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6 -> G) -> (exists x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 P G K H. destruct H as [x1 H]. exact (dex_elim_5 A2 A3 A4 A5 A6 (P x1) G (K x1) H). Qed.
Lemma dex_elim_7 : forall (A1 A2 A3 A4 A5 A6 A7 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 P G K H. destruct H as [x1 H]. exact (dex_elim_6 A2 A3 A4 A5 A6 A7 (P x1) G (K x1) H). Qed.
Lemma dex_elim_8 : forall (A1 A2 A3 A4 A5 A6 A7 A8 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 P G K H. destruct H as [x1 H]. exact (dex_elim_7 A2 A3 A4 A5 A6 A7 A8 (P x1) G (K x1) H). Qed.
Lemma dex_elim_9 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 P G K H. destruct H as [x1 H]. exact (dex_elim_8 A2 A3 A4 A5 A6 A7 A8 A9 (P x1) G (K x1) H). Qed.
Lemma dex_elim_10 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 P G K H. destruct H as [x1 H]. exact (dex_elim_9 A2 A3 A4 A5 A6 A7 A8 A9 A10 (P x1) G (K x1) H). Qed.
Lemma dex_elim_11 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 P G K H. destruct H as [x1 H]. exact (dex_elim_10 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 (P x1) G (K x1) H). Qed.
Lemma dex_elim_12 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 P G K H. destruct H as [x1 H]. exact (dex_elim_11 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 (P x1) G (K x1) H). Qed.
Lemma dex_elim_13 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 P G K H. destruct H as [x1 H]. exact (dex_elim_12 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 (P x1) G (K x1) H). Qed.
Lemma dex_elim_14 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 P G K H. destruct H as [x1 H]. exact (dex_elim_13 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 (P x1) G (K x1) H). Qed.
Lemma dex_elim_15 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 P G K H. destruct H as [x1 H]. exact (dex_elim_14 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 (P x1) G (K x1) H). Qed.
Lemma dex_elim_16 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 P G K H. destruct H as [x1 H]. exact (dex_elim_15 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 (P x1) G (K x1) H). Qed.
Lemma dex_elim_17 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 P G K H. destruct H as [x1 H]. exact (dex_elim_16 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 (P x1) G (K x1) H). Qed.
Lemma dex_elim_18 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 P G K H. destruct H as [x1 H]. exact (dex_elim_17 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 (P x1) G (K x1) H). Qed.
Lemma dex_elim_19 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 P G K H. destruct H as [x1 H]. exact (dex_elim_18 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 (P x1) G (K x1) H). Qed.
Lemma dex_elim_20 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 P G K H. destruct H as [x1 H]. exact (dex_elim_19 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 (P x1) G (K x1) H). Qed.
Lemma dex_elim_21 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 P G K H. destruct H as [x1 H]. exact (dex_elim_20 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 (P x1) G (K x1) H). Qed.
Lemma dex_elim_22 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 P G K H. destruct H as [x1 H]. exact (dex_elim_21 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 (P x1) G (K x1) H). Qed.
Lemma dex_elim_23 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 P G K H. destruct H as [x1 H]. exact (dex_elim_22 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 (P x1) G (K x1) H). Qed.
Lemma dex_elim_24 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 P G K H. destruct H as [x1 H]. exact (dex_elim_23 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 (P x1) G (K x1) H). Qed.
Lemma dex_elim_25 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 P G K H. destruct H as [x1 H]. exact (dex_elim_24 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 (P x1) G (K x1) H). Qed.
Lemma dex_elim_26 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 P G K H. destruct H as [x1 H]. exact (dex_elim_25 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 (P x1) G (K x1) H). Qed.
Lemma dex_elim_27 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 P G K H. destruct H as [x1 H]. exact (dex_elim_26 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 (P x1) G (K x1) H). Qed.
Lemma dex_elim_28 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 P G K H. destruct H as [x1 H]. exact (dex_elim_27 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 (P x1) G (K x1) H). Qed.
Lemma dex_elim_29 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 P G K H. destruct H as [x1 H]. exact (dex_elim_28 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 (P x1) G (K x1) H). Qed.
Lemma dex_elim_30 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 P G K H. destruct H as [x1 H]. exact (dex_elim_29 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 (P x1) G (K x1) H). Qed.
Lemma dex_elim_31 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 P G K H. destruct H as [x1 H]. exact (dex_elim_30 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 (P x1) G (K x1) H). Qed.
Lemma dex_elim_32 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 P G K H. destruct H as [x1 H]. exact (dex_elim_31 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 (P x1) G (K x1) H). Qed.
Lemma dex_elim_33 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 P G K H. destruct H as [x1 H]. exact (dex_elim_32 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 (P x1) G (K x1) H). Qed.
Lemma dex_elim_34 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 P G K H. destruct H as [x1 H]. exact (dex_elim_33 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 (P x1) G (K x1) H). Qed.
Lemma dex_elim_35 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 P G K H. destruct H as [x1 H]. exact (dex_elim_34 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 (P x1) G (K x1) H). Qed.
Lemma dex_elim_36 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 P G K H. destruct H as [x1 H]. exact (dex_elim_35 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 (P x1) G (K x1) H). Qed.
Lemma dex_elim_37 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> A37 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 P G K H. destruct H as [x1 H]. exact (dex_elim_36 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 (P x1) G (K x1) H). Qed.
Lemma dex_elim_38 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> A37 -> A38 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 P G K H. destruct H as [x1 H]. exact (dex_elim_37 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 (P x1) G (K x1) H). Qed.
Lemma dex_elim_39 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> A37 -> A38 -> A39 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 P G K H. destruct H as [x1 H]. exact (dex_elim_38 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 (P x1) G (K x1) H). Qed.
Lemma dex_elim_40 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> A37 -> A38 -> A39 -> A40 -> Prop) (G : Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 -> G) -> (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 P G K H. destruct H as [x1 H]. exact (dex_elim_39 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 (P x1) G (K x1) H). Qed.
Lemma dand_elim_2 : forall (C1 C2 G : Prop), (C1 -> C2 -> G) -> C1 /\ C2 -> G.
Proof. intros C1 C2 G K [H1 H2]. exact (K H1 H2). Qed.
Lemma dand_elim_3 : forall (C1 C2 C3 G : Prop), (C1 -> C2 -> C3 -> G) -> C1 /\ C2 /\ C3 -> G.
Proof. intros C1 C2 C3 G K [H1 H]. exact (dand_elim_2 C2 C3 G (K H1) H). Qed.
Lemma dand_elim_4 : forall (C1 C2 C3 C4 G : Prop), (C1 -> C2 -> C3 -> C4 -> G) -> C1 /\ C2 /\ C3 /\ C4 -> G.
Proof. intros C1 C2 C3 C4 G K [H1 H]. exact (dand_elim_3 C2 C3 C4 G (K H1) H). Qed.
Lemma dand_elim_5 : forall (C1 C2 C3 C4 C5 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 -> G.
Proof. intros C1 C2 C3 C4 C5 G K [H1 H]. exact (dand_elim_4 C2 C3 C4 C5 G (K H1) H). Qed.
Lemma dand_elim_6 : forall (C1 C2 C3 C4 C5 C6 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 G K [H1 H]. exact (dand_elim_5 C2 C3 C4 C5 C6 G (K H1) H). Qed.
Lemma dand_elim_7 : forall (C1 C2 C3 C4 C5 C6 C7 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 G K [H1 H]. exact (dand_elim_6 C2 C3 C4 C5 C6 C7 G (K H1) H). Qed.
Lemma dand_elim_8 : forall (C1 C2 C3 C4 C5 C6 C7 C8 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 G K [H1 H]. exact (dand_elim_7 C2 C3 C4 C5 C6 C7 C8 G (K H1) H). Qed.
Lemma dand_elim_9 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 G K [H1 H]. exact (dand_elim_8 C2 C3 C4 C5 C6 C7 C8 C9 G (K H1) H). Qed.
Lemma dand_elim_10 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 G K [H1 H]. exact (dand_elim_9 C2 C3 C4 C5 C6 C7 C8 C9 C10 G (K H1) H). Qed.
Lemma dand_elim_11 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 G K [H1 H]. exact (dand_elim_10 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 G (K H1) H). Qed.
Lemma dand_elim_12 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 G K [H1 H]. exact (dand_elim_11 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 G (K H1) H). Qed.
Lemma dand_elim_13 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 G K [H1 H]. exact (dand_elim_12 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 G (K H1) H). Qed.
Lemma dand_elim_14 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 G K [H1 H]. exact (dand_elim_13 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 G (K H1) H). Qed.
Lemma dand_elim_15 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 G K [H1 H]. exact (dand_elim_14 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 G (K H1) H). Qed.
Lemma dand_elim_16 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 G K [H1 H]. exact (dand_elim_15 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 G (K H1) H). Qed.
Lemma dand_elim_17 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 G K [H1 H]. exact (dand_elim_16 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 G (K H1) H). Qed.
Lemma dand_elim_18 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 G K [H1 H]. exact (dand_elim_17 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 G (K H1) H). Qed.
Lemma dand_elim_19 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 G K [H1 H]. exact (dand_elim_18 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 G (K H1) H). Qed.
Lemma dand_elim_20 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 G K [H1 H]. exact (dand_elim_19 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 G (K H1) H). Qed.
Lemma dand_elim_21 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 G K [H1 H]. exact (dand_elim_20 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 G (K H1) H). Qed.
Lemma dand_elim_22 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 G K [H1 H]. exact (dand_elim_21 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 G (K H1) H). Qed.
Lemma dand_elim_23 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 G K [H1 H]. exact (dand_elim_22 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 G (K H1) H). Qed.
Lemma dand_elim_24 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 G K [H1 H]. exact (dand_elim_23 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 G (K H1) H). Qed.
Lemma dand_elim_25 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 G K [H1 H]. exact (dand_elim_24 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 G (K H1) H). Qed.
Lemma dand_elim_26 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 G K [H1 H]. exact (dand_elim_25 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 G (K H1) H). Qed.
Lemma dand_elim_27 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 G K [H1 H]. exact (dand_elim_26 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 G (K H1) H). Qed.
Lemma dand_elim_28 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> C28 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 /\ C28 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 G K [H1 H]. exact (dand_elim_27 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 G (K H1) H). Qed.
Lemma dand_elim_29 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> C28 -> C29 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 /\ C28 /\ C29 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 G K [H1 H]. exact (dand_elim_28 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 G (K H1) H). Qed.
Lemma dand_elim_30 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> C28 -> C29 -> C30 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 /\ C28 /\ C29 /\ C30 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 G K [H1 H]. exact (dand_elim_29 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 G (K H1) H). Qed.
Lemma dand_elim_31 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> C28 -> C29 -> C30 -> C31 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 /\ C28 /\ C29 /\ C30 /\ C31 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 G K [H1 H]. exact (dand_elim_30 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 G (K H1) H). Qed.
Lemma dand_elim_32 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> C28 -> C29 -> C30 -> C31 -> C32 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 /\ C28 /\ C29 /\ C30 /\ C31 /\ C32 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 G K [H1 H]. exact (dand_elim_31 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 G (K H1) H). Qed.
Lemma dand_elim_33 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> C28 -> C29 -> C30 -> C31 -> C32 -> C33 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 /\ C28 /\ C29 /\ C30 /\ C31 /\ C32 /\ C33 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 G K [H1 H]. exact (dand_elim_32 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 G (K H1) H). Qed.
Lemma dand_elim_34 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> C28 -> C29 -> C30 -> C31 -> C32 -> C33 -> C34 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 /\ C28 /\ C29 /\ C30 /\ C31 /\ C32 /\ C33 /\ C34 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 G K [H1 H]. exact (dand_elim_33 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 G (K H1) H). Qed.
Lemma dand_elim_35 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> C28 -> C29 -> C30 -> C31 -> C32 -> C33 -> C34 -> C35 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 /\ C28 /\ C29 /\ C30 /\ C31 /\ C32 /\ C33 /\ C34 /\ C35 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 G K [H1 H]. exact (dand_elim_34 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 G (K H1) H). Qed.
Lemma dand_elim_36 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> C28 -> C29 -> C30 -> C31 -> C32 -> C33 -> C34 -> C35 -> C36 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 /\ C28 /\ C29 /\ C30 /\ C31 /\ C32 /\ C33 /\ C34 /\ C35 /\ C36 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 G K [H1 H]. exact (dand_elim_35 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 G (K H1) H). Qed.
Lemma dand_elim_37 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 C37 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> C28 -> C29 -> C30 -> C31 -> C32 -> C33 -> C34 -> C35 -> C36 -> C37 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 /\ C28 /\ C29 /\ C30 /\ C31 /\ C32 /\ C33 /\ C34 /\ C35 /\ C36 /\ C37 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 C37 G K [H1 H]. exact (dand_elim_36 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 C37 G (K H1) H). Qed.
Lemma dand_elim_38 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 C37 C38 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> C28 -> C29 -> C30 -> C31 -> C32 -> C33 -> C34 -> C35 -> C36 -> C37 -> C38 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 /\ C28 /\ C29 /\ C30 /\ C31 /\ C32 /\ C33 /\ C34 /\ C35 /\ C36 /\ C37 /\ C38 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 C37 C38 G K [H1 H]. exact (dand_elim_37 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 C37 C38 G (K H1) H). Qed.
Lemma dand_elim_39 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 C37 C38 C39 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> C28 -> C29 -> C30 -> C31 -> C32 -> C33 -> C34 -> C35 -> C36 -> C37 -> C38 -> C39 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 /\ C28 /\ C29 /\ C30 /\ C31 /\ C32 /\ C33 /\ C34 /\ C35 /\ C36 /\ C37 /\ C38 /\ C39 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 C37 C38 C39 G K [H1 H]. exact (dand_elim_38 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 C37 C38 C39 G (K H1) H). Qed.
Lemma dand_elim_40 : forall (C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 C37 C38 C39 C40 G : Prop), (C1 -> C2 -> C3 -> C4 -> C5 -> C6 -> C7 -> C8 -> C9 -> C10 -> C11 -> C12 -> C13 -> C14 -> C15 -> C16 -> C17 -> C18 -> C19 -> C20 -> C21 -> C22 -> C23 -> C24 -> C25 -> C26 -> C27 -> C28 -> C29 -> C30 -> C31 -> C32 -> C33 -> C34 -> C35 -> C36 -> C37 -> C38 -> C39 -> C40 -> G) -> C1 /\ C2 /\ C3 /\ C4 /\ C5 /\ C6 /\ C7 /\ C8 /\ C9 /\ C10 /\ C11 /\ C12 /\ C13 /\ C14 /\ C15 /\ C16 /\ C17 /\ C18 /\ C19 /\ C20 /\ C21 /\ C22 /\ C23 /\ C24 /\ C25 /\ C26 /\ C27 /\ C28 /\ C29 /\ C30 /\ C31 /\ C32 /\ C33 /\ C34 /\ C35 /\ C36 /\ C37 /\ C38 /\ C39 /\ C40 -> G.
Proof. intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 C37 C38 C39 C40 G K [H1 H]. exact (dand_elim_39 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30 C31 C32 C33 C34 C35 C36 C37 C38 C39 C40 G (K H1) H). Qed.
Ltac2 lxd_fail (s : string) := Control.zero (Tactic_failure (Some (Message.of_string s))).
Ltac2 dex_elim_lemma (n : int) : constr :=
  match n with
  | 1 => '@dex_elim_1
  | 2 => '@dex_elim_2
  | 3 => '@dex_elim_3
  | 4 => '@dex_elim_4
  | 5 => '@dex_elim_5
  | 6 => '@dex_elim_6
  | 7 => '@dex_elim_7
  | 8 => '@dex_elim_8
  | 9 => '@dex_elim_9
  | 10 => '@dex_elim_10
  | 11 => '@dex_elim_11
  | 12 => '@dex_elim_12
  | 13 => '@dex_elim_13
  | 14 => '@dex_elim_14
  | 15 => '@dex_elim_15
  | 16 => '@dex_elim_16
  | 17 => '@dex_elim_17
  | 18 => '@dex_elim_18
  | 19 => '@dex_elim_19
  | 20 => '@dex_elim_20
  | 21 => '@dex_elim_21
  | 22 => '@dex_elim_22
  | 23 => '@dex_elim_23
  | 24 => '@dex_elim_24
  | 25 => '@dex_elim_25
  | 26 => '@dex_elim_26
  | 27 => '@dex_elim_27
  | 28 => '@dex_elim_28
  | 29 => '@dex_elim_29
  | 30 => '@dex_elim_30
  | 31 => '@dex_elim_31
  | 32 => '@dex_elim_32
  | 33 => '@dex_elim_33
  | 34 => '@dex_elim_34
  | 35 => '@dex_elim_35
  | 36 => '@dex_elim_36
  | 37 => '@dex_elim_37
  | 38 => '@dex_elim_38
  | 39 => '@dex_elim_39
  | 40 => '@dex_elim_40
  | _ => lxd_fail "lxp_dex: arity out of table"
  end.
Ltac2 dand_elim_lemma (n : int) : constr :=
  match n with
  | 2 => '@dand_elim_2
  | 3 => '@dand_elim_3
  | 4 => '@dand_elim_4
  | 5 => '@dand_elim_5
  | 6 => '@dand_elim_6
  | 7 => '@dand_elim_7
  | 8 => '@dand_elim_8
  | 9 => '@dand_elim_9
  | 10 => '@dand_elim_10
  | 11 => '@dand_elim_11
  | 12 => '@dand_elim_12
  | 13 => '@dand_elim_13
  | 14 => '@dand_elim_14
  | 15 => '@dand_elim_15
  | 16 => '@dand_elim_16
  | 17 => '@dand_elim_17
  | 18 => '@dand_elim_18
  | 19 => '@dand_elim_19
  | 20 => '@dand_elim_20
  | 21 => '@dand_elim_21
  | 22 => '@dand_elim_22
  | 23 => '@dand_elim_23
  | 24 => '@dand_elim_24
  | 25 => '@dand_elim_25
  | 26 => '@dand_elim_26
  | 27 => '@dand_elim_27
  | 28 => '@dand_elim_28
  | 29 => '@dand_elim_29
  | 30 => '@dand_elim_30
  | 31 => '@dand_elim_31
  | 32 => '@dand_elim_32
  | 33 => '@dand_elim_33
  | 34 => '@dand_elim_34
  | 35 => '@dand_elim_35
  | 36 => '@dand_elim_36
  | 37 => '@dand_elim_37
  | 38 => '@dand_elim_38
  | 39 => '@dand_elim_39
  | 40 => '@dand_elim_40
  | _ => lxd_fail "lxp_dand: arity out of table"
  end.

Ltac2 lxd_is_ind (h : constr) (r : constr) : bool :=
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Ind i _ => (match Constr.Unsafe.kind r with Constr.Unsafe.Ind j _ => Ind.equal i j | _ => false end)
  | _ => false
  end.
Ltac2 lxd_ind_of (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App h _ => h
  | _ => c
  end.
Ltac2 lxd_var_of (v : Ltac1.t) : ident :=
  match Ltac1.to_ident v with
  | Some i => i
  | None =>
    match Ltac1.to_constr v with
    | Some c => match Constr.Unsafe.kind c with
                | Constr.Unsafe.Var i => i
                | _ => lxd_fail "lxp_dex: not a hypothesis"
                end
    | None =>
      match Ltac1.to_intro_pattern v with
      | Some (Std.IntroNaming (Std.IntroIdentifier i)) => i
      | _ => lxd_fail "lxp_dex: not an identifier"
      end
    end
  end.

(* [comment removed for export] *)
Ltac2 rec lxd_tele (exr : constr) (t : constr) (fuel : int) (doms : constr list) (bs : binder list) : (constr list) * (binder list) * constr :=
  if Int.le fuel 0 then (List.rev doms, bs, t) else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Bool.and (lxd_is_ind h exr) (Int.equal (Array.length args) 2) then
        let a := Array.get args 0 in
        match Constr.Unsafe.kind (Array.get args 1) with
        | Constr.Unsafe.Lambda b body =>
            if Constr.Unsafe.closedn 0 a then lxd_tele exr body (Int.sub fuel 1) (a :: doms) (b :: bs)
            else (List.rev doms, bs, t)
        | _ => (List.rev doms, bs, t)
        end
      else (List.rev doms, bs, t)
  | _ => (List.rev doms, bs, t)
  end.

(* [comment removed for export] *)
Ltac2 lxd_beta_premise () : unit :=
  let g := Control.goal () in
  match Constr.Unsafe.kind g with
  | Constr.Unsafe.Prod b cod =>
      let ty := Constr.Binder.type b in
      match Constr.Unsafe.kind ty with
      | Constr.Unsafe.App h args =>
          let rec strip (c : constr) (k : int) : constr option :=
            if Int.le k 0 then Some c else
            match Constr.Unsafe.kind c with
            | Constr.Unsafe.Lambda _ b => strip b (Int.sub k 1)
            | _ => None
            end in
          let n := Array.length args in
          (match Constr.Unsafe.kind h with
           | Constr.Unsafe.Lambda _ _ =>
             (match strip h n with
              | Some bd =>
                  let ty' := Constr.Unsafe.substnl (List.rev (Array.to_list args)) 0 bd in
                  let g' := Constr.Unsafe.make (Constr.Unsafe.Prod (Constr.Binder.make (Constr.Binder.name b) ty') cod) in
                  Std.change None (fun _ => g') { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }
              | None => () end)
           | _ => () end)
      | _ => ()
      end
  | _ => ()
  end.
Ltac lxd_beta_premise := ltac2:(Control.enter lxd_beta_premise).
Ltac lxd_intros_n n PO := do n (let x := fresh "x" in intro x); lxd_beta_premise; intro PO.

(* [comment removed for export] *)
Ltac2 lxd_dex (po : ident) : unit :=
  let t' := Std.eval_hnf (Constr.type (Control.hyp po)) in
  let (doms, bs, body) := lxd_tele (lxd_ind_of '(@ex nat (fun _ => True))) t' 40 [] [] in
  let n := List.length doms in
  if Int.lt n 1 then () else
  let lem := dex_elim_lemma n in
  let p := List.fold_left (fun acc b => Constr.Unsafe.make (Constr.Unsafe.Lambda b acc)) body bs in
  let g := Control.goal () in
  let hd := Constr.Unsafe.make (Constr.Unsafe.App lem (Array.of_list (List.append doms [p; g]))) in
  let pov := Control.hyp po in
  Control.refine (fun () => open_constr:($hd _ $pov));
  Std.clear [po];
  ltac1:(k h |- lxd_intros_n k h) (Ltac1.of_int n) (Ltac1.of_ident po).
Ltac lxp_dex PO := let f := ltac2:(po |- Control.enter (fun () => lxd_dex (lxd_var_of po))) in f PO.

(* [comment removed for export] *)
Ltac2 rec lxd_conjs (andr : constr) (t : constr) (fuel : int) : constr list :=
  if Int.le fuel 1 then [t] else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Bool.and (lxd_is_ind h andr) (Int.equal (Array.length args) 2) then
        Array.get args 0 :: lxd_conjs andr (Array.get args 1) (Int.sub fuel 1)
      else [t]
  | _ => [t]
  end.
Ltac2 lxd_dand (po : ident) : unit :=
  let t := Constr.type (Control.hyp po) in
  let cs := lxd_conjs (lxd_ind_of '(True /\ True)) t 40 in
  let n := List.length cs in
  let pov := Control.hyp po in
  if Int.lt n 2 then (ltac1:(h |- revert h) (Ltac1.of_ident po)) else
  let lem := dand_elim_lemma n in
  let g := Control.goal () in
  let hd := Constr.Unsafe.make (Constr.Unsafe.App lem (Array.of_list (List.append cs [g]))) in
  Control.refine (fun () => open_constr:($hd _ $pov));
  Std.clear [po].
Ltac lxp_dand PO := let f := ltac2:(po |- Control.enter (fun () => lxd_dand (lxd_var_of po))) in f PO.

