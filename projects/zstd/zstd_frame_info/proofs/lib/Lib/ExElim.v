(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import Lia.
Unset Lia Cache.
Unset Nia Cache.


Lemma ex_elim_2 : forall (A1 A2 : Type) (P : A1 -> A2 -> Prop) (G : Prop),
  (exists x1 x2, P x1 x2) -> (forall x1 x2, P x1 x2 -> G) -> G.
Proof. intros A1 A2 P G (x1 & x2 & H) K. exact (K x1 x2 H). Qed.

Lemma ex_elim_3 : forall (A1 A2 A3 : Type) (P : A1 -> A2 -> A3 -> Prop) (G : Prop),
  (exists x1 x2 x3, P x1 x2 x3) -> (forall x1 x2 x3, P x1 x2 x3 -> G) -> G.
Proof. intros A1 A2 A3 P G (x1 & x2 & x3 & H) K. exact (K x1 x2 x3 H). Qed.

Lemma ex_elim_4 : forall (A1 A2 A3 A4 : Type) (P : A1 -> A2 -> A3 -> A4 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4, P x1 x2 x3 x4) -> (forall x1 x2 x3 x4, P x1 x2 x3 x4 -> G) -> G.
Proof. intros A1 A2 A3 A4 P G (x1 & x2 & x3 & x4 & H) K. exact (K x1 x2 x3 x4 H). Qed.

Lemma ex_elim_5 : forall (A1 A2 A3 A4 A5 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5) -> (forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 P G (x1 & x2 & x3 & x4 & x5 & H) K. exact (K x1 x2 x3 x4 x5 H). Qed.

Lemma ex_elim_6 : forall (A1 A2 A3 A4 A5 A6 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6) -> (forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 P G (x1 & x2 & x3 & x4 & x5 & x6 & H) K. exact (K x1 x2 x3 x4 x5 x6 H). Qed.

Lemma ex_elim_7 : forall (A1 A2 A3 A4 A5 A6 A7 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7) -> (forall x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 H). Qed.

Lemma ex_elim_8 : forall (A1 A2 A3 A4 A5 A6 A7 A8 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8) -> (forall x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 H). Qed.

Lemma ex_elim_9 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 H). Qed.

Lemma ex_elim_10 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 H). Qed.

Lemma ex_elim_11 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H). Qed.

Lemma ex_elim_12 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H). Qed.

Lemma ex_elim_13 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H). Qed.

Lemma ex_elim_14 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 H). Qed.

Lemma ex_elim_15 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 H). Qed.

Lemma ex_elim_16 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 H). Qed.

Lemma ex_elim_17 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 H). Qed.

Lemma ex_elim_18 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 H). Qed.

Lemma ex_elim_19 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 H). Qed.

Lemma ex_elim_20 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 H). Qed.

Lemma ex_elim_21 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 H). Qed.

Lemma ex_elim_22 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 H). Qed.

Lemma ex_elim_23 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 H). Qed.

Lemma ex_elim_24 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 H). Qed.

Lemma ex_elim_25 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 H). Qed.

Lemma ex_elim_26 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 H). Qed.

Lemma ex_elim_27 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 H). Qed.

Lemma ex_elim_28 : forall (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 : Type) (P : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> Prop) (G : Prop),
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 -> G) -> G.
Proof. intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 P G (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & H) K. exact (K x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 H). Qed.
