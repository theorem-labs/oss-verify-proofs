(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

Lemma ex1_elim {T1 : Type} {P : T1 -> Prop} {G : Prop} :
  (exists x1, P x1) -> (forall x1, P x1 -> G) -> G.
Proof. intros [x1 H] k; exact (k x1 H). Qed.

Lemma ex2_elim {T1 T2 : Type} {P : T1 -> T2 -> Prop} {G : Prop} :
  (exists x1 x2, P x1 x2) -> (forall x1 x2, P x1 x2 -> G) -> G.
Proof. intros [x1 H] k; exact (ex1_elim H (k x1)). Qed.

Lemma ex3_elim {T1 T2 T3 : Type} {P : T1 -> T2 -> T3 -> Prop} {G : Prop} :
  (exists x1 x2 x3, P x1 x2 x3) -> (forall x1 x2 x3, P x1 x2 x3 -> G) -> G.
Proof. intros [x1 H] k; exact (ex2_elim H (k x1)). Qed.

Lemma ex4_elim {T1 T2 T3 T4 : Type} {P : T1 -> T2 -> T3 -> T4 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4, P x1 x2 x3 x4) -> (forall x1 x2 x3 x4, P x1 x2 x3 x4 -> G) -> G.
Proof. intros [x1 H] k; exact (ex3_elim H (k x1)). Qed.

Lemma ex5_elim {T1 T2 T3 T4 T5 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5) -> (forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 -> G) -> G.
Proof. intros [x1 H] k; exact (ex4_elim H (k x1)). Qed.

Lemma ex6_elim {T1 T2 T3 T4 T5 T6 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6) -> (forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6 -> G) -> G.
Proof. intros [x1 H] k; exact (ex5_elim H (k x1)). Qed.

Lemma ex7_elim {T1 T2 T3 T4 T5 T6 T7 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7) -> (forall x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7 -> G) -> G.
Proof. intros [x1 H] k; exact (ex6_elim H (k x1)). Qed.

Lemma ex8_elim {T1 T2 T3 T4 T5 T6 T7 T8 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8) -> (forall x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8 -> G) -> G.
Proof. intros [x1 H] k; exact (ex7_elim H (k x1)). Qed.

Lemma ex9_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9 -> G) -> G.
Proof. intros [x1 H] k; exact (ex8_elim H (k x1)). Qed.

Lemma ex10_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 -> G) -> G.
Proof. intros [x1 H] k; exact (ex9_elim H (k x1)). Qed.

Lemma ex11_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 -> G) -> G.
Proof. intros [x1 H] k; exact (ex10_elim H (k x1)). Qed.

Lemma ex12_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 -> G) -> G.
Proof. intros [x1 H] k; exact (ex11_elim H (k x1)). Qed.

Lemma ex13_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 -> G) -> G.
Proof. intros [x1 H] k; exact (ex12_elim H (k x1)). Qed.

Lemma ex14_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 -> G) -> G.
Proof. intros [x1 H] k; exact (ex13_elim H (k x1)). Qed.

Lemma ex15_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> G) -> G.
Proof. intros [x1 H] k; exact (ex14_elim H (k x1)). Qed.

Lemma ex16_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 -> G) -> G.
Proof. intros [x1 H] k; exact (ex15_elim H (k x1)). Qed.

Lemma ex17_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 -> G) -> G.
Proof. intros [x1 H] k; exact (ex16_elim H (k x1)). Qed.

Lemma ex18_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 -> G) -> G.
Proof. intros [x1 H] k; exact (ex17_elim H (k x1)). Qed.

Lemma ex19_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 -> G) -> G.
Proof. intros [x1 H] k; exact (ex18_elim H (k x1)). Qed.

Lemma ex20_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> T20 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 -> G) -> G.
Proof. intros [x1 H] k; exact (ex19_elim H (k x1)). Qed.

Lemma ex21_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> T20 -> T21 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 -> G) -> G.
Proof. intros [x1 H] k; exact (ex20_elim H (k x1)). Qed.

Lemma ex22_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> T20 -> T21 -> T22 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 -> G) -> G.
Proof. intros [x1 H] k; exact (ex21_elim H (k x1)). Qed.

Lemma ex23_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> T20 -> T21 -> T22 -> T23 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 -> G) -> G.
Proof. intros [x1 H] k; exact (ex22_elim H (k x1)). Qed.

Lemma ex24_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> T20 -> T21 -> T22 -> T23 -> T24 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 -> G) -> G.
Proof. intros [x1 H] k; exact (ex23_elim H (k x1)). Qed.

Lemma ex25_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> T20 -> T21 -> T22 -> T23 -> T24 -> T25 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 -> G) -> G.
Proof. intros [x1 H] k; exact (ex24_elim H (k x1)). Qed.

Lemma ex26_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> T20 -> T21 -> T22 -> T23 -> T24 -> T25 -> T26 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 -> G) -> G.
Proof. intros [x1 H] k; exact (ex25_elim H (k x1)). Qed.

Lemma ex27_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> T20 -> T21 -> T22 -> T23 -> T24 -> T25 -> T26 -> T27 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 -> G) -> G.
Proof. intros [x1 H] k; exact (ex26_elim H (k x1)). Qed.

Lemma ex28_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> T20 -> T21 -> T22 -> T23 -> T24 -> T25 -> T26 -> T27 -> T28 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 -> G) -> G.
Proof. intros [x1 H] k; exact (ex27_elim H (k x1)). Qed.

Lemma ex29_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> T20 -> T21 -> T22 -> T23 -> T24 -> T25 -> T26 -> T27 -> T28 -> T29 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 -> G) -> G.
Proof. intros [x1 H] k; exact (ex28_elim H (k x1)). Qed.

Lemma ex30_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> T20 -> T21 -> T22 -> T23 -> T24 -> T25 -> T26 -> T27 -> T28 -> T29 -> T30 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 -> G) -> G.
Proof. intros [x1 H] k; exact (ex29_elim H (k x1)). Qed.

Lemma ex31_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> T20 -> T21 -> T22 -> T23 -> T24 -> T25 -> T26 -> T27 -> T28 -> T29 -> T30 -> T31 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 -> G) -> G.
Proof. intros [x1 H] k; exact (ex30_elim H (k x1)). Qed.

Lemma ex32_elim {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28 T29 T30 T31 T32 : Type} {P : T1 -> T2 -> T3 -> T4 -> T5 -> T6 -> T7 -> T8 -> T9 -> T10 -> T11 -> T12 -> T13 -> T14 -> T15 -> T16 -> T17 -> T18 -> T19 -> T20 -> T21 -> T22 -> T23 -> T24 -> T25 -> T26 -> T27 -> T28 -> T29 -> T30 -> T31 -> T32 -> Prop} {G : Prop} :
  (exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32) -> (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 -> G) -> G.
Proof. intros [x1 H] k; exact (ex31_elim H (k x1)). Qed.

Lemma and2_elim {A1 A2 G : Prop} :
  A1 /\ A2 -> (A1 -> A2 -> G) -> G.
Proof. intros [a1 a2] k; exact (k a1 a2). Qed.

Lemma and3_elim {A1 A2 A3 G : Prop} :
  A1 /\ A2 /\ A3 -> (A1 -> A2 -> A3 -> G) -> G.
Proof. intros [a1 H] k; exact (and2_elim H (k a1)). Qed.

Lemma and4_elim {A1 A2 A3 A4 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 -> (A1 -> A2 -> A3 -> A4 -> G) -> G.
Proof. intros [a1 H] k; exact (and3_elim H (k a1)). Qed.

Lemma and5_elim {A1 A2 A3 A4 A5 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 -> (A1 -> A2 -> A3 -> A4 -> A5 -> G) -> G.
Proof. intros [a1 H] k; exact (and4_elim H (k a1)). Qed.

Lemma and6_elim {A1 A2 A3 A4 A5 A6 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> G) -> G.
Proof. intros [a1 H] k; exact (and5_elim H (k a1)). Qed.

Lemma and7_elim {A1 A2 A3 A4 A5 A6 A7 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> G) -> G.
Proof. intros [a1 H] k; exact (and6_elim H (k a1)). Qed.

Lemma and8_elim {A1 A2 A3 A4 A5 A6 A7 A8 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> G) -> G.
Proof. intros [a1 H] k; exact (and7_elim H (k a1)). Qed.

Lemma and9_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> G) -> G.
Proof. intros [a1 H] k; exact (and8_elim H (k a1)). Qed.

Lemma and10_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> G) -> G.
Proof. intros [a1 H] k; exact (and9_elim H (k a1)). Qed.

Lemma and11_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> G) -> G.
Proof. intros [a1 H] k; exact (and10_elim H (k a1)). Qed.

Lemma and12_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> G) -> G.
Proof. intros [a1 H] k; exact (and11_elim H (k a1)). Qed.

Lemma and13_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> G) -> G.
Proof. intros [a1 H] k; exact (and12_elim H (k a1)). Qed.

Lemma and14_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> G) -> G.
Proof. intros [a1 H] k; exact (and13_elim H (k a1)). Qed.

Lemma and15_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> G) -> G.
Proof. intros [a1 H] k; exact (and14_elim H (k a1)). Qed.

Lemma and16_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> G) -> G.
Proof. intros [a1 H] k; exact (and15_elim H (k a1)). Qed.

Lemma and17_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> G) -> G.
Proof. intros [a1 H] k; exact (and16_elim H (k a1)). Qed.

Lemma and18_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> G) -> G.
Proof. intros [a1 H] k; exact (and17_elim H (k a1)). Qed.

Lemma and19_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> G) -> G.
Proof. intros [a1 H] k; exact (and18_elim H (k a1)). Qed.

Lemma and20_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> G) -> G.
Proof. intros [a1 H] k; exact (and19_elim H (k a1)). Qed.

Lemma and21_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> G) -> G.
Proof. intros [a1 H] k; exact (and20_elim H (k a1)). Qed.

Lemma and22_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> G) -> G.
Proof. intros [a1 H] k; exact (and21_elim H (k a1)). Qed.

Lemma and23_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> G) -> G.
Proof. intros [a1 H] k; exact (and22_elim H (k a1)). Qed.

Lemma and24_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> G) -> G.
Proof. intros [a1 H] k; exact (and23_elim H (k a1)). Qed.

Lemma and25_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> G) -> G.
Proof. intros [a1 H] k; exact (and24_elim H (k a1)). Qed.

Lemma and26_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> G) -> G.
Proof. intros [a1 H] k; exact (and25_elim H (k a1)). Qed.

Lemma and27_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> G) -> G.
Proof. intros [a1 H] k; exact (and26_elim H (k a1)). Qed.

Lemma and28_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> G) -> G.
Proof. intros [a1 H] k; exact (and27_elim H (k a1)). Qed.

Lemma and29_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> G) -> G.
Proof. intros [a1 H] k; exact (and28_elim H (k a1)). Qed.

Lemma and30_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> G) -> G.
Proof. intros [a1 H] k; exact (and29_elim H (k a1)). Qed.

Lemma and31_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> G) -> G.
Proof. intros [a1 H] k; exact (and30_elim H (k a1)). Qed.

Lemma and32_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> G) -> G.
Proof. intros [a1 H] k; exact (and31_elim H (k a1)). Qed.

Lemma and33_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\ A33 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> G) -> G.
Proof. intros [a1 H] k; exact (and32_elim H (k a1)). Qed.

Lemma and34_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\ A33 /\ A34 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> G) -> G.
Proof. intros [a1 H] k; exact (and33_elim H (k a1)). Qed.

Lemma and35_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\ A33 /\ A34 /\ A35 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> G) -> G.
Proof. intros [a1 H] k; exact (and34_elim H (k a1)). Qed.

Lemma and36_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\ A33 /\ A34 /\ A35 /\ A36 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> G) -> G.
Proof. intros [a1 H] k; exact (and35_elim H (k a1)). Qed.

Lemma and37_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\ A33 /\ A34 /\ A35 /\ A36 /\ A37 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> A37 -> G) -> G.
Proof. intros [a1 H] k; exact (and36_elim H (k a1)). Qed.

Lemma and38_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\ A33 /\ A34 /\ A35 /\ A36 /\ A37 /\ A38 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> A37 -> A38 -> G) -> G.
Proof. intros [a1 H] k; exact (and37_elim H (k a1)). Qed.

Lemma and39_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\ A33 /\ A34 /\ A35 /\ A36 /\ A37 /\ A38 /\ A39 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> A37 -> A38 -> A39 -> G) -> G.
Proof. intros [a1 H] k; exact (and38_elim H (k a1)). Qed.

Lemma and40_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\ A33 /\ A34 /\ A35 /\ A36 /\ A37 /\ A38 /\ A39 /\ A40 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> A37 -> A38 -> A39 -> A40 -> G) -> G.
Proof. intros [a1 H] k; exact (and39_elim H (k a1)). Qed.

Lemma and41_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\ A33 /\ A34 /\ A35 /\ A36 /\ A37 /\ A38 /\ A39 /\ A40 /\ A41 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> A37 -> A38 -> A39 -> A40 -> A41 -> G) -> G.
Proof. intros [a1 H] k; exact (and40_elim H (k a1)). Qed.

Lemma and42_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\ A33 /\ A34 /\ A35 /\ A36 /\ A37 /\ A38 /\ A39 /\ A40 /\ A41 /\ A42 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> A37 -> A38 -> A39 -> A40 -> A41 -> A42 -> G) -> G.
Proof. intros [a1 H] k; exact (and41_elim H (k a1)). Qed.

Lemma and43_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\ A33 /\ A34 /\ A35 /\ A36 /\ A37 /\ A38 /\ A39 /\ A40 /\ A41 /\ A42 /\ A43 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> A37 -> A38 -> A39 -> A40 -> A41 -> A42 -> A43 -> G) -> G.
Proof. intros [a1 H] k; exact (and42_elim H (k a1)). Qed.

Lemma and44_elim {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 A42 A43 A44 G : Prop} :
  A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10 /\ A11 /\ A12 /\ A13 /\ A14 /\ A15 /\ A16 /\ A17 /\ A18 /\ A19 /\ A20 /\ A21 /\ A22 /\ A23 /\ A24 /\ A25 /\ A26 /\ A27 /\ A28 /\ A29 /\ A30 /\ A31 /\ A32 /\ A33 /\ A34 /\ A35 /\ A36 /\ A37 /\ A38 /\ A39 /\ A40 /\ A41 /\ A42 /\ A43 /\ A44 -> (A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> A26 -> A27 -> A28 -> A29 -> A30 -> A31 -> A32 -> A33 -> A34 -> A35 -> A36 -> A37 -> A38 -> A39 -> A40 -> A41 -> A42 -> A43 -> A44 -> G) -> G.
Proof. intros [a1 H] k; exact (and43_elim H (k a1)). Qed.


(* [comment removed for export] *)
Ltac flK T :=
  lazymatch eval hnf in T with
  | @ex ?A ?P =>
      let r := constr:(fun x : A => ltac:(let b := eval cbv beta in (P x) in let n := flK b in exact n)) in
      lazymatch r with (fun _ => ?n) => constr:(S n) end
  | _ => constr:(O)
  end.

(* [comment removed for export] *)
Ltac flex FL k :=
  lazymatch k with
  | 1 => refine (ex1_elim FL _); clear FL
  | 2 => refine (ex2_elim FL _); clear FL
  | 3 => refine (ex3_elim FL _); clear FL
  | 4 => refine (ex4_elim FL _); clear FL
  | 5 => refine (ex5_elim FL _); clear FL
  | 6 => refine (ex6_elim FL _); clear FL
  | 7 => refine (ex7_elim FL _); clear FL
  | 8 => refine (ex8_elim FL _); clear FL
  | 9 => refine (ex9_elim FL _); clear FL
  | 10 => refine (ex10_elim FL _); clear FL
  | 11 => refine (ex11_elim FL _); clear FL
  | 12 => refine (ex12_elim FL _); clear FL
  | 13 => refine (ex13_elim FL _); clear FL
  | 14 => refine (ex14_elim FL _); clear FL
  | 15 => refine (ex15_elim FL _); clear FL
  | 16 => refine (ex16_elim FL _); clear FL
  | 17 => refine (ex17_elim FL _); clear FL
  | 18 => refine (ex18_elim FL _); clear FL
  | 19 => refine (ex19_elim FL _); clear FL
  | 20 => refine (ex20_elim FL _); clear FL
  | 21 => refine (ex21_elim FL _); clear FL
  | 22 => refine (ex22_elim FL _); clear FL
  | 23 => refine (ex23_elim FL _); clear FL
  | 24 => refine (ex24_elim FL _); clear FL
  | 25 => refine (ex25_elim FL _); clear FL
  | 26 => refine (ex26_elim FL _); clear FL
  | 27 => refine (ex27_elim FL _); clear FL
  | 28 => refine (ex28_elim FL _); clear FL
  | 29 => refine (ex29_elim FL _); clear FL
  | 30 => refine (ex30_elim FL _); clear FL
  | 31 => refine (ex31_elim FL _); clear FL
  | 32 => refine (ex32_elim FL _); clear FL
  | _ => fail 100 "LxP_Flat.flex: unsupported arity" k
  end.

(* [comment removed for export] *)
Ltac fland FL n :=
  lazymatch n with
  | 2 => refine (and2_elim FL _); clear FL
  | 3 => refine (and3_elim FL _); clear FL
  | 4 => refine (and4_elim FL _); clear FL
  | 5 => refine (and5_elim FL _); clear FL
  | 6 => refine (and6_elim FL _); clear FL
  | 7 => refine (and7_elim FL _); clear FL
  | 8 => refine (and8_elim FL _); clear FL
  | 9 => refine (and9_elim FL _); clear FL
  | 10 => refine (and10_elim FL _); clear FL
  | 11 => refine (and11_elim FL _); clear FL
  | 12 => refine (and12_elim FL _); clear FL
  | 13 => refine (and13_elim FL _); clear FL
  | 14 => refine (and14_elim FL _); clear FL
  | 15 => refine (and15_elim FL _); clear FL
  | 16 => refine (and16_elim FL _); clear FL
  | 17 => refine (and17_elim FL _); clear FL
  | 18 => refine (and18_elim FL _); clear FL
  | 19 => refine (and19_elim FL _); clear FL
  | 20 => refine (and20_elim FL _); clear FL
  | 21 => refine (and21_elim FL _); clear FL
  | 22 => refine (and22_elim FL _); clear FL
  | 23 => refine (and23_elim FL _); clear FL
  | 24 => refine (and24_elim FL _); clear FL
  | 25 => refine (and25_elim FL _); clear FL
  | 26 => refine (and26_elim FL _); clear FL
  | 27 => refine (and27_elim FL _); clear FL
  | 28 => refine (and28_elim FL _); clear FL
  | 29 => refine (and29_elim FL _); clear FL
  | 30 => refine (and30_elim FL _); clear FL
  | 31 => refine (and31_elim FL _); clear FL
  | 32 => refine (and32_elim FL _); clear FL
  | 33 => refine (and33_elim FL _); clear FL
  | 34 => refine (and34_elim FL _); clear FL
  | 35 => refine (and35_elim FL _); clear FL
  | 36 => refine (and36_elim FL _); clear FL
  | 37 => refine (and37_elim FL _); clear FL
  | 38 => refine (and38_elim FL _); clear FL
  | 39 => refine (and39_elim FL _); clear FL
  | 40 => refine (and40_elim FL _); clear FL
  | 41 => refine (and41_elim FL _); clear FL
  | 42 => refine (and42_elim FL _); clear FL
  | 43 => refine (and43_elim FL _); clear FL
  | 44 => refine (and44_elim FL _); clear FL
  | _ => fail 100 "LxP_Flat.fland: unsupported arity" n
  end.

(* [comment removed for export] *)
Ltac flunder k tac :=
  lazymatch k with
  | O => tac
  | S ?k' => let x := fresh "flx" in intro x; flunder k' tac; revert x
  end.

(* [comment removed for export] *)
Ltac flpieces FL n :=
  lazymatch n with
  | 1 => revert FL
  | _ =>
    let T := type of FL in
    lazymatch eval hnf in T with
    | @ex _ _ =>
        let k := flK T in
        let kk := eval cbv in (Nat.min k (Nat.pred n)) in
        let r := eval cbv in (Nat.sub n kk) in
        flex FL kk;
        lazymatch r with
        | 1 => flunder kk ltac:(let FT := fresh "FL" in intro FT; cbv beta in FT; revert FT)
        | _ => flunder kk ltac:(let FT := fresh "FL" in intro FT; cbv beta in FT; flpieces FT r)
        end
    | _ /\ _ => let j := eval cbv in (Nat.min n 44) in flandmax FL j n
    | _ <-> _ => let j := eval cbv in (Nat.min n 44) in flandmax FL j n
    | _ => fail 100 "LxP_Flat.flpieces: not an ex/and telescope" T
    end
  end
with flandmax FL j n :=
  lazymatch j with
  | 1 => fail 100 "LxP_Flat.flandmax: no conjunction prefix"
  | _ => first
    [ fland FL j;
      lazymatch eval cbv in (Nat.sub n j) with
      | O => idtac
      | ?d => let jm := eval cbv in (Nat.pred j) in
              flunder jm ltac:(let FT := fresh "FL" in intro FT; flpieces FT (S d))
      end
    | let j' := eval cbv in (Nat.pred j) in flandmax FL j' n ]
  end.

(* [comment removed for export] *)
Ltac flat X M := let FL := fresh "FL" in pose proof X as FL; flpieces FL M.

(* [comment removed for export] *)
Ltac flclear X := try match goal with H : _ |- _ => constr_eq H X; clear H end.
