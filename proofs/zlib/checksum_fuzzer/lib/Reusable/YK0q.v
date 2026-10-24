(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.
Record region : Type := Rg { rg_lo : Z; rg_hi : Z }.
Definition rg_wf (r : region) : Prop :=
0 <= rg_lo r /\ rg_lo r <= rg_hi r /\ rg_hi r <= 2 ^ 64.
Definition covers (r : region) (a : word) (n : nat) : Prop :=
rg_lo r <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= rg_hi r.
Definition rg_disj (r1 r2 : region) : Prop :=
rg_hi r1 <= rg_lo r2 \/ rg_hi r2 <= rg_lo r1.
Lemma rg_disj_sym : forall r1 r2, rg_disj r1 r2 -> rg_disj r2 r1.
Proof. intros r1 r2 [H|H]; [right|left]; exact H. Qed.
Lemma covers_mono : forall r r' a n,
covers r a n -> rg_lo r' <= rg_lo r -> rg_hi r <= rg_hi r' -> covers r' a n.
Proof. intros r r' a n [H1 H2] Hl Hh. split; lia. Qed.
Lemma covers_nowrap : forall r a n,
rg_wf r -> covers r a n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64.
Proof. intros r a n (_ & _ & Hhi) (_ & H). lia. Qed.
Lemma covers_disj : forall r1 r2 a1 n1 a2 n2,
rg_disj r1 r2 -> covers r1 a1 n1 -> covers r2 a2 n2 ->
bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
\/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1.
Proof. intros r1 r2 a1 n1 a2 n2 [H|H] [H1 H2] [H3 H4]; [left|right]; lia. Qed.
Lemma covers_same_disj : forall r a1 n1 a2 n2,
covers r a1 n1 -> covers r a2 n2 ->
bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
\/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1 ->
bv_unsigned a1 + Z.of_nat n1 <= bv_unsigned a2
\/ bv_unsigned a2 + Z.of_nat n2 <= bv_unsigned a1.
Proof. auto. Qed.
Definition stack_rg (sp : word) (below above : Z) : region :=
Rg (bv_unsigned sp - below) (bv_unsigned sp + above).
Definition seg_rg (lo hi : Z) : region := Rg lo hi.
Definition heap_rg (base : word) (cur : Z) : region :=
Rg (bv_unsigned base) (bv_unsigned base + cur).
Lemma heap_rg_bump : forall base cur cur' a n,
cur <= cur' -> covers (heap_rg base cur) a n -> covers (heap_rg base cur') a n.
Proof.
intros base cur cur' a n Hle H.
apply (covers_mono (heap_rg base cur)); [exact H | cbn; lia | cbn; lia].
Qed.
Definition layout_wf (rs : list region) : Prop :=
Forall rg_wf rs /\
forall i j, (i < j)%nat -> (j < length rs)%nat ->
rg_disj (nth i rs (Rg 0 0)) (nth j rs (Rg 0 0)).
