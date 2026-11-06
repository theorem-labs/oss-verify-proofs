(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0n.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition GH : Z := 2 ^ 23 + 2 ^ 14.
Lemma hcost_le_GH : forall n, 0 <= n <= 2 ^ 26 -> hcost n <= GH.
Proof.
intros n Hn. unfold hcost, GH. destruct (Z.leb_spec n 63472); [lia|].
assert (n / 8 <= 2 ^ 26 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 26 / 8) with (2 ^ 23) in *. lia.
Qed.
Lemma rga_d_malloc : forall A C n, bud_le A C 1 1 (wcost n) (hcost n) -> 0 <= n <= 2 ^ 26 -> bud_le A C 1 1 (2 ^ 17) GH.
Proof.
intros A C n H Hn. pose proof (wcost_range n (proj1 Hn)) as Hw. pose proof (hcost_le_GH n Hn) as Hh.
eapply bud_le_mono; [exact H | lia | lia | lia | lia].
Qed.
Lemma rga_d_realloc : forall A C n, bud_le A C 3 1 (wcost n) (hcost n) -> 0 <= n <= 2 ^ 26 -> bud_le A C 3 1 (2 ^ 17) GH.
Proof.
intros A C n H Hn. pose proof (wcost_range n (proj1 Hn)) as Hw. pose proof (hcost_le_GH n Hn) as Hh.
eapply bud_le_mono; [exact H | lia | lia | lia | lia].
Qed.
Definition gbud (S Sc : astate) (k : Z) : Prop := bud_le S Sc k k (2 ^ 17 * k) (GH * k).


Lemma gbud_step : forall S Sc S2 k e c w h, gbud S Sc k -> bud_le Sc S2 e c w h -> c <= e -> w <= 2 ^ 17 * e -> h <= GH * e -> gbud S S2 (k + e).
Proof.
intros S Sc S2 k e c w h H D Hc Hw Hh. unfold gbud in *.
eapply bud_le_mono; [exact (bud_le_trans _ _ _ _ _ _ _ _ _ _ _ H D) | unfold GH in *; lia ..].
Qed.
Lemma gbud_malloc : forall S Sc S2 k n, gbud S Sc k -> bud_le Sc S2 1 1 (wcost n) (hcost n) -> 0 <= n <= 2 ^ 26 -> gbud S S2 (k + 1).
Proof.
intros S Sc S2 k n H D Hn. pose proof (rga_d_malloc _ _ _ D Hn) as D'.
apply (gbud_step S Sc S2 k 1 1 (2 ^ 17) GH H D'); unfold GH; lia.
Qed.
Lemma gbud_realloc : forall S Sc S2 k n, gbud S Sc k -> bud_le Sc S2 3 1 (wcost n) (hcost n) -> 0 <= n <= 2 ^ 26 -> gbud S S2 (k + 3).
Proof.
intros S Sc S2 k n H D Hn. pose proof (rga_d_realloc _ _ _ D Hn) as D'.
apply (gbud_step S Sc S2 k 3 1 (2 ^ 17) GH H D'); unfold GH; lia.
Qed.
Lemma gbud_free : forall S Sc S2 k, gbud S Sc k -> bud_le Sc S2 1 0 0 0 -> gbud S S2 (k + 1).
Proof. intros S Sc S2 k H D. apply (gbud_step S Sc S2 k 1 0 0 0 H D); unfold GH; lia. Qed.
