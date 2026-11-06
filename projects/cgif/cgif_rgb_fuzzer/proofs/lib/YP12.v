(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a.
Variables W Hh N : Z.
Hypothesis HW : 1 <= W.
Hypothesis HH : 1 <= Hh.
Hypothesis HN : N = W * Hh.

Lemma row_col : forall i, 0 <= i < N -> i = W * (i / W) + i mod W /\ 0 <= i mod W < W /\ 0 <= i / W < Hh.
Proof.
intros i Hi. pose proof (Z.div_mod i W ltac:(lia)). pose proof (Z.mod_pos_bound i W ltac:(lia)).
split; [lia|]. split; [lia|]. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. subst N. lia.
Qed.
Lemma fs_right : forall i, 0 <= i < N -> i mod W < W - 1 -> 0 <= i + 1 < N.
Proof.
intros i Hi Hg. destruct (row_col i Hi) as (E & Hm & Hr). split; [lia|].
assert (W * (i / W) + W <= W * Hh) by nia. subst N. lia.
Qed.


Lemma fs_down_right : forall i, 0 <= i < N -> i < N - W -> i mod W < W - 1 -> 0 <= i + W + 1 < N.
Proof.
intros i Hi Hg Hc. destruct (row_col i Hi) as (E & Hm & Hr). split; [lia|].
assert (Hr1 : W * (i / W) + W + i mod W < W * Hh) by (subst N; lia).
assert (i / W + 1 < Hh) by nia.
assert (W * (i / W + 2) <= W * Hh) by nia. subst N. lia.
Qed.











End a.








