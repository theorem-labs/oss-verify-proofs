(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma q_col_room : forall Wd Hd i, 1 <= Wd -> 0 <= i < Hd * Wd -> i mod Wd < Wd - 1 -> i + 2 <= Hd * Wd.
Proof.
intros Wd Hd i HW Hi Hm. pose proof (Z.div_mod i Wd ltac:(lia)) as D. pose proof (Z.mod_pos_bound i Wd ltac:(lia)) as Hb.
assert (Hq : i / Wd < Hd) by (apply Z.div_lt_upper_bound; lia).
assert (0 <= i / Wd) by (apply Z.div_pos; lia). nia.
Qed.
Lemma q_row_col_room : forall Wd Hd i, 1 <= Wd -> 0 <= i < Hd * Wd - Wd -> i mod Wd < Wd - 1 -> i + Wd + 2 <= Hd * Wd.
Proof.
intros Wd Hd i HW Hi Hm. pose proof (Z.div_mod i Wd ltac:(lia)) as D. pose proof (Z.mod_pos_bound i Wd ltac:(lia)) as Hb.
assert (Hq : i / Wd < Hd - 1) by (apply Z.div_lt_upper_bound; [lia | nia]).
assert (0 <= i / Wd) by (apply Z.div_pos; lia). nia.
Qed.
Lemma q_inb1 : forall fmt N Wd Hd i j, N = Hd * Wd -> 1 <= Wd -> 3 <= fmt -> 0 <= i < N -> 0 <= j < 3 -> i mod Wd < Wd - 1 ->
4 * (fmt * i + j + fmt) + 4 <= 4 * (fmt * N).
Proof. intros fmt N Wd Hd i j -> HW Hf Hi Hj Hm. pose proof (q_col_room Wd Hd i HW Hi Hm). nia. Qed.
Lemma q_inb2 : forall fmt N Wd i j, 1 <= Wd -> 3 <= fmt -> 0 <= i < N -> 0 <= j < 3 -> i < N - Wd ->
4 * (fmt * i + j + fmt * Wd) + 4 <= 4 * (fmt * N).
Proof. intros fmt N Wd i j HW Hf Hi Hj Hl. nia. Qed.
Lemma q_inb3 : forall fmt N Wd i j, 1 <= Wd -> 3 <= fmt -> 0 <= i < N -> 0 <= j < 3 -> i < N - Wd ->
4 * (fmt * i + j + fmt * (Wd - 1)) + 4 <= 4 * (fmt * N).
Proof. intros fmt N Wd i j HW Hf Hi Hj Hl. nia. Qed.
Lemma q_inb4 : forall fmt N Wd Hd i j, N = Hd * Wd -> 1 <= Wd -> 3 <= fmt -> 0 <= i < N -> 0 <= j < 3 -> i < N - Wd -> i mod Wd < Wd - 1 ->
4 * (fmt * i + j + fmt * (Wd + 1)) + 4 <= 4 * (fmt * N).
Proof. intros fmt N Wd Hd i j -> HW Hf Hi Hj Hl Hm. pose proof (q_row_col_room Wd Hd i HW ltac:(lia) Hm). nia. Qed.
