(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma mulhu_le : forall y M, 0 <= y < 18446744073709551616 -> 0 <= M < 18446744073709551616 ->
  0 <= Z.shiftr (y * M) 64 <= y /\ (0 < y -> Z.shiftr (y * M) 64 < y).
Proof.
  intros y M Hy HM. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 64) with 18446744073709551616.
  split; [split|].
  - apply Z.div_pos; nia.
  - apply Z.div_le_upper_bound; nia.
  - intros Hp. apply Z.div_lt_upper_bound; nia.
Qed.

Lemma shr_le : forall z k, 0 <= z -> 0 <= k -> 0 <= Z.shiftr z k <= z.
Proof.
  intros z k Hz Hk. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk) as P.
  split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; nia.
Qed.

Lemma divstep_lt : forall x M k, 0 < x < 18446744073709551616 -> 0 <= M < 18446744073709551616 -> 0 <= k ->
  0 <= Z.shiftr ((Z.shiftr (x * M) 64) mod 18446744073709551616) k < x.
Proof.
  intros x M k Hx HM Hk. destruct (mulhu_le x M ltac:(lia) HM) as [[H0 H1] H2]. specialize (H2 ltac:(lia)).
  rewrite Z.mod_small by lia. pose proof (shr_le (Z.shiftr (x * M) 64) k H0 Hk). lia.
Qed.

Lemma divstep2_lt : forall x M k, 0 < x < 18446744073709551616 -> 0 <= M < 18446744073709551616 -> 0 <= k ->
  0 <= Z.shiftr ((Z.shiftr (Z.shiftr x 2 * M) 64) mod 18446744073709551616) k < x.
Proof.
  intros x M k Hx HM Hk. pose proof (shr_le x 2 ltac:(lia) ltac:(lia)) as Hy.
  assert (Hy2 : Z.shiftr x 2 < x).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. apply Z.div_lt_upper_bound; lia. }
  destruct (mulhu_le (Z.shiftr x 2) M ltac:(lia) HM) as [[H0 H1] _].
  rewrite Z.mod_small by lia. pose proof (shr_le (Z.shiftr (Z.shiftr x 2 * M) 64) k H0 Hk). lia.
Qed.
