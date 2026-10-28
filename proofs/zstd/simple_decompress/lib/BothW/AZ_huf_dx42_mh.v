(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition HR (o len c : Z) : Prop := 0 <= o /\ 0 <= c <= 112 /\ (1 <= o -> (o + 8 <= len /\ c <= 56)).
(* [comment removed for export] *)
Definition HINV (o len b : Z) : Prop := 0 <= o /\ ((o + 8 <= len /\ 0 <= b <= 8) \/ (o = 0 /\ 0 <= b <= 64)).

(* [comment removed for export] *)
Definition mdh (P : Prop) : Prop := P.

(* [comment removed for export] *)
Lemma pend_idx : forall (w : bv 64) (sh tl : Z), sh = 64 - tl -> 1 <= tl <= 12 -> 0 <= bv_unsigned w / 2 ^ sh < 2 ^ tl.
Proof.
  intros w sh tl HSH TL. pose proof (bv_unsigned_in_range 64 w) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in R.
  assert (P : 0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|].
  rewrite <- Z.pow_add_r by lia. replace (sh + tl) with 64 by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma shift_of_dl : forall tl rsv, 1 <= tl <= 12 -> 0 <= rsv -> Z.land (- (tl + 256 * rsv)) 63 = 64 - tl.
Proof.
  intros tl rsv TL RSV. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6) with 64.
  Z.div_mod_to_equations. lia.
Qed.
