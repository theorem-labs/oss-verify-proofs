(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition DRV_CALLS : Z := 12.
Definition DRV_BYTES : Z := (2^16 + 2^22) + (2^27 - 2^17 + 10 * 2^22) + (2^26 + 2^22).

(* [comment removed for export] *)
Definition room_k0 (FC : Z) : Z := DRV_CALLS + 4 * FC.
Definition room_b0 (FB : Z) : Z := DRV_BYTES + 4 * FB.

(* [comment removed for export] *)
Definition need_k (FC : Z) (j : nat) : Z := (10 - Z.of_nat j) + 1 + 4 * FC.
Definition need_b (FB : Z) (j : nat) (cap : Z) : Z :=
  (2^27 - 2 * cap) + (10 - Z.of_nat j) * 2^22 + (2^26 + 2^22) + 4 * FB.

(* [comment removed for export] *)
Definition fuzz_k (FC : Z) (rem : Z) : Z := rem * FC.
Definition fuzz_b (FB : Z) (rem : Z) : Z := rem * FB.

Lemma need0 : forall FC FB, room_k0 FC - 1 = need_k FC 0 /\ room_b0 FB - (65536 + 2^22) = need_b FB 0 65536.
Proof. intros. unfold room_k0, room_b0, need_k, need_b, DRV_CALLS, DRV_BYTES. cbn [Z.of_nat]. lia. Qed.

(* [comment removed for export] *)
Lemma need_grow : forall FC FB j cap,
  need_k FC (S j) = need_k FC j - 1 /\ need_b FB (S j) (2 * cap) = need_b FB j cap - (2 * cap + 2^22).
Proof. intros. unfold need_k, need_b. rewrite Nat2Z.inj_succ. lia. Qed.

(* [comment removed for export] *)
Lemma need_lo : forall FC FB j cap, 0 <= FC -> 0 <= FB -> Z.of_nat j <= 10 -> 0 <= cap <= 2^26 ->
  1 + 4 * FC <= need_k FC j /\ (2^26 + 2^22) + 4 * FB <= need_b FB j cap.
Proof. intros. unfold need_k, need_b. lia. Qed.

(* [comment removed for export] *)
Lemma fuzz_step : forall FC FB rem,
  fuzz_k FC rem = FC + fuzz_k FC (rem - 1) /\ fuzz_b FB rem = FB + fuzz_b FB (rem - 1).
Proof. intros. unfold fuzz_k, fuzz_b. lia. Qed.

Lemma fuzz_nonneg : forall FC FB rem, 0 <= FC -> 0 <= FB -> 0 <= rem -> 0 <= fuzz_k FC rem /\ 0 <= fuzz_b FB rem.
Proof. intros. unfold fuzz_k, fuzz_b. split; apply Z.mul_nonneg_nonneg; assumption. Qed.

Lemma fuzz_le4 : forall FC FB rem, 0 <= FC -> 0 <= FB -> 0 <= rem <= 4 ->
  fuzz_k FC rem <= 4 * FC /\ fuzz_b FB rem <= 4 * FB.
Proof. intros FC FB rem H1 H2 H3. unfold fuzz_k, fuzz_b. split; apply Z.mul_le_mono_nonneg_r; lia. Qed.
