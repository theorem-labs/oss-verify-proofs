(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Fixpoint all_from (f : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with O => true | S n' => f lo && all_from f (lo + 1) n' end.

Lemma all_from_spec : forall f n lo, all_from f lo n = true -> forall x, lo <= x < lo + Z.of_nat n -> f x = true.
Proof.
  intros f n. induction n as [|n IH]; intros lo H x Hx; [lia|].
  cbn [all_from] in H. apply andb_prop in H. destruct H as [H0 H1].
  destruct (Z.eq_dec x lo) as [->|NE]; [exact H0|]. apply (IH (lo + 1) H1). lia.
Qed.

Definition sf_beta (e2 : Z) : Z := e2 + Z.shiftr ((2 - sf_k e2) * 1741647) 19.

Definition sf_beta2 (e2 : Z) : Z := e2 + Z.shiftr (sf_k2 e2 * -1741647) 19.

Lemma sf_beta_range : forall e2, -1074 <= e2 <= 972 -> 6 <= sf_beta e2 <= 9.
Proof.
  intros e2 H.
  assert (C : all_from (fun e => (6 <=? sf_beta e) && (sf_beta e <=? 9)) (-1074) (Z.to_nat 2047) = true) by (vm_compute; reflexivity).
  pose proof (all_from_spec _ _ _ C e2 ltac:(lia)) as T. cbv beta in T.
  apply andb_prop in T. destruct T as [A B]. apply Z.leb_le in A, B. lia.
Qed.

Lemma sf_beta2_range : forall e2, -1074 <= e2 <= 972 -> 0 <= sf_beta2 e2 <= 3.
Proof.
  intros e2 H.
  assert (C : all_from (fun e => (0 <=? sf_beta2 e) && (sf_beta2 e <=? 3)) (-1074) (Z.to_nat 2047) = true) by (vm_compute; reflexivity).
  pose proof (all_from_spec _ _ _ C e2 ltac:(lia)) as T. cbv beta in T.
  apply andb_prop in T. destruct T as [A B]. apply Z.leb_le in A, B. lia.
Qed.

Lemma lor_beta_lt64 : forall b, 6 <= b <= 9 -> 0 <= Z.lor (64 - b) b < 64.
Proof. intros b H. assert (b = 6 \/ b = 7 \/ b = 8 \/ b = 9) as [->|[->|[->| ->]]] by lia; cbn; lia. Qed.

Lemma sf_prod2_small : forall e2, -1074 <= e2 <= 972 ->
  -2147483648 <= (2 - sf_k e2) * 1741647 < 2147483648 /\ -2147483648 <= sf_k2 e2 * -1741647 < 2147483648.
Proof.
  intros e2 H. pose proof (sf_k_range e2 H). pose proof (sf_k2_range e2 H). lia.
Qed.

Lemma sw32_mulc : forall x c, -2147483648 <= x * c < 2147483648 -> sw32 ((x mod 18446744073709551616) * c) = x * c.
Proof.
  intros x c H. rewrite <- (sw32_mod64 ((x mod 18446744073709551616) * c)).
  rewrite Z.mul_mod_idemp_l by lia. rewrite sw32_mod64. apply sw32_small. lia.
Qed.
Lemma mod64_mulc : forall x c, ((x mod 18446744073709551616) * c) mod 18446744073709551616 = (x * c) mod 18446744073709551616.
Proof. intros x c. apply Z.mul_mod_idemp_l. lia. Qed.

Lemma sw32_small_mod64 : forall x, -2147483648 <= x < 2147483648 -> sw32 (x mod 18446744073709551616) = x.
Proof. intros x H. rewrite sw32_mod64. apply sw32_small. exact H. Qed.

Lemma sf_beta_machine : forall e2, -1074 <= e2 <= 972 ->
  sw32 ((sw32 (Z.shiftr (sw32 (((2 - sf_k e2) * 1741647) mod 18446744073709551616)) 19)) mod 18446744073709551616
        + e2 mod 18446744073709551616) = sf_beta e2.
Proof.
  intros e2 H. pose proof (sf_prod2_small e2 H) as [P _]. pose proof (sf_beta_range e2 H) as B. unfold sf_beta in *.
  rewrite (sw32_small_mod64 ((2 - sf_k e2) * 1741647)) by lia.
  set (q := Z.shiftr ((2 - sf_k e2) * 1741647) 19) in *.
  assert (Q : -4096 <= q <= 4096).
  { unfold q. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 19) with 524288. Z.div_mod_to_equations. lia. }
  rewrite (sw32_small q) by lia.
  rewrite <- (sw32_mod64 (q mod 18446744073709551616 + e2 mod 18446744073709551616)).
  rewrite <- Z.add_mod by lia. rewrite sw32_mod64. rewrite sw32_small by lia. lia.
Qed.

Lemma sw32_sub_small : forall c b, -2147483648 <= c - b < 2147483648 -> sw32 (c - b mod 18446744073709551616) = c - b.
Proof.
  intros c b H. rewrite <- (sw32_mod64 (c - b mod 18446744073709551616)).
  rewrite Zminus_mod_idemp_r. rewrite sw32_mod64. apply sw32_small. exact H.
Qed.

Lemma sf_beta2_machine : forall e2, -1074 <= e2 <= 972 ->
  sw32 (Z.shiftr (sw32 (((sf_k2 e2 mod 18446744073709551616) * 18446744073707809969) mod 18446744073709551616)) 19) + e2 = sf_beta2 e2.
Proof.
  intros e2 H. pose proof (sf_prod2_small e2 H) as [_ P]. pose proof (sf_k2_range e2 H) as K. unfold sf_beta2.
  set (k := sf_k2 e2) in *.
  replace (((k mod 18446744073709551616) * 18446744073707809969) mod 18446744073709551616) with ((k * -1741647) mod 18446744073709551616).
  2:{ rewrite Z.mul_mod_idemp_l by lia.
      replace (k * 18446744073707809969) with (k * -1741647 + k * 18446744073709551616) by lia.
      rewrite Z.mod_add by lia. reflexivity. }
  rewrite (sw32_small_mod64 (k * -1741647)) by lia.
  set (q := Z.shiftr (k * -1741647) 19) in *.
  assert (Q : -4096 <= q <= 4096).
  { unfold q. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 19) with 524288. Z.div_mod_to_equations. lia. }
  rewrite (sw32_small q) by lia. lia.
Qed.
