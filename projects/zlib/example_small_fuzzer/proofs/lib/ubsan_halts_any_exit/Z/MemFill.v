(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition ms_u32 (c : Z) : Z := ((c mod 2 ^ 8) * 2 ^ 8 + c mod 2 ^ 8) * 2 ^ 16 + ((c mod 2 ^ 8) * 2 ^ 8 + c mod 2 ^ 8).
Definition ms_c32 (c : Z) : Z := szwrap 32 (ms_u32 c).
Definition ms_c64 (c : Z) : Z := ms_c32 c * 2 ^ 32 + ms_u32 c.

Fixpoint allb (n : nat) (f : Z -> bool) : bool :=
  match n with O => true | S n' => f (Z.of_nat n') && allb n' f end.

Lemma allb_ok : forall n f, allb n f = true -> forall z, 0 <= z < Z.of_nat n -> f z = true.
Proof.
  induction n as [|n IH]; intros f H z Hz; [lia|].
  cbn [allb] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec z (Z.of_nat n)) as [->|Hne]; [exact H1|]. apply IH; [exact H2 | lia].
Qed.

Definition cst_ok (lo hi : Z) (p : Z * nat) : Prop :=
  0 <= fst p /\ fst p + Z.of_nat (snd p) <= 2 ^ 64 /\ lo <= fst p /\ fst p + Z.of_nat (snd p) <= hi.

Ltac prove_In := cbn [In]; repeat (first [ left; reflexivity | right ]).

Lemma land_neg_pow2 : forall x n, 0 <= n -> Z.land x (- 2 ^ n) = x - x mod 2 ^ n.
Proof.
  intros x n Hn.
  replace (- 2 ^ n) with (Z.lnot (Z.ones n)) by (unfold Z.ones; rewrite Z.shiftl_1_l; unfold Z.lnot; lia).
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod x (2 ^ n) ltac:(lia)). lia.
Qed.

Lemma land_m4 : forall x, Z.land x (-4) = x - x mod 4.
Proof. intros x. exact (land_neg_pow2 x 2 ltac:(lia)). Qed.
Lemma land_m32 : forall x, Z.land x (-32) = x - x mod 32.
Proof. intros x. exact (land_neg_pow2 x 5 ltac:(lia)). Qed.

Lemma land_4 : forall y, Z.land y 4 = y mod 8 - y mod 4.
Proof.
  intros y.
  assert (E7 : Z.land y 7 = y mod 8) by (change 7 with (Z.ones 3); apply Z.land_ones; lia).
  assert (E : Z.land y 4 = Z.land (Z.land y 7) 4).
  { rewrite <- Z.land_assoc. reflexivity. }
  rewrite E, E7.
  pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as Hr.
  assert (H8 : forall r, 0 <= r < 8 -> Z.land r 4 = r - r mod 4).
  { intros r Hr8.
    pose proof (allb_ok 8 (fun r => Z.eqb (Z.land r 4) (r - r mod 4)) ltac:(vm_compute; reflexivity) r Hr8) as Hb.
    apply Z.eqb_eq in Hb. exact Hb. }
  rewrite H8 by lia.
  enough (E4 : (y mod 8) mod 4 = y mod 4) by lia.
  apply Z.mod_mod_divide. exists 2. reflexivity.
Qed.

Definition iv (a : Z) (k : nat) : Z * Z := (a, a + Z.of_nat k).



Lemma memset_lin_facts : forall s n : Z, exists K N1 B N2 q1 q2 : Z,
  K = (0 - s) mod 4 /\ N1 = Z.land (n - K) (-4) /\ B = Z.land (s + K) 4 /\
  N2 = Z.land (N1 - B + -24) (-32) /\
  0 <= K < 4 /\ N1 = 4 * q1 /\ n - K - 3 <= N1 <= n - K /\ (B = 0 \/ B = 4) /\
  N2 = 32 * q2 /\ N1 - B - 24 - 31 <= N2 <= N1 - B - 24.
Proof.
  intros s n.
  set (K := (0 - s) mod 4). set (N1 := Z.land (n - K) (-4)). set (B := Z.land (s + K) 4).
  set (N2 := Z.land (N1 - B + -24) (-32)).
  exists K, N1, B, N2, ((n - K) / 4), ((N1 - B + -24) / 32).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  assert (LK : 0 <= K < 4) by (subst K; apply Z.mod_pos_bound; lia).
  assert (LN1 : N1 = 4 * ((n - K) / 4) /\ n - K - 3 <= N1 <= n - K).
  { subst N1. rewrite land_m4. pose proof (Z.div_mod (n - K) 4 ltac:(lia)).
    pose proof (Z.mod_pos_bound (n - K) 4 ltac:(lia)). lia. }
  assert (LB : B = 0 \/ B = 4).
  { subst B. rewrite land_4. pose proof (Z.mod_pos_bound (s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (s + K) 4 ltac:(lia)).
    pose proof (Z.div_mod (s + K) 8 ltac:(lia)). pose proof (Z.div_mod (s + K) 4 ltac:(lia)). lia. }
  assert (LN2 : N2 = 32 * ((N1 - B + -24) / 32) /\ N1 - B - 24 - 31 <= N2 <= N1 - B - 24).
  { subst N2. rewrite land_m32. pose proof (Z.div_mod (N1 - B + -24) 32 ltac:(lia)).
    pose proof (Z.mod_pos_bound (N1 - B + -24) 32 ltac:(lia)). lia. }
  lia.
Qed.
