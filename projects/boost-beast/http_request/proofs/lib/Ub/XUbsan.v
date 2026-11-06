(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac ZBridge TacX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma land3_mod4 : forall x, Z.land x 3 = x mod 4.
Proof. intros. change 3 with (2^2 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma land1_mod2 : forall x, Z.land x 1 = x mod 2.
Proof. intros. change 1 with (2^1 - 1) at 1. rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma land15_mod16 : forall x, Z.land x 15 = x mod 16.
Proof. intros. change 15 with (2^4 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land6_of_mod8 : forall x, x mod 8 = 0 -> Z.land x 6 = 0.
Proof. intros x H. change 6 with (Z.land 7 6). rewrite Z.land_assoc, land7_mod8, H. reflexivity. Qed.

Lemma land4_of_mod8 : forall x, x mod 8 = 0 -> Z.land x 4 = 0.
Proof. intros x H. change 4 with (Z.land 7 4). rewrite Z.land_assoc, land7_mod8, H. reflexivity. Qed.

Lemma mod8_of_mod16 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. replace x with (0 + (2 * (x / 16)) * 8) by lia. rewrite Z_mod_plus_full. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lxor_m1_64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  assert (L : Z.log2 x < 64). { destruct (Z.eq_dec x 0) as [->|NE]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite <- (Z.ldiff_ones_l_low x 64) by lia.
  symmetry. apply Z.sub_nocarry_ldiff.
  rewrite Z.ldiff_ones_r_low by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma al8_of_sp16 : forall s c, s mod 16 = 0 -> c mod 8 = 0 -> (s + c) mod 8 = 0.
Proof.
  intros s c H1 H2. replace (s + c) with (c + (2 * (s / 16)) * 8) by lia.
  rewrite Z_mod_plus_full. exact H2.
Qed.

Lemma al16_of_sp16 : forall s c, s mod 16 = 0 -> c mod 16 = 0 -> (s + c) mod 16 = 0.
Proof.
  intros s c H1 H2. replace (s + c) with (c + (s / 16) * 16) by lia.
  rewrite Z_mod_plus_full. exact H2.
Qed.

(* [comment removed for export] *)
Lemma al8_off : forall a c, a mod 8 = 0 -> c mod 8 = 0 -> (a + c) mod 8 = 0.
Proof.
  intros a c H1 H2. replace (a + c) with (c + (a / 8) * 8) by lia.
  rewrite Z_mod_plus_full. exact H2.
Qed.

(* [comment removed for export] *)
Ltac notrap :=
  let K := fresh "KT" in
  step; if_cases K; zify_cond K;
  [ exfalso;
    first [ lia
          | rewrite land7_mod8 in K; lia
          | rewrite land3_mod4 in K; lia
          | rewrite lxor_m1_64 in K by lia; lia
          | rewrite land6_of_mod8 in K by lia; lia
          | rewrite land4_of_mod8 in K by lia; lia
          | let t := type of K in fail 100 "notrap: cannot refute the trap condition" t ]
  | clear K ].
