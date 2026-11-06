(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.

Class arun := ARun {
  aceil : Z;
  aceil_lo : 0x7fff7f800000 <= aceil;
  aceil_hi : aceil <= 0x7fffff800000;
  (* [comment removed for export] *)
  aceil_pg : aceil mod 4096 = 0 }.

Definition ACEIL_MIN : Z := 0x7fff7f800000.
Definition ACEIL_MAX : Z := 0x7fffff800000.

(* [comment removed for export] *)
Definition hull64 (x : Z) : Z := x - x mod 64.
Lemma hull64_le : forall x, hull64 x <= x < hull64 x + 64.
Proof. intros x. unfold hull64. pose proof (Z.mod_pos_bound x 64 ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Definition bottomup_floor : Z := 0x2aaaaaaab000.

Section AR. Context {hAR : arun}.
Definition ACEIL : Z := aceil.
#[using="Type"] Lemma aceil_bounds : 0x7fff7f800000 <= ACEIL <= 0x7fffff800000.
Proof. unfold ACEIL. split; [exact aceil_lo| exact aceil_hi]. Qed.
#[using="Type"] Lemma aceil_min_le : ACEIL_MIN <= ACEIL. Proof. exact aceil_lo. Qed.
#[using="Type"] Lemma aceil_le_max : ACEIL <= ACEIL_MAX. Proof. exact aceil_hi. Qed.
#[using="Type"] Lemma aceil_lt47 : ACEIL < 2^47. Proof. pose proof aceil_hi. unfold ACEIL in *. lia. Qed.
#[using="Type"] Lemma ACEIL_pg : ACEIL mod 4096 = 0. Proof. exact aceil_pg. Qed.
#[using="Type"] Lemma ACEIL_al64 : ACEIL mod 64 = 0.
Proof.
  pose proof aceil_pg as P. unfold ACEIL.
  pose proof (Z.div_mod aceil 4096 ltac:(lia)) as D. rewrite P, Z.add_0_r in D.
  rewrite D. replace (4096 * (aceil / 4096)) with ((64 * (aceil / 4096)) * 64) by lia. apply Z_mod_mult.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma ACEIL_le_hull64 : forall s, ACEIL <= s -> ACEIL <= s - s mod 64.
Proof.
  intros s H. pose proof ACEIL_al64 as A.
  pose proof (Z.div_mod ACEIL 64 ltac:(lia)) as D1. pose proof (Z.div_mod s 64 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound s 64 ltac:(lia)) as M2. rewrite A, Z.add_0_r in D1.
  assert (ACEIL / 64 <= s / 64) by (apply Z.div_le_mono; lia). nia.
Qed.

(* [comment removed for export] *)
Definition atop_ok (t : Z) : Prop := ACEIL <= t < ACEIL + 4096.
#[using="Type"] Lemma atop_ok_le : forall t, atop_ok t -> ACEIL <= t. Proof. intros t [H _]. exact H. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma atop_grant : forall t a n, atop_ok t -> a mod 4096 = 0 -> n mod 4096 = 0 -> a + n <= t -> a + n <= ACEIL.
Proof.
  intros t a n [T1 T2] A N LE. pose proof aceil_pg as P. unfold ACEIL in *.
  pose proof (Z.div_mod a 4096 ltac:(lia)) as Da. pose proof (Z.div_mod n 4096 ltac:(lia)) as Dn. pose proof (Z.div_mod aceil 4096 ltac:(lia)) as Dc.
  rewrite A, Z.add_0_r in Da. rewrite N, Z.add_0_r in Dn. rewrite P, Z.add_0_r in Dc. nia.
Qed.
End AR.
Arguments atop_ok : simpl never.
Arguments ACEIL : simpl never.

(* [comment removed for export] *)
Ltac aceilb :=
  lazymatch goal with
  | _ : 0x7fff7f800000 <= ACEIL <= 0x7fffff800000 |- _ => idtac
  | _ => let H := fresh "ACB" in pose proof aceil_bounds as H
  end.

(* [comment removed for export] *)
Ltac aceil_mentioned :=
  match goal with
  | |- context [ACEIL] => idtac
  | _ : context [ACEIL] |- _ => idtac
  end.
Lemma ACEIL_pg_ex {hAR : arun} : exists q, ACEIL = 4096 * q.
Proof. exists (ACEIL / 4096). pose proof ACEIL_pg. pose proof (Z.div_mod ACEIL 4096 ltac:(lia)). lia. Qed.
Ltac Zify.zify_pre_hook ::=
  try (lazymatch goal with
       | _ : ACEIL = 4096 * _ |- _ => idtac
       | _ => aceil_mentioned; pose proof aceil_bounds;
              let q := fresh "aceilq" in destruct ACEIL_pg_ex as [q ?]
       end).

(* [comment removed for export] *)
Definition arun_of (c : Z) (Hlo : 0x7fff7f800000 <= c) (Hhi : c <= 0x7fffff800000) (Hpg : c mod 4096 = 0) : arun := ARun c Hlo Hhi Hpg.
