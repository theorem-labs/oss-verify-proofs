(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasT.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mtf_inv_bounds : forall mb, mtf_inv mb -> forall l, 0 <= l < 16 -> 1 + 16 * l <= mb l <= 4080 - 16 * (15 - l).
Proof.
  (intros mb; cps_intros (A & B & C); intros l Hl).
  assert (UP : forall k, (k <= 15)%nat -> forall l, 0 <= l -> l + Z.of_nat k <= 15 -> mb l + 16 * Z.of_nat k <= mb (l + Z.of_nat k)).
  { induction k; intros Hk l0 H0 H1. - change (Z.of_nat 0) with 0. rewrite Z.mul_0_r, !Z.add_0_r. lia.
    - specialize (IHk ltac:(lia) l0 H0 ltac:(lia)). specialize (B (l0 + Z.of_nat k) ltac:(lia)).
      replace (l0 + Z.of_nat (S k)) with (l0 + Z.of_nat k + 1) by lia. lia. }
  pose proof (UP (Z.to_nat l) ltac:(lia) 0 ltac:(lia) ltac:(lia)) as U1. rewrite Z.add_0_l, Z2Nat.id in U1 by lia.
  pose proof (UP (Z.to_nat (15 - l)) ltac:(lia) l ltac:(lia) ltac:(lia)) as U2. rewrite Z2Nat.id in U2 by lia.
  replace (l + (15 - l)) with 15 in U2 by lia. lia.
Qed.

Lemma mtf_home_inv : forall mb, mtf_home mb -> mtf_inv mb.
Proof.
  intros mb H. unfold mtf_inv. rewrite !H by lia. split; [lia|]. split; [|lia].
  intros l Hl. rewrite !H by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section General.
  Variables (mtfa mb : Z -> Z) (nn : Z).
  Hypothesis INV : mtf_inv mb.
  Hypothesis Hnn : 16 <= nn <= 255.
  Let lno := nn / MTFL_SIZE.
  Let off := nn mod MTFL_SIZE.

  Lemma lno_off_range : 1 <= lno <= 15 /\ 0 <= off <= 15 /\ nn = 16 * lno + off.
  Proof.
    unfold lno, off, MTFL_SIZE. pose proof (Z.div_mod nn 16 ltac:(lia)). pose proof (Z.mod_pos_bound nn 16 ltac:(lia)).
    assert (1 <= nn / 16) by (apply Z.div_le_lower_bound; lia). assert (nn / 16 < 16) by (apply Z.div_lt_upper_bound; lia). lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End General.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lxor_lt_pow2 : forall a b k, 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lxor a b < 2 ^ k.
Proof.
  intros a b k Ha Hb.
  assert (0 <= k) by (destruct (Z.neg_nonneg_cases k) as [K|K]; [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
  assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; [lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NE]; [lia|].
  apply Z.log2_lt_pow2; [lia|].
  pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)).
  destruct (Z.eq_dec a 0) as [->|]; [rewrite Z.lxor_0_l in *; apply Z.log2_lt_pow2; lia|].
  destruct (Z.eq_dec b 0) as [->|]; [rewrite Z.lxor_0_r in *; apply Z.log2_lt_pow2; lia|].
  assert (Z.log2 a < k) by (apply Z.log2_lt_pow2; lia). assert (Z.log2 b < k) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
