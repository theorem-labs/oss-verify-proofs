(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzLemmasMtf.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shl32_shr32 : forall x, (0 <= x < 2^32)%Z -> (x * 4294967296 / 4294967296 = x)%Z.
Proof. intros. now rewrite Z.div_mul by lia. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land_ones64_l : forall y, (0 <= y < 2^64)%Z -> Z.land 18446744073709551615 y = y.
Proof. intros y Hy. rewrite Z.land_comm. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land_0_l : forall y, Z.land 0 y = 0%Z.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lxor_byte_bit : forall a b, (0 <= a < 256)%Z -> (0 <= b <= 1)%Z -> (0 <= Z.lxor a b < 256)%Z.
Proof.
  intros a b Ha Hb. apply (lxor_lt_pow2 _ _ 8); cbn; lia.
Qed.
Lemma land255_range : forall x, (0 <= Z.land x 255 < 256)%Z.
Proof. intros. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma swrap32_mod256 : forall u, (bv_swrap 32 u mod 256 = u mod 256)%Z.
Proof.
  intros u. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  set (q := ((u + 2^31) / 2^32)%Z).
  pose proof (Z.div_mod (u + 2^31) (2^32) ltac:(lia)) as E. fold q in E.
  replace ((u + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31)%Z with (u + (- q * 16777216) * 256)%Z by lia.
  apply Z.mod_add. lia.
Qed.

(* [comment removed for export] *)
Lemma le1_sx32 : forall w : word, le1 (sx32 w) = [Z_to_bv 8 (bv_unsigned w)].
Proof.
  intros w. unfold sx32. rewrite le1_lit. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8)%Z with 256%Z. apply swrap32_mod256.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rtpos_wrap : forall rT, (0 <= rT < 512)%Z ->
  Z.land ((Z.b2z ((rT + -511) mod 18446744073709551616 <? 1) + -1) mod 18446744073709551616) (rT + 1) = ((rT + 1) mod 512)%Z.
Proof.
  intros rT H. destruct (Z.eq_dec rT 511) as [->|NE]; [reflexivity|].
  replace ((rT + -511) mod 18446744073709551616)%Z with (rT + -511 + 18446744073709551616)%Z.
  2:{ apply (Z.mod_unique_pos _ _ (-1)%Z); lia. }
  replace (rT + -511 + 18446744073709551616 <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616)%Z with 18446744073709551615%Z.
  rewrite land_ones64_l by lia. rewrite Z.mod_small; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


End ACeilS1.
