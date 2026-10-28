(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From Stdlib Require Import List. Import ListNotations.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib Mem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzInv BzContracts DecCut DecAux DecAuxM DecAuxL.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


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
Lemma swrap32_addm1 : forall x, 1 <= x < 2147483648 -> bv_swrap 32 (x + 18446744073709551615) = x - 1.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  replace (x + 18446744073709551615 + 2147483648) with ((x - 1 + 2147483648) + 4294967296 * 4294967296) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mod16_linR : forall x, x mod 16 = 0 -> x = 16 * (x / 16).
Proof. intros x H. pose proof (Z.div_mod x 16 ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma zbv_addm1 : forall x, Z_to_bv 64 (x + 18446744073709551615) = Z_to_bv 64 (x - 1).
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with 18446744073709551616.
  replace (x + 18446744073709551615) with ((x - 1) + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sx32_m1w : sx32 (Z_to_bv 64 (-1)) = Z_to_bv 64 (-1).
Proof. reflexivity. Qed.
Lemma swrap32_m1add : forall x, 1 <= x < 2147483648 -> bv_swrap 32 (18446744073709551615 + x) = x - 1.
Proof. intros x Hx. rewrite Z.add_comm. apply swrap32_addm1. exact Hx. Qed.

End ACeilS1.
