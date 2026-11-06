(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec SeqExec StepTac.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma testbit_high : forall n a k, 0 <= n -> 0 <= a < 2^n -> n <= k -> Z.testbit a k = false.
Proof. intros. eapply Z_testbit_high; eauto. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land_pagemask : forall x, 0 <= x < 2^64 -> Z.land x (2^64 - 4096) = x - x mod 4096.
Proof.
  intros x Hx. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec.
  assert (Em : 2^64 - 4096 = Z.shiftl (2^52 - 1) 12) by reflexivity. rewrite Em.
  assert (Ex : x - x mod 4096 = Z.shiftl (x / 2^12) 12).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. lia. }
  rewrite Ex.
  destruct (Z.lt_ge_cases k 12) as [Hl|Hg].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia.
    destruct (Z.lt_ge_cases k 64) as [Hl2|Hg2].
    + assert (Ht : Z.testbit (2^52 - 1) (k - 12) = true).
      { replace (2^52 - 1) with (Z.ones 52) by reflexivity. apply Z.ones_spec_low. lia. }
      rewrite Ht, andb_true_r. rewrite Z.div_pow2_bits by lia. f_equal. lia.
    + rewrite (testbit_high 64 x k) by lia.
      rewrite (testbit_high 52 (x / 2^12) (k - 12)); [reflexivity | lia | | lia].
      change (2^12) with 4096. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
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

Lemma v_add_ZZ : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof. intros. unfold v_add. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma v_sub_ZZ : forall x y, 0 <= y <= x -> x < 2^64 ->
  v_sub (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof. intros. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma c_ltu_Z : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  c_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros. unfold c_ltu, bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
