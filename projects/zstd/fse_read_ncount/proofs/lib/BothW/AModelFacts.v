(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia Bool.
From stdpp Require Import bitvector.definitions.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rz_size_eq : forall n, rz_size n = 16 * 2 ^ rz_log n.
Proof. intros n. unfold rz_size. rewrite Z.shiftl_mul_pow2. reflexivity. unfold rz_log.
repeat (destruct (_ <=? _)); lia. Qed.
#[using="Type"] Lemma rounded_size_eq : forall n, rounded_size n = (Z.max n 8 + 7) / 8 * 8.
Proof. intros n. unfold rounded_size, rup. f_equal. f_equal. lia. Qed.
#[using="Type"] Lemma land_align8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
intros x Hx.
replace 18446744073709551608 with (Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity.
replace (x - x mod 8) with (Z.shiftl (Z.shiftr x 3) 3).
2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
rewrite <- Z.ldiff_ones_r by lia.
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
destruct (Z.ltb_spec i 64) as [L|L]; cbn.
- reflexivity.
- destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
#[using="Type"] Lemma rounded_size_align : forall n, rounded_size n = Z.max n 8 + 7 - (Z.max n 8 + 7) mod 8.
Proof. intros n. rewrite rounded_size_eq. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma land_align8_48 : forall x, 0 <= x < 2^48 -> Z.land x 281474976710648 = x - x mod 8.
Proof.
intros x Hx.
replace 281474976710648 with (Z.ldiff (Z.ones 48) (Z.ones 3)) by reflexivity.
replace (x - x mod 8) with (Z.shiftl (Z.shiftr x 3) 3).
2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
rewrite <- Z.ldiff_ones_r by lia.
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
destruct (Z.ltb_spec i 48) as [L|L]; cbn.
- reflexivity.
- destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
apply Z.lt_le_trans with 48; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
#[using="Type"] Lemma a_next_put_cls : forall c r st, a_next (put_cls c r st) = a_next st.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma a_live_put_cls : forall c r st, a_live (put_cls c r st) = a_live st.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma size_of_class_small : forall c, c <= 16 -> size_of_class c = 32 * c.
Proof. intros c Hc. unfold size_of_class. replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
End CANSEC1.
