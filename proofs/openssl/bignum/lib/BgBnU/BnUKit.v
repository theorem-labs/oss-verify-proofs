(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma land3_wrap : forall e, e mod 4 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 e)) 3 = 0.
Proof.
  intros e H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (2 ^ 2) with 4. Z.div_mod_to_equations. lia.
Qed.

Lemma land7_wz : forall e, e mod 8 = 0 -> Z.land (bv_unsigned (MallocRep.wz e)) 7 = 0.
Proof. intros e H. unfold MallocRep.wz. apply land7_wrap. exact H. Qed.

(* [comment removed for export] *)
Lemma snez_pos : forall p, 0 < p < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 p) = Z_to_bv 64 1.
Proof.
  intros p H. rewrite v_sltu_b2z. rewrite !unsigned_lit by lia. replace (0 <? p) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma snez_pos_wz : forall p, 0 < p < 2^64 -> v_sltu (Z_to_bv 64 0) (MallocRep.wz p) = Z_to_bv 64 1.
Proof. intros p H. unfold MallocRep.wz. apply snez_pos. exact H. Qed.
Lemma seqz_pos : forall e, 0 < e < 2^64 -> v_sltiu (Z_to_bv 64 e) 1 = Z_to_bv 64 0.
Proof.
  intros e H. rewrite v_sltiu_b2z. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  replace (e <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma lxor_1_0 : Z.lxor (bv_unsigned (Z_to_bv 64 1)) (bv_unsigned (Z_to_bv 64 0)) = 1.
Proof. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64).
  assert (L : Z.land x (Z.lxor x (Z.ones 64)) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z.ltb_spec n 64) as [Hlt|Hge].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
    - rewrite (Z.bits_above_log2 x n); [reflexivity| lia|].
      destruct (Z.eq_dec x 0) as [->|NZ]; [cbn; lia|]. assert (Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). lia. }
  pose proof (Z.add_nocarry_lxor _ _ L) as E.
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in E. lia.
Qed.
Lemma not64 : forall x, 0 <= x < 2^64 -> Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615 = 18446744073709551615 - x.
Proof. intros x H. rewrite unsigned_lit by lia. apply lxor_ones64. exact H. Qed.

(* [comment removed for export] *)
Ltac chkw tac := zstep; let C := fresh "C" in if_cases C; [ exfalso; unfold MallocRep.wz in C; zify_cond C; tac C | clear C ].
