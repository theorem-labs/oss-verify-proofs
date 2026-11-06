(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib GrayLib LeptStructs LeptExec DitherLib DitherLib2 DitherTac DitherTac2 DitherTab.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope Z_scope.

Definition tvw_ok (v : word) : Prop := tv_ok (rdv true 4 (word_to_le_bytes 4 v)).

Lemma rdv_w4 : forall v : word, rdv true 4 (word_to_le_bytes 4 v) = bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned v mod 2 ^ 32))).
Proof. intros v. unfold rdv, extz. rewrite bytes_le_N. reflexivity. Qed.

(* [comment removed for export] *)
Lemma tvw_small : forall v : word, bv_unsigned v < 2 ^ 30 -> tvw_ok v.
Proof.
  intros v Hv. pose proof (u64_range v) as Rv. unfold tvw_ok. rewrite rdv_w4. rewrite Z.mod_small by lia.
  rewrite swrap32_small by lia. rewrite Z_to_bv_bv_unsigned. left. lia.
Qed.
(* [comment removed for export] *)
Lemma tvw_neg : forall y : word, bv_unsigned y < 2 ^ 30 -> tvw_ok (mul_div M_MUL (Z_to_bv 64 (-1)) y).
Proof.
  intros y Hy. pose proof (u64_range y) as Ry. unfold tvw_ok. rewrite rdv_w4, m_mul. unfold v_mul.
  change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1). rewrite !u_Z2bv_mod.
  set (t := bv_unsigned y) in *.
  destruct (Z.eq_dec t 0) as [E0|NZ].
  - rewrite E0. change ((2 ^ 64 - 1) * 0) with 0. change (0 mod 2 ^ 64 mod 2 ^ 32) with 0. change (bv_swrap 32 0) with 0. change (0 mod 2 ^ 64) with 0. left. lia.
  - replace ((2 ^ 64 - 1) * t) with (2 ^ 64 - t + (t - 1) * 2 ^ 64) by ring. rewrite Z_mod_plus_full. rewrite (Z.mod_small (2 ^ 64 - t)) by lia.
    replace (2 ^ 64 - t) with (2 ^ 32 - t + 4294967295 * 2 ^ 32) by (change (2 ^ 64) with (4294967296 * 2 ^ 32); lia).
    rewrite Z_mod_plus_full. rewrite (Z.mod_small (2 ^ 32 - t)) by lia.
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
    replace (2 ^ 32 - t + 2 ^ 31) with (2 ^ 31 - t + 1 * 2 ^ 32) by lia. rewrite Z_mod_plus_full. rewrite (Z.mod_small (2 ^ 31 - t)) by lia.
    replace (2 ^ 31 - t - 2 ^ 31) with (2 ^ 64 - t + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. right. lia.
Qed.

(* [comment removed for export] *)
Lemma srlw_small : forall (x : word) k, 2 <= k < 32 -> bv_unsigned (sext 64 (alu32 ALU_SRL (low32 x) (low32 (Z_to_bv 64 k)))) < 2 ^ 30.
Proof.
  intros x k Hk. rewrite w_srlw. unfold v_srlw. rewrite (u_Z2bv k) by lia. rewrite (Z.mod_small k 32) by lia.
  assert (W : 0 <= bv_wrap 32 (bv_unsigned x) < 2 ^ 32) by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32) with (2 ^ 32); apply Z.mod_pos_bound; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  assert (P : 2 ^ 2 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 2) with 4 in P.
  assert (D : 0 <= bv_wrap 32 (bv_unsigned x) / 2 ^ k < 2 ^ 30).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 30) with 1073741824. change (2 ^ 32) with 4294967296 in W. nia. }
  rewrite swrap32_small by lia. rewrite u_Z2bv by lia. lia.
Qed.
Lemma srl_small : forall (x : word) k, 34 <= k < 64 -> bv_unsigned (alu64 ALU_SRL x (Z_to_bv 64 k)) < 2 ^ 30.
Proof.
  intros x k Hk. pose proof (u64_range x) as Rx. rewrite alu_srl. unfold v_srl. rewrite (u_Z2bv k) by lia. rewrite (Z.mod_small k 64) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (P : 2 ^ 34 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). change (2 ^ 34) with 17179869184 in P.
  assert (D : 0 <= bv_unsigned x / 2 ^ k < 2 ^ 30).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 30) with 1073741824. change (2 ^ 64) with 18446744073709551616 in Rx. nia. }
  rewrite u_Z2bv by lia. lia.
Qed.
Lemma lit_small : forall z, 0 <= z < 2 ^ 30 -> bv_unsigned (Z_to_bv 64 z) < 2 ^ 30.
Proof. intros z Hz. rewrite u_Z2bv by lia. lia. Qed.

(* [comment removed for export] *)
Lemma dl_and11 : alu64 ALU_AND (Z_to_bv 64 1) (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof. apply bv_eq. reflexivity. Qed.
Ltac dl_an_pass ::=
  rewrite ?dl_addi0; rewrite ?dl_add; rewrite ?dl_ext4 by lia; rewrite ?dl_addw by lia; rewrite ?dl_zext32 by lia;
  rewrite ?dl_sllw by dl_nia; rewrite ?dl_mulw by dl_nia; rewrite ?dl_add;
  rewrite ?dl_max0 by lia; rewrite ?dl_max0w by lia; rewrite ?dl_sltu0 by lia; rewrite ?dl_slt_true by lia; rewrite ?dl_slt_false by lia; rewrite ?dl_xor11; rewrite ?dl_xor01;
  rewrite ?dl_xor3 by lia; rewrite ?dl_bitword by lia; rewrite ?dl_dibitword by lia; rewrite ?dl_bitword_w by lia; rewrite ?dl_dibitword_w by lia; rewrite ?dl_mulc by dl_nia; rewrite ?dl_add; rewrite ?zbv_addi;
  rewrite ?dl_and3 by dl_al_side; rewrite ?dl_and11; rewrite ?dl_sltu_false by lia; rewrite ?dl_seqz by lia.

(* [comment removed for export] *)
Ltac dl_small :=
  lazymatch goal with
  | |- bv_unsigned (sext 64 (alu32 ALU_SRL _ _)) < _ => apply srlw_small; lia
  | |- bv_unsigned (alu64 ALU_SRL _ _) < _ => apply srl_small; lia
  | |- bv_unsigned (Z_to_bv 64 _) < _ => apply lit_small; lia
  end.
(* [comment removed for export] *)
Ltac dl_tvw :=
  lazymatch goal with
  | |- tvw_ok (mul_div M_MUL (Z_to_bv 64 (-1)) _) => apply tvw_neg; dl_small
  | |- tvw_ok _ => apply tvw_small; dl_small
  end.

(* [comment removed for export] *)
Ltac dl_lia_ap :=
  match goal with H : dapart ?a _ ?b _ |- _ =>
    match goal with |- context [a] => match goal with |- context [b] =>
      let D := fresh "D" in pose proof H as D; unfold dapart in D; dl_lia end end end.
Ltac dl_saved0 ::=
  repeat match goal with
  | |- rdn _ (wbytes _ (Z_to_bv 64 ?za) _) (Z_to_bv 64 ?z) _ = _ =>
      first [ (constr_eq za z; apply dl_rdn_hit0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; dl_lia)
            | (apply dl_rdn_skip0; [ cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [dl_lia | dl_lia_ap] | ]) ]
  end.
