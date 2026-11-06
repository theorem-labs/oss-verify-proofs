(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib GrayLib LeptStructs LeptExec DitherLib DitherLib2 DitherTac.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope Z_scope.

Lemma dl_srlw_zero : forall j k, 0 <= k < 32 -> 0 <= j < 2 ^ k ->
  sext 64 (alu32 ALU_SRL (low32 (Z_to_bv 64 j)) (low32 (Z_to_bv 64 k))) = Z_to_bv 64 0.
Proof.
  intros j k Hk Hj. assert (2 ^ k <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
  rewrite dl_srlw_small by lia. f_equal. apply Z.div_small. lia.
Qed.

Lemma dl_or_and3 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a mod 4 = 0 -> b mod 4 = 0 ->
  alu64 ALU_AND (alu64 ALU_OR (Z_to_bv 64 a) (Z_to_bv 64 b)) (Z_to_bv 64 3) = Z_to_bv 64 0.
Proof.
  intros a b Ha Hb Ma Mb. rewrite alu_or, alu_and. unfold v_or, v_and. rewrite (u_Z2bv a), (u_Z2bv b), (u_Z2bv 3) by lia.
  assert (Hor : 0 <= Z.lor a b < 2 ^ 64).
  { split; [apply Z.lor_nonneg; lia|]. destruct (Z.eq_dec (Z.lor a b) 0) as [->|NZ]; [lia|].
    apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg a b); lia|]. rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt; (destruct (Z.eq_dec a 0) as [->|]; destruct (Z.eq_dec b 0) as [->|]; try (cbn; lia); apply Z.log2_lt_pow2; lia). }
  rewrite (u_Z2bv (Z.lor a b)) by lia. f_equal. rewrite Z.land_lor_distr_l.
  change 3 with (Z.ones 2). rewrite !Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Ma, Mb. reflexivity.
Qed.

Lemma dl_sltu_false : forall a b, 0 <= b <= a -> a < 2 ^ 64 -> alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
  intros a b Hb Ha. rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite !u_Z2bv by lia. destruct (Z.ltb_spec a b); [lia | reflexivity].
Qed.
Lemma dl_xor00 : alu64 ALU_XOR (Z_to_bv 64 0) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. apply bv_eq. reflexivity. Qed.
Lemma dl_negw1 : sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 (-1).
Proof. apply bv_eq. reflexivity. Qed.
Lemma dl_max0w : forall x, 0 < x < 2 ^ 63 ->
  alu64 ALU_AND (sext 64 (alu32 ALU_SUB (low32 (Z_to_bv 64 0)) (low32 (alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 x))))) (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. rewrite dl_slt_true by lia. rewrite dl_negw1, alu_and. unfold v_and. f_equal.
  rewrite (u_Z2bv x) by lia. change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma dl_al4m : forall a k, a mod 4 = 0 -> (a + 4 * k) mod 4 = 0.
Proof. exact dl_al4. Qed.

Ltac dl_al_side := first [ assumption | lia | (apply dl_al4; assumption) ].
Ltac dl_an_pass :=
  rewrite ?dl_addi0; rewrite ?dl_add; rewrite ?dl_addw by lia; rewrite ?dl_zext32 by lia;
  rewrite ?dl_sllw by dl_nia; rewrite ?dl_mulw by dl_nia; rewrite ?dl_add;
  rewrite ?dl_max0 by lia; rewrite ?dl_max0w by lia; rewrite ?dl_sltu0 by lia; rewrite ?dl_slt_true by lia; rewrite ?dl_slt_false by lia; rewrite ?dl_xor11; rewrite ?dl_xor01;
  rewrite ?dl_xor3 by lia; rewrite ?dl_bitword by lia; rewrite ?dl_dibitword by lia; rewrite ?dl_bitword_w by lia; rewrite ?dl_dibitword_w by lia; rewrite ?dl_mulc by dl_nia; rewrite ?dl_add; rewrite ?zbv_addi;
  rewrite ?dl_and3 by dl_al_side.
(* [comment removed for export] *)
Ltac dl_an ::= repeat (progress dl_an_pass).

Ltac dl_guard ::=
  dl_an; rewrite ?dl_srlw_zero by lia; rewrite ?dl_or_and3 by dl_al_side;
  rewrite ?dl_seqz by dl_lia; rewrite ?dl_sltu0 by dl_lia; rewrite ?dl_sltu_false by dl_lia; rewrite ?dl_slt_false by dl_lia;
  rewrite ?dl_xor00; rewrite ?dl_xor10; rewrite ?dl_xor11; rewrite ?dl_xor01;
  rewrite ?dl_and3 by first [ dl_lia | (apply dl_al4; assumption) | assumption ];
  cbn [branch_taken]; unfold bv_eqb, bv_ltu, bv_lts;
  rewrite ?bv_signed_Zs by dl_lia; rewrite ?u_Z2bv by dl_lia;
  first [ apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge
        | (apply negb_true_iff; first [apply Z.eqb_neq | apply Z.ltb_ge])
        | (apply negb_false_iff; first [apply Z.eqb_eq | apply Z.ltb_lt]) ];
  dl_lia.
