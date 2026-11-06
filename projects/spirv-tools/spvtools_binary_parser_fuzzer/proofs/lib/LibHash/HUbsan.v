(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HWord.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma align16_8 : forall p, p mod 16 = 0 -> p mod 8 = 0.
Proof. intros p Hp. rewrite <- (Z.mod_mod_divide p 16 8 ltac:(exists 2; reflexivity)), Hp. reflexivity. Qed.
Lemma align8_add : forall b k, b mod 8 = 0 -> (8 * k + b) mod 8 = 0.
Proof. intros b k Hb. rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia. exact Hb. Qed.

Section Ubsan.
  Variable SEGS : list Segment.

  Lemma sc_trap_align : forall M E e a, edenot E e = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> a mod 8 = 0 ->
    sc_denot SEGS M E (SCBr false BC_NE (EAlu ALU_AND e (ELit 7)) (ELit 0)).
  Proof using SEGS.
    intros M E e a He Ha Hal. cbn [sc_denot]. cbn [edenot]. rewrite He.
    rewrite w_and by lia. rewrite land_7, Hal. reflexivity.
  Qed.

  Lemma sc_trap_null : forall M E e a, edenot E e = Z_to_bv 64 a -> 0 < a < 2 ^ 64 ->
    sc_denot SEGS M E (SCBr false BC_EQ e (ELit 0)).
  Proof using SEGS.
    intros M E e a He Ha. cbn [sc_denot]. rewrite He. cbn [edenot]. rewrite br_eq by lia.
    destruct (Z.eqb_spec a 0); [lia | reflexivity].
  Qed.

  Lemma sc_trap_wrap : forall M E e1 e2 a k, edenot E e1 = Z_to_bv 64 (a + k) -> edenot E e2 = Z_to_bv 64 a ->
    0 <= a -> 0 <= k -> a + k < 2 ^ 64 ->
    sc_denot SEGS M E (SCBr false BC_LTU e1 e2).
  Proof using SEGS.
    intros M E e1 e2 a k H1 H2 Ha Hk Hak. cbn [sc_denot]. rewrite H1, H2. rewrite br_ltu by lia.
    destruct (Z.ltb_spec (a + k) a); [lia | reflexivity].
  Qed.

  Lemma sc_trap_nullxor : forall M E e1 e2 a k, edenot E e2 = Z_to_bv 64 a -> edenot E e1 = Z_to_bv 64 (a + k) ->
    0 < a -> 0 <= k -> a + k < 2 ^ 64 ->
    sc_denot SEGS M E (SCBr false BC_EQ (EAlu ALU_XOR (EAlu ALU_SLTU (ELit 0) e2) (EAlu ALU_SLTU e1 (ELit 1))) (ELit 0)).
  Proof using SEGS.
    intros M E e1 e2 a k H2 H1 Ha Hk Hak. cbn [sc_denot]. cbn [edenot]. rewrite H1, H2.
    rewrite !w_sltu by lia.
    replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (a + k <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite w_xor by lia. reflexivity.
  Qed.

  Lemma sc_trap_srl : forall M E e a k, edenot E e = Z_to_bv 64 a -> 0 <= k < 64 -> 0 <= a < 2 ^ k ->
    sc_denot SEGS M E (SCBr false BC_NE (EAlu ALU_SRL e (ELit k)) (ELit 0)).
  Proof using SEGS.
    intros M E e a k He Hk Ha. cbn [sc_denot]. cbn [edenot]. rewrite He.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (split; [lia|]; eapply Z.lt_le_trans; [apply (proj2 Ha)|]; apply Z.pow_le_mono_r; lia).
    rewrite w_srl by lia. rewrite (Z.div_small a (2 ^ k)) by lia. reflexivity.
  Qed.

  Lemma sc_trap_notlt : forall M E e1 e2 p k, edenot E e1 = Z_to_bv 64 (2 ^ 64 - 1 - p) -> edenot E e2 = Z_to_bv 64 k ->
    0 <= p -> 0 <= k -> p + k < 2 ^ 64 ->
    sc_denot SEGS M E (SCBr false BC_LTU e1 e2).
  Proof using SEGS.
    intros M E e1 e2 p k H1 H2 Hp Hk Hpk. cbn [sc_denot]. rewrite H1, H2. rewrite br_ltu by lia.
    destruct (Z.ltb_spec (2 ^ 64 - 1 - p) k); [lia | reflexivity].
  Qed.
End Ubsan.
