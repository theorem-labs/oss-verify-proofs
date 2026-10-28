(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec SymExec3 SymExec3Sound LibMaskBits.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PmArm_MaskS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmCut LbB_TablStmt LbB_PmOL.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition RT_M0 (t : Z) : list (reg * expr) := RT_ARM ++ [(18%bv, ELit t)].

Definition RT_ML : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_MLZ : list (reg * expr) := RT_ML ++ [(21%bv, ELit 0)].
Definition RT_MLF : list (reg * expr) := RT_ML ++ [(10%bv, ELit 0)].

Lemma sxw_sx32A : forall v, 0 <= v < 2 ^ 32 -> sxw v = Z_to_bv 64 (sx32A v).
Proof.
  intros v Hv. unfold sxw, sx32A, PrsGrammar.sx32. rewrite bv_swrap32_cases by lia.
  destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity|].
  rewrite (Z_to_bv_mod64 (v - 2 ^ 32)), (Z_to_bv_mod64 (v + 2 ^ 64 - 2 ^ 32)). f_equal.
  replace (v + 2 ^ 64 - 2 ^ 32) with ((v - 2 ^ 32) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma pow2_range32A : forall j, 0 <= j <= 31 -> 0 < 2 ^ j < 2 ^ 32.
Proof. intros j Hj. split; [apply Z.pow_pos_nonneg; lia|]. apply Z.pow_lt_mono_r; lia. Qed.

Lemma sx32A_range' : forall x, 0 <= x < 2 ^ 32 -> 0 <= sx32A x < 2 ^ 64 /\ (x <> 0 -> 1 <= sx32A x) /\ (sx32A x = 0 <-> x = 0).
Proof. intros x Hx. unfold sx32A, PrsGrammar.sx32. destruct (Z.ltb_spec x (2 ^ 31)); lia. Qed.

Section MaskArith.
  Variable E : env.
  Variables j wr : Z.
  Hypothesis E23 : edenot E (EVar 23) = Z_to_bv 64 (sx32A (2 ^ j)).
  Hypothesis E21 : edenot E (EVar 21) = Z_to_bv 64 (sx32A wr).
  Hypothesis HJ : 0 <= j <= 31.
  Hypothesis HWR : 0 <= wr < 2 ^ 32.

  Lemma mask_and_val :
    edenot E (EAlu ALU_AND (EVar 23) (EVar 21)) = Z_to_bv 64 (sx32A (if Z.testbit wr j then 2 ^ j else 0)).
  Proof.
    pose proof (pow2_range32A j HJ) as P.
    cbn [edenot]. cbn [edenot] in E23, E21. rewrite E23, E21.
    rewrite <- !sxw_sx32A by (try lia; destruct (Z.testbit wr j); lia).
    rewrite land_sxw by lia. rewrite land_pow2_testbit by lia. reflexivity.
  Qed.

  Lemma mask_br_set : Z.testbit wr j = true ->
    branch_taken BC_EQ (edenot E (EAlu ALU_AND (EVar 23) (EVar 21))) (edenot E (ELit 0)) = false.
  Proof.
    intros TB. pose proof (pow2_range32A j HJ) as P. rewrite mask_and_val, TB. change (edenot E (ELit 0)) with (Z_to_bv 64 0).
    destruct (sx32A_range' (2 ^ j) ltac:(lia)) as (R1 & R2 & R3).
    rewrite br_eq by lia. apply Z.eqb_neq. lia.
  Qed.

  Lemma mask_br_clr : Z.testbit wr j = false ->
    branch_taken BC_EQ (edenot E (EAlu ALU_AND (EVar 23) (EVar 21))) (edenot E (ELit 0)) = true.
  Proof.
    intros TB. rewrite mask_and_val, TB. change (edenot E (ELit 0)) with (Z_to_bv 64 0).
    change (sx32A 0) with 0. rewrite br_eq by lia. reflexivity.
  Qed.

  Lemma mask_xor_val : Z.testbit wr j = true ->
    edenot E (EAlu ALU_XOR (EVar 23) (EVar 21)) = Z_to_bv 64 (sx32A (wr - 2 ^ j)).
  Proof.
    intros TB. pose proof (pow2_range32A j HJ) as P.
    assert (Hle : 2 ^ j <= wr).
    { destruct (Z.lt_ge_cases wr (2 ^ j)) as [Hlt|]; [| lia]. exfalso.
      pose proof TB as TB'. apply Z.testbit_true in TB'; [| lia]. rewrite Z.div_small in TB' by lia. cbn in TB'. discriminate TB'. }
    cbn [edenot]. cbn [edenot] in E23, E21. rewrite E23, E21.
    rewrite <- !sxw_sx32A by lia. rewrite lxor_sxw by lia. rewrite lxor_pow2_clear by first [lia | exact TB]. reflexivity.
  Qed.

  Lemma mask_srl_val : 1 <= j ->
    edenot E (EAluw ALU_SRL (EVar 23) (ELit 1)) = Z_to_bv 64 (sx32A (2 ^ (j - 1))).
  Proof.
    clear E21 HWR. intros HJ1. pose proof (pow2_range32A j HJ) as P. pose proof (pow2_range32A (j - 1) ltac:(lia)) as P1.
    cbn [edenot]. cbn [edenot] in E23. rewrite E23. change (Z_to_bv 64 1) with (Z_to_bv 64 1).
    rewrite <- !sxw_sx32A by lia. apply srliw1_mask. lia.
  Qed.
End MaskArith.
