(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsWalk.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_RGl LbA_Own LbA_TablStmt LbA_TablImg LbA_TablReg LbA_TablGT LbA_TablGT2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section GT3.
  Context {HCEIL : HeapCeil}.
  Lemma gt_hi : forall x, 5281 <= x -> gt_at x.
  Proof.
    intros x XR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC (Hx & Ha0).
    assert (Hc : 5281 <= x < 5281 + Z.of_nat 61 \/ 5342 <= x <= 5357 \/ 5358 <= x < 5358 + Z.of_nat 14 \/ 5372 <= x <= 6198
                 \/ x = 6199 \/ 6200 <= x <= 2 ^ 32 - 1) by lia.
    destruct Hc as [H|[H|[H|[H|[H|H]]]]].
    - enum_range x 5281 61%nat H; lit_in Ha0; (rl_run_gen (@None (Z * Z)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]; bool_lit_post).
    - rl_run_gen (Some (5342, 5357)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - enum_range x 5358 14%nat H; lit_in Ha0; (rl_run_gen (@None (Z * Z)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]; bool_lit_post).
    - rl_run_gen (Some (5372, 6198)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - subst x. rl_run_gen (@None (Z * Z)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - rl_run_gen (Some (6200, 2 ^ 32 - 1)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
  Qed.

  Theorem generates_type_okA : generates_type_stmtA.
  Proof.
    intros x. destruct (Z_lt_le_dec x 4417) as [L|L]; [exact (gt_lo x L)|].
    destruct (Z_lt_le_dec x 5281) as [M|M]; [exact (gt_mid x (conj L M)) | exact (gt_hi x M)].
  Qed.
End GT3.
