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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_RGl LbA_Own LbA_TablStmt LbA_TablImg LbA_TablReg LbA_TablGT.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section GT2.
  Context {HCEIL : HeapCeil}.
  Lemma gt_mid : forall x, 4417 <= x < 5281 -> gt_at x.
  Proof.
    intros x XR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
           ST CE LO S16 S47 MI AC (Hx & Ha0).
    assert (Hc : 4417 <= x < 4417 + Z.of_nat 56 \/ 4473 <= x <= 5075 \/ x = 5076 \/ 5077 <= x <= 5114 \/ x = 5115 \/ 5116 <= x <= 5280) by lia.
    destruct Hc as [H|[H|[H|[H|[H|H]]]]].
    - enum_range x 4417 56%nat H; lit_in Ha0; (rl_run_gen (@None (Z * Z)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]; bool_lit_post).
    - rl_run_gen (Some (4473, 5075)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - subst x. rl_run_gen (@None (Z * Z)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - rl_run_gen (Some (5077, 5114)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - subst x. rl_run_gen (@None (Z * Z)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
    - rl_run_gen (Some (5116, 5280)) AT_GENERATES_TYPE [GT_RET1; GT_RET0]. all: bool_lit_post.
  Qed.
End GT2.
