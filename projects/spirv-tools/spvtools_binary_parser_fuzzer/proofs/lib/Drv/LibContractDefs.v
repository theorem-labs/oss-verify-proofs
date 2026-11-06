(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Export LibContractS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom LibIface LibBudget S1Layout U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ Require Import MallocInstS1 MallocInstU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import DrvLibContract S1Statics U1Statics.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require S1TargetConsts U1TargetConsts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition lib_contract_U1 : Prop :=
  forall (AC : AllocCeiling) (RRND : RunRandom),
    lib_call_stmt U1Layout.SEGS U1Layout.L MI_U1 U1ST
      U1TargetConsts.LLVM_ENTRY U1TargetConsts.EMPTY_OBJ LIB_STACK lib_caps LIB_BIGCAP
      U1TargetConsts.TD_LOCALE U1TargetConsts.GLOBAL_LOCALE.
