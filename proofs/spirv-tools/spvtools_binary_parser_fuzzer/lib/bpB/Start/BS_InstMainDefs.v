(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BothAllocModel BsMainFacts BsMainLazy.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocRep BsMainSyms.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition cert_st0 (X : pm_syms) (env : list Z) (ts : bool) : astate :=
  init_state (ps_b06 X) (pm_space_beg X) (ps_b08 X) env ts.

Definition cert_s0 (sp0z brk0z : Z) (X : pm_syms) (env : list Z) (ts : bool) (AL0 : Z) : ast :=
  mkAst (cert_st0 X env ts) (ps_b09 X) (ps_b10 X) (ps_b16 X)
        (zz2ww (PM_LAZY sp0z X)) (zz2ww (PM_S sp0z brk0z X)) (zz2ww (PM_ZR sp0z X))
        AL0 (pm_stack_top sp0z) (pm_stack_bottom sp0z).
