(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec SymExec3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_DKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_SnTA.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2.

Definition SNX_D1 : Z := 0xf92ac.
Definition SNX_D2 : Z := 0xf96a0.

Definition SNX_RT : list (reg * expr) :=
  [(1%bv, ELit 1019280); (2%bv, EVar 58); (3%bv, EVar 50); (4%bv, EVar 51); (8%bv, EVar 33); (9%bv, EVar 58); (18%bv, EVar 52);
   (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit 2147450880)); (20%bv, EVar 36); (21%bv, EVar 32); (22%bv, EVar 35);
   (23%bv, ELit 2147450880); (24%bv, EVar 46); (25%bv, EVar 47); (26%bv, EVar 52); (27%bv, EVar 49)].

Definition SNX_SF : list fent := [(16, 8%nat, EVar 52)].

Definition SNX_FT : list fent := [(0, 8%nat, ELit 1102416563); (8, 8%nat, ELit 95127); (16, 8%nat, ELit 1019160)].

Definition SNX_HT : list fent := LbA_SnTA.HT4.
