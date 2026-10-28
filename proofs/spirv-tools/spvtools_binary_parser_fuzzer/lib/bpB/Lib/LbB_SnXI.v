(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnTA.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2.

Definition SNX_D1 : Z := 0xf98d0.
Definition SNX_D2 : Z := 0xf9bf8.

Definition SNX_RT : list (reg * expr) :=
  [(1%bv, ELit 1020988); (2%bv, EVar 58); (3%bv, EVar 50); (4%bv, EVar 51); (8%bv, EVar 33); (9%bv, EVar 58); (18%bv, EVar 52);
   (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit 2147450880)); (20%bv, EVar 36); (21%bv, EVar 32); (22%bv, EVar 35);
   (23%bv, EVar 52); (24%bv, ELit 2147450880); (25%bv, EVar 47); (26%bv, EVar 48); (27%bv, EVar 49)].

Definition SNX_SF : list fent := [(8, 8%nat, EVar 52)].

Definition SNX_FT : list fent := [(0, 8%nat, ELit 1102416563); (8, 8%nat, ELit 127831); (16, 8%nat, ELit 1020880)].

Definition SNX_HT : list fent := LbB_SnTA.HT4.
