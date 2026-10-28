(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2.

Definition EX_RTa : list (reg * expr) :=
  [(1%bv, ELit 1019416); (2%bv, EVar 58); (3%bv, EVar 50); (4%bv, EVar 51); (8%bv, EVar 33); (9%bv, EVar 58); (10%bv, EVar 36);
   (18%bv, EVar 52); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit 2147450880)); (20%bv, EVar 35);
   (21%bv, EAlu ALU_ADD (EVar 52) (ELit 32)); (22%bv, EVar 37); (23%bv, EVar 32); (24%bv, EVar 36); (25%bv, EVar 52);
   (26%bv, ELit 2147450880); (27%bv, EVar 49)].

Definition EX_RTb : list (reg * expr) :=
  [(1%bv, ELit 1019568); (2%bv, EVar 58); (3%bv, EVar 50); (4%bv, EVar 51); (8%bv, EVar 33); (9%bv, EVar 58); (10%bv, EVar 37);
   (18%bv, EVar 52); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit 2147450880)); (20%bv, EVar 35);
   (21%bv, EAlu ALU_ADD (EVar 52) (ELit 32)); (22%bv, EVar 37); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 32) (ELit 72));
   (25%bv, EVar 52); (26%bv, ELit 2147450880);
   (27%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880))].

Definition EX_RTc : list (reg * expr) :=
  [(1%bv, ELit 1019668); (2%bv, EVar 58); (3%bv, EVar 50); (4%bv, EVar 51); (8%bv, EVar 33); (9%bv, EVar 58); (18%bv, EVar 52);
   (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 18446744073709551612);
   (21%bv, EAlu ALU_ADD (EVar 52) (ELit 32)); (22%bv, EVar 61); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 32) (ELit 72));
   (25%bv, EVar 52); (26%bv, ELit 2147450880);
   (27%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880))].

