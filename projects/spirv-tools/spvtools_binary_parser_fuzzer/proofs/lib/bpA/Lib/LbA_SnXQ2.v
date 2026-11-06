(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec SymExec3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_DKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2.

Definition SX_RT7 : list (reg * expr) :=
  [(1%bv, ELit 1022068); (2%bv, EVar 58); (3%bv, EVar 50); ( 4%bv, EVar 51); (8%bv, EVar 33); (9%bv, EVar 58); (10%bv, EAlu ALU_ADD (EVar 52) (ELit 880));
   (11%bv, ELit 152096); (12%bv, ELit 8); (18%bv, EVar 52); (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit 2147450880)); (20%bv, EVar 36);
   (21%bv, ELit 18446744073709551608); (22%bv, EAlu ALU_ADD (EVar 52) (ELit 880)); (23%bv, EAlu ALU_ADD (EVar 52) (ELit 96));
   (24%bv, EAlu ALU_ADD (EVar 52) (ELit 160)); (25%bv, EAlu ALU_ADD (EVar 52) (ELit 32)); (26%bv, EVar 52); (27%bv, EVar 55)].

Definition SX_SF7 : list fent :=
  [(16, 8%nat, EVar 52)].

Definition SX_RT9 : list (reg * expr) :=
  [(1%bv, ELit 1022112); (2%bv, EVar 58); (3%bv, EVar 50); ( 4%bv, EVar 51); (8%bv, EVar 33); (9%bv, EVar 58); ( 18%bv, EVar 52);
   (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 18446744073709551612); (21%bv, ELit 18446744073709551608);
   (22%bv, EAlu ALU_ADD (EVar 52) (ELit 880)); (23%bv, EAlu ALU_ADD (EVar 52) (ELit 96)); (24%bv, EAlu ALU_ADD (EVar 52) (ELit 160));
   (25%bv, EAlu ALU_ADD (EVar 52) (ELit 32)); (26%bv, EVar 52); (27%bv, EVar 55)].

