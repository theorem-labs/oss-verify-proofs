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

Definition EX_RTa : list (reg * expr) :=
  [(1%bv, ELit 1016928); (2%bv, EVar 58); (3%bv, EVar 50); ( 4%bv, EVar 51); (8%bv, EVar 33); (9%bv, EVar 58); ( 10%bv, EVar 36); (18%bv, EVar 52);
   (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 2147450880); (21%bv, EVar 54); (22%bv, EVar 32);
   (23%bv, EVar 55); (24%bv, EAlu ALU_ADD (EVar 52) (ELit 224)); (25%bv, EAlu ALU_ADD (EVar 52) (ELit 96)); (26%bv, EAlu ALU_ADD (EVar 52) (ELit 160));
   (27%bv, EAlu ALU_ADD (EVar 52) (ELit 32))].

Definition EX_RTb : list (reg * expr) :=
  [(1%bv, ELit 1017084); (2%bv, EVar 58); (3%bv, EVar 50); ( 4%bv, EVar 51); (8%bv, EVar 33); (9%bv, EVar 58); ( 10%bv, EVar 37); (18%bv, EVar 52);
   (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 2147450880); (21%bv, EVar 59); (22%bv, EVar 32);
   (23%bv, EAlu ALU_ADD (EVar 32) (ELit 72)); (24%bv, EAlu ALU_ADD (EVar 52) (ELit 224));
   (25%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (26%bv, EVar 35);
   (27%bv, EAlu ALU_ADD (EVar 52) (ELit 32))].

Definition EX_RTc : list (reg * expr) :=
  [(1%bv, ELit 1017184); (2%bv, EVar 58); (3%bv, EVar 50); ( 4%bv, EVar 51); (8%bv, EVar 33); (9%bv, EVar 58); ( 18%bv, EVar 52);
   (19%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 52) (ELit 3)) (ELit 2147450880)); (20%bv, ELit 18446744073709551612); (21%bv, EVar 61); ( 22%bv, EVar 32);
   (23%bv, EAlu ALU_ADD (EVar 32) (ELit 72)); (24%bv, EAlu ALU_ADD (EVar 52) (ELit 224));
   (25%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (26%bv, EVar 35);
   (27%bv, EAlu ALU_ADD (EVar 52) (ELit 32))].

