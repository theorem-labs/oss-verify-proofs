(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BSymExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BLibKnowFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BRefExitBase BRefStdioDefs BsStdioCall BsPrintfFirst.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsCarryKeep.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Definition AEXIT : Z := 0x165478.
Definition AEXIT_ECALL : Z := 0x165188.
Definition AX_FR : Z := 400.
Definition XFUEL : nat := 20000.
Definition XSTOPS : list Z := [0x16cdd0]%Z.

Definition x_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0 | 4 => ELit 0x6c5858%Z | 10 => EVar 2
                          | _ => EVar (8 + i) end)%nat (seq 0 32)).

Definition ax_lit_cells : list (Z * nat * Z) :=
  [(0x6e5ac8, 4%nat, 0);
   (0x6e5aeb, 1%nat, 0);
   (0x6e58ac, 4%nat, 0);
   (0x6e58b0, 4%nat, 3);
   (0x6e58b8, 8%nat, 0x6e58c0);
   (0x6e58c0, 8%nat, 0);
   (0x6e58c8, 8%nat, 0x165424);
   (0x6e59c8, 8%nat, 0xd7e54);
   (0x222ee0, 1%nat, 0);
   (0x18d9d0, 1%nat, 0);
   (0x186f40, 8%nat, 0x186f40);
   (0x18d980, 8%nat, 1);
   (0x19089c, 1%nat, 1);
   (0x191d18, 1%nat, 1);
   (0x191038, 8%nat, 0x7fff8000);
   (0x18e8f0, 8%nat, 0);
   (0x18e850, 4%nat, 1);
   (0x187148, 8%nat, 0x176ea4);
   (0x222be0, 8%nat, 0xffffffffffffffff);
   (0x6e6060, 8%nat, 0);
   (0x1899ac, 4%nat, 0xffffffff);
   (0x189b8c, 4%nat, 0xffffffff);

   (0x6e58d0, 8%nat, 0x126ca0); (0x6e58d8, 8%nat, 0xae38c); (0x6e59d0, 8%nat, 0x6c38f8); (0x6e59d8, 8%nat, 0)]%Z.

Definition ax_flush_cells : list (Z * nat * Z) :=
  [(0x189b38, 8%nat, 0x6e6480); (0x189b48, 8%nat, 0x16cdd0); (0x189b58, 8%nat, 0x6e6480); (0x189b60, 8%nat, 1024); (0x189b78, 4%nat, 1)]%Z.

Definition scr0 : scripts := SCR [] [] [].

Definition keep_nonshadow (K : kentry) : bool :=
  match K with
  | KWord (SA (ELit 0) a) _ _ => negb ((0x7fff0000 <=? a) && (a <? 0x900000000))%Z
  | _ => true
  end.
Definition kn_drop_shadow (kn : list kentry) : list kentry := List.filter keep_nonshadow kn.

Definition one_carry (a : Z) (w : nat) (v : expr) (kn : list kentry) : list kentry :=
  fst (fst (carry [SE (SA (ELit 0) a) w v] kn [])).
