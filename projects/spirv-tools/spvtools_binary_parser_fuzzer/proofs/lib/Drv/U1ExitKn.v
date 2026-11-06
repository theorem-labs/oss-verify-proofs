(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require SymExec2 SymExec3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition exit_cxx_cells : list (Z * nat * Z) :=
  [(0x1004f8, 8%nat, 0xec880);
   (0x100538, 8%nat, 0xf00e8);
   (0x100540, 8%nat, 0x100f70);
   (0x100548, 8%nat, 0x1004c4);
   (0x100558, 8%nat, 0xec880);
   (0x100598, 8%nat, 0xeff08);
   (0x1005a0, 8%nat, 0x100f70);
   (0x1005a8, 8%nat, 0x1004cc);
   (0x1005b8, 8%nat, 0xec9b0);
   (0x1005f8, 8%nat, 0xf00e8);
   (0x100600, 8%nat, 0x101100);
   (0x100608, 8%nat, 0x1004dc);
   (0x100618, 8%nat, 0xec9b0);
   (0x100658, 8%nat, 0xeff08);
   (0x100660, 8%nat, 0x101100);
   (0x100668, 8%nat, 0x1004e4);
   (0x100748, 8%nat, 0xec420);
   (0x100759, 1%nat, 0x10);
   (0x100770, 4%nat, 0x0);
   (0x100778, 8%nat, 0x1004f8);
   (0x1007d8, 8%nat, 0x0);
   (0x1007e8, 8%nat, 0xec540);
   (0x1007f9, 1%nat, 0x10);
   (0x100810, 4%nat, 0x0);
   (0x100818, 8%nat, 0x1005b8);
   (0x100878, 8%nat, 0x0);
   (0x1009c8, 8%nat, 0xec420);
   (0x1009d9, 1%nat, 0x10);
   (0x1009f0, 4%nat, 0x0);
   (0x1009f8, 8%nat, 0x100558);
   (0x100a58, 8%nat, 0x0);
   (0x100a68, 8%nat, 0xec540);
   (0x100a79, 1%nat, 0x10);
   (0x100a90, 4%nat, 0x0);
   (0x100a98, 8%nat, 0x100618);
   (0x100af8, 8%nat, 0x0);
   (0x100f70, 8%nat, 0xecef8);
   (0x101100, 8%nat, 0xecc48);
   (0x101110, 8%nat, 0x4b798);
   (0x122468, 4%nat, 0x1);
   (0x122470, 8%nat, 0x122478);
   (0x122480, 8%nat, 0x93e78);
   (0x122580, 8%nat, 0x1004b8)].

Definition AT_SLOT_CELL : Z := 0x122468.
Definition exit_cxx_common : list (Z * nat * Z) := Eval vm_compute in
  filter (fun c : Z * nat * Z => match c with (a, _, _) => negb (Z.eqb a AT_SLOT_CELL) end) exit_cxx_cells.
Definition exit_t_cells : list (Z * nat * Z) :=
  [(0x122468, 4%nat, 0x2);
   (0x122488, 8%nat, 0xd1e00);
   (0x122588, 8%nat, 0x65c64);
   (0x100254, 1%nat, 0x0)].
Definition exit_cxx_cells_t : list (Z * nat * Z) := Eval vm_compute in (exit_cxx_common ++ exit_t_cells).

Lemma exit_cxx_cells_t_split : exit_cxx_cells_t = exit_cxx_common ++ exit_t_cells.
Proof. vm_compute. reflexivity. Qed.

Definition kn_cxx_exit : list SymExec3.SX2.kentry :=
  map (fun c => match c with (a, w, v) => SymExec3.SX2.KWord (SymExec3.SX2.SA (SymExec3.SX2.ELit 0) a) w (SymExec3.SX2.ELit v) end) exit_cxx_cells.
Definition kn_cxx_exit2 : list SymExec2.SX2.kentry :=
  map (fun c => match c with (a, w, v) => SymExec2.SX2.KWord (SymExec2.SX2.SA (SymExec2.SX2.ELit 0) a) w (SymExec2.SX2.ELit v) end) exit_cxx_cells.
Definition kn_cxx_exit_t : list SymExec3.SX2.kentry :=
  map (fun c => match c with (a, w, v) => SymExec3.SX2.KWord (SymExec3.SX2.SA (SymExec3.SX2.ELit 0) a) w (SymExec3.SX2.ELit v) end) exit_cxx_cells_t.
