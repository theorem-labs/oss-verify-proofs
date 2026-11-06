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
  [(0xfe798, 8%nat, 0xeab28);
   (0xfe7d8, 8%nat, 0xee390);
   (0xfe7e0, 8%nat, 0xff210);
   (0xfe7e8, 8%nat, 0xfe764);
   (0xfe7f8, 8%nat, 0xeab28);
   (0xfe838, 8%nat, 0xee1b0);
   (0xfe840, 8%nat, 0xff210);
   (0xfe848, 8%nat, 0xfe76c);
   (0xfe858, 8%nat, 0xeac58);
   (0xfe898, 8%nat, 0xee390);
   (0xfe8a0, 8%nat, 0xff3a0);
   (0xfe8a8, 8%nat, 0xfe77c);
   (0xfe8b8, 8%nat, 0xeac58);
   (0xfe8f8, 8%nat, 0xee1b0);
   (0xfe900, 8%nat, 0xff3a0);
   (0xfe908, 8%nat, 0xfe784);
   (0xfe9e8, 8%nat, 0xea6c8);
   (0xfe9f9, 1%nat, 0x10);
   (0xfea10, 4%nat, 0x0);
   (0xfea18, 8%nat, 0xfe798);
   (0xfea78, 8%nat, 0x0);
   (0xfea88, 8%nat, 0xea7e8);
   (0xfea99, 1%nat, 0x10);
   (0xfeab0, 4%nat, 0x0);
   (0xfeab8, 8%nat, 0xfe858);
   (0xfeb18, 8%nat, 0x0);
   (0xfec68, 8%nat, 0xea6c8);
   (0xfec79, 1%nat, 0x10);
   (0xfec90, 4%nat, 0x0);
   (0xfec98, 8%nat, 0xfe7f8);
   (0xfecf8, 8%nat, 0x0);
   (0xfed08, 8%nat, 0xea7e8);
   (0xfed19, 1%nat, 0x10);
   (0xfed30, 4%nat, 0x0);
   (0xfed38, 8%nat, 0xfe8b8);
   (0xfed98, 8%nat, 0x0);
   (0xff210, 8%nat, 0xeb1a0);
   (0xff3a0, 8%nat, 0xeaef0);
   (0xff3b0, 8%nat, 0x4b7d0);
   (0x100688, 8%nat, 0x120980);
   (0x120708, 4%nat, 0x1);
   (0x120710, 8%nat, 0x120718);
   (0x120720, 8%nat, 0x92120);
   (0x120820, 8%nat, 0xfe758)].

Definition AT_SLOT_CELL : Z := 0x120708.
Definition exit_cxx_common : list (Z * nat * Z) := Eval vm_compute in
  filter (fun c : Z * nat * Z => match c with (a, _, _) => negb (Z.eqb a AT_SLOT_CELL) end) exit_cxx_cells.
Definition exit_t_cells : list (Z * nat * Z) :=
  [(0x120708, 4%nat, 0x2);
   (0x120728, 8%nat, 0xd00a8);
   (0x120828, 8%nat, 0x65a10);
   (0xfe4f4, 1%nat, 0x0)].
Definition exit_cxx_cells_t : list (Z * nat * Z) := Eval vm_compute in (exit_cxx_common ++ exit_t_cells).

Lemma exit_cxx_cells_t_split : exit_cxx_cells_t = exit_cxx_common ++ exit_t_cells.
Proof. vm_compute. reflexivity. Qed.

Definition kn_cxx_exit : list SymExec3.SX2.kentry :=
  map (fun c => match c with (a, w, v) => SymExec3.SX2.KWord (SymExec3.SX2.SA (SymExec3.SX2.ELit 0) a) w (SymExec3.SX2.ELit v) end) exit_cxx_cells.
Definition kn_cxx_exit2 : list SymExec2.SX2.kentry :=
  map (fun c => match c with (a, w, v) => SymExec2.SX2.KWord (SymExec2.SX2.SA (SymExec2.SX2.ELit 0) a) w (SymExec2.SX2.ELit v) end) exit_cxx_cells.
Definition kn_cxx_exit_t : list SymExec3.SX2.kentry :=
  map (fun c => match c with (a, w, v) => SymExec3.SX2.KWord (SymExec3.SX2.SA (SymExec3.SX2.ELit 0) a) w (SymExec3.SX2.ELit v) end) exit_cxx_cells_t.
