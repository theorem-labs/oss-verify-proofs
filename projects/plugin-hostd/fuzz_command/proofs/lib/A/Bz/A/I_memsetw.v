(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/I_memsetw.v, with its module paths, module names and addresses changed; 560 lines of the source are left out. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A Require Import R_small.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition icells_ms (m : mem) : Prop :=
  ro_cells asegs m 0xa63f0 [C8 (Z_to_bv 64 0xb10b8)]            (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa6f58 [C8 (Z_to_bv 64 0xb1d99)]         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa82b0 [C8 (Z_to_bv 64 0x9ef40)]         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xb10b8 [C8 (Z_to_bv 64 0x7fff8000)]      (* [comment removed for export] *)
  /\ ro_cells asegs m 0xb1d99 [C1 (Z_to_bv 8 1)].              (* [comment removed for export] *)
