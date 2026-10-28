(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition S0_static (a : Z) : Prop :=
  (0x64470 <= a < 0x64888) \/ (0x64450 <= a < 0x64458) \/ (0x32138 <= a < 0x32140).
Definition S0_globals (segs : list Segment) (m : word -> option byte) : Prop :=
  rw_cells segs m 0x64473 [C1 (Z_to_bv 8 0)]              (* [comment removed for export] *)
  /\ rw_cells segs m 0x644a0 [C8 (Z_to_bv 64 4096)]       (* [comment removed for export] *)
  /\ rw_cells segs m 0x644e0 [C4 (Z_to_bv 64 0)]          (* [comment removed for export] *)
  /\ rw_cells segs m 0x32138 [C8 (Z_to_bv 64 0x64450)]    (* [comment removed for export] *)
  /\ rw_cells segs m 0x64450 [C8 (Z_to_bv 64 run_guard)].  (* [comment removed for export] *)
Definition S0_private (a : Z) : Prop := 0x644e8 <= a < 0x64888.   (* [comment removed for export] *)
Definition S0_layout : alloc_layout :=
  mkLayout 0x29504 0x293c4 0x441e0 0x10000 0x66000 0x32000 S0_static S0_private S0_globals 8192.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)  (* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)
(* [comment removed for export] *)


End ACeilS1.
