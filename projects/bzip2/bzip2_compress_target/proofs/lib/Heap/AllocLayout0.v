(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition S0_static (a : Z) : Prop :=
  (0x5a970 <= a < 0x5ad88) \/ (0x5a950 <= a < 0x5a958) \/ (0x28678 <= a < 0x28680).
Definition S0_globals (segs : list Segment) (m : word -> option byte) : Prop :=
  rw_cells segs m 0x5a973 [C1 (Z_to_bv 8 0)]              (* [comment removed for export] *)
  /\ rw_cells segs m 0x5a9a0 [C8 (Z_to_bv 64 4096)]       (* [comment removed for export] *)
  /\ rw_cells segs m 0x5a9e0 [C4 (Z_to_bv 64 0)]          (* [comment removed for export] *)
  /\ rw_cells segs m 0x28678 [C8 (Z_to_bv 64 0x5a950)]    (* [comment removed for export] *)
  /\ rw_cells segs m 0x5a950 [C8 (Z_to_bv 64 run_guard)].  (* [comment removed for export] *)
Definition S0_private (a : Z) : Prop := 0x5a9e8 <= a < 0x5ad88.   (* [comment removed for export] *)
Definition S0_layout : alloc_layout :=
  mkLayout 0x1fa40 0x1f900 0x3a6e0 0x10000 0x5c000 0x28000 S0_static S0_private S0_globals 8192.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)  (* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)
(* [comment removed for export] *)


End ACeilS1.
