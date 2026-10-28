(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition smB_W3 (cx : cctx) (usp : Z) : list (Z * Z) :=
  [(c_E cx + 1704, c_E cx + 19706); (c_E cx + 37708, c_E cx + 39256); (c_E cx + 45448, c_E cx + 55768);
   (usp - HM_FRAME, usp); (usp + 104, usp + 112); (usp + 184, usp + 640); (usp + 888, usp + 900)].

(* [comment removed for export] *)
Definition smB_slots3 (cx : cctx) (e : est) (usp : Z) (sv w24 w56 : word) : list cell :=
  let E := c_E cx in let A1 := c_A1 cx in let A := sm_alpha e in let nG := smA_ng e in
  [C8 (Z_to_bv 64 37450); C8 (Z_to_bv 64 (E + 128)); C8 w24; C8 (Z_to_bv 64 A); C8 sv; C8 (Z_to_bv 64 (E + 38998)); C8 w56;
   C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (nG - 1)); C8 (Z_to_bv 64 (4 * A)); C8 (Z_to_bv 64 (E + 45448 + 1032 * nG));
   C8 (Z_to_bv 64 nG); C8 (Z_to_bv 64 4); C8 (Z_to_bv 64 (A1 + 2)); C8 (Z_to_bv 64 (E + 51648 + 16 * A)); C8 (Z_to_bv 64 (E + 37708));
   C8 (Z_to_bv 64 (E + 51640)); C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (usp + 616 + 4 * nG));
   C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (E + 45448))].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.
(* [comment removed for export] *)
