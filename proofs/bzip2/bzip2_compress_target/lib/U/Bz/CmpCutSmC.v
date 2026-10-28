(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA CmpCutSmB.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Definition smC_W3 (cx : cctx) (usp : Z) : list (Z * Z) :=
  [(c_E cx + 19706, c_E cx + 37708); (c_E cx + 39256, c_E cx + 45448); (usp - 16, usp); (usp + 560, usp + 592); (usp + 872, usp + 888)].

(* [comment removed for export] *)
Definition smC_hi3 (cx : cctx) (e0 : est) (nSel : Z) : list cell :=
  [C8 (Z_to_bv 64 nSel); C8 (Z_to_bv 64 3005); C8 (Z_to_bv 64 (c_E cx + 39256)); C8 (Z_to_bv 64 nSel);
   C8 (Z_to_bv 64 (flag6 (smA_ng e0))); C8 (Z_to_bv 64 (c_E cx + 1704)); C8 (Z_to_bv 64 (e_nInUse e0))].

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.
(* [comment removed for export] *)
