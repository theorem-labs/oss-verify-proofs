(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Record s3w := S3W { w8 : word; w24 : word; w48 : word; w56 : word; w64 : word; w72 : word; w80 : word; w88 : word;
                    w104 : word; w112 : word; w120 : word; w136 : word; w152 : word; w160 : word; w168 : word; w176 : word;
                    w568 : word }.

(* [comment removed for export] *)
Definition sdW3 (cx : cctx) (usp : Z) : list (Z * Z) :=
  [(c_E cx + 116, c_E cx + 120); (c_E cx + 640, c_E cx + 648); (c_A2 cx, c_A2 cx + ARR2_SIZE); (usp + 872, usp + 888)].

Section S3Bundle.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (nG nSel : Z) (usp : Z) (sv : word) (W : s3w).
  Local Notation E := (c_E cx). Local Notation A1 := (c_A1 cx). Local Notation A2 := (c_A2 cx). Local Notation J := (c_J cx).

  (* [comment removed for export] *)
  Definition sd_lo3 : list cell :=
    [C8 (w8 W); C8 (Z_to_bv 64 (E + 128)); C8 (w24 W); C8 (Z_to_bv 64 (e_nInUse e + 2)); C8 sv;
     C8 (w48 W); C8 (w56 W); C8 (w64 W); C8 (w72 W); C8 (w80 W); C8 (w88 W); C8 (Z_to_bv 64 nG);
     C8 (w104 W); C8 (w112 W); C8 (w120 W); C8 (Z_to_bv 64 (E + 37708)); C8 (w136 W); C8 (Z_to_bv 64 A1);
     C8 (w152 W); C8 (w160 W); C8 (w168 W); C8 (w176 W)].
  (* [comment removed for export] *)
  Definition sd_hi3 : list cell :=
    [C8 (Z_to_bv 64 nSel); C8 (w568 W); C8 (Z_to_bv 64 (E + 39256)); C8 (Z_to_bv 64 nSel);
     C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))].
  (* [comment removed for export] *)
End S3Bundle.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.
(* [comment removed for export] *)
