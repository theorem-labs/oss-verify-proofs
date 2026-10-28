(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Definition flag6 (nG : Z) : Z := if nG =? 6 then 1 else 0.

(* [comment removed for export] *)
Definition smA_W3 (cx : cctx) (usp : Z) : list (Z * Z) :=
  [(c_E cx + 37708, c_E cx + 39256); (usp + 8, usp + 184); (usp + 576, usp + 616)].

(* [comment removed for export] *)
Definition smA_slots3 (cx : cctx) (e : est) (usp : Z) (sv w24 w56 : word) : list cell :=
  let E := c_E cx in let A1 := c_A1 cx in let A := sm_alpha e in let nG := smA_ng e in
  [C8 (Z_to_bv 64 37450);                 (* [comment removed for export] *)
   C8 (Z_to_bv 64 (E + 128));             (* [comment removed for export] *)
   C8 w24;                                 (* [comment removed for export] *)
   C8 (Z_to_bv 64 A);                     (* [comment removed for export] *)
   C8 sv;                                  (* [comment removed for export] *)
   C8 (Z_to_bv 64 (E + 38998));           (* [comment removed for export] *)
   C8 w56;                                 (* [comment removed for export] *)
   C8 (Z_to_bv 64 (flag6 nG));            (* [comment removed for export] *)
   C8 (Z_to_bv 64 (nG - 1));              (* [comment removed for export] *)
   C8 (Z_to_bv 64 (4 * A));               (* [comment removed for export] *)
   C8 (Z_to_bv 64 (E + 45448 + 1032 * nG)); (* [comment removed for export] *)
   C8 (Z_to_bv 64 nG);                    (* [comment removed for export] *)
   C8 (Z_to_bv 64 0);                     (* [comment removed for export] *)
   C8 (Z_to_bv 64 (A1 + 2));              (* [comment removed for export] *)
   C8 (Z_to_bv 64 (E + 51648 + 16 * A));  (* [comment removed for export] *)
   C8 (Z_to_bv 64 (E + 37708));           (* [comment removed for export] *)
   C8 (Z_to_bv 64 (E + 51640));           (* [comment removed for export] *)
   C8 (Z_to_bv 64 A1);                    (* [comment removed for export] *)
   C8 (Z_to_bv 64 (E + 37708));           (* [comment removed for export] *)
   C8 (Z_to_bv 64 (usp + 616 + 4 * nG));  (* [comment removed for export] *)
   C8 (Z_to_bv 64 A);                     (* [comment removed for export] *)
   C8 (Z_to_bv 64 (E + 45448))].          (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)                    (* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS1.
(* [comment removed for export] *)
