(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut DecAux S0_dec_U13.
 (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut S0_dec_U13. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require RelLiaR.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.


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
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition eob_facts (cx : bctx) (v : dv) (nblock : Z) (sym unz : Z -> Z) : Prop :=
  (0 <= nblock <= 100000 * b_n cx)%Z /\
  hist_ok unz sym (Z.to_nat nblock) /\
  ag32s (r_unz (dv_r v)) unz 256 /\
  (forall i, (0 <= i < nblock)%Z -> (0 <= sym i < 256)%Z) /\
  match dv_k v with
  | BlkF ttw => b_small cx = 0%Z /\ forall i, (0 <= i < nblock)%Z -> nth_error ttw (Z.to_nat i) = Some (Z_to_bv 64 (sym i))
  | BlkS l16 l4 => b_small cx = 1%Z /\ forall i, (0 <= i < nblock)%Z ->
        nth_error l16 (Z.to_nat (2 * i)) = Some (Z_to_bv 8 (sym i)) /\ nth_error l16 (Z.to_nat (2 * i + 1)) = Some (Z_to_bv 8 0)
  end.

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

End ACeilS1.
