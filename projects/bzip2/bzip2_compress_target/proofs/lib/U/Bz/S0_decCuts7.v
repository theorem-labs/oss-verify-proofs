(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecAuxM S0_dec_U13.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac.DecAuxB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAuxM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Export S0_decCuts.
From Stdlib Require Lia. 
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
Module S0_decCutsB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac.DecAuxB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13.
Export OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.
End S0_decCutsB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section ACeilS1. Context {ACEIL__ : ACeil}.


End ACeilS1.
