(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mpi_addsub.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_mul_stmt () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.binop_keep"].


Definition U_MPI_MUL_MPI : Z := 0x20b58.

Notation MPI_MUL_MPI_STACK := 304 (only parsing).

(* [comment removed for export] *)
Definition mul_mpi_R (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop :=
  (r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) /\ binop_keep LB dX dX'.

(* [comment removed for export] *)
Definition mul_mpi_val_R (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_stmt ()) "(0.(1.(0.(2.$3.O2.=)(2.$3.(4.O1.)(5.(4.O4.)(4.O3.))))(2.$3.O2.$6.))(7.O6.O5.O1.))")
(* [comment removed for export] *).

Definition mpi_mul_mpi_stmt segs L HI ENTRY MSF := mpi_binop_stmt segs L HI ENTRY MSF MPI_MUL_MPI_STACK mul_mpi_R.
Definition mpi_mul_mpi_val_stmt segs L HI ENTRY MSF := mpi_binop_stmt segs L HI ENTRY MSF MPI_MUL_MPI_STACK mul_mpi_val_R.

