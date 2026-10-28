(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_stmtA_sz A_mpi_opnd A_mpi_journey A_mpi_add_abs_W A_mpi_sub_abs A_mpi_add_sub A_mpi_add_int A_mpi_sub_int A_mpi_add_abs_sz A_mpi_sub_abs_sz A_mpi_add_sub_sz A_mpi_add_int_sz A_mpi_sub_int_sz A_mpi_addsub_sz_glue A_mpi_stmtA_c24 A_mpi_add_sub_sz_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_mpi_add_sub_stmtSZ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AEvtS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_add_sub_o_c24 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_sz_c24.mpi_addsub_stmtA_o_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_sz_c24.C24_ADD_SUB_c"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.add_sub_mpi_R"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_sz_c24.add_sub_mpi_stmtA_oz_c"; "add_sub_mpi_stmtA_o_c"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ADD_SUB_MPI"].


(* [comment removed for export] *)
Definition add_sub_mpi_stmtA_o_c (flip : Z) segs R HIA ENTRY := ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_o_c24 ()) "(0.O4.O3.O2.O1.$1.La3,(2.&40.)(3.(2.&40.)R1.(4.&40.O5.))(5.O5.))")
(* [comment removed for export] *).

Lemma add_sub_mpi_stmtA_o_c_of_oz : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_o_c24 ()) "Pflip,$6.PR,$7.PHIA,(8.$9.R1.)PENTRY,$6.P,(:.R4.$9.R3.R2.R1.)(;.R5.$9.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros flip R HIA ENTRY H. unfold add_sub_mpi_stmtA_o_c, mpi_addsub_stmtA_o_c. intros.
  eapply aevtS_mono.
  - unfold add_sub_mpi_stmtA_oz_c, mpi_addsub_stmtA_o_c in H. eapply H with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (d := d); eassumption.
  - intros c PO. eapply binop_postA_mono; [apply mo_frame_refl| | exact PO]. intros r dd [V _]. exact V.
Qed.

Lemma A_add_sub_mpi_spec_o_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_add_sub_o_c24 ()) "Pflip,$6.P,(<.(3.$6.R1.+1.)(3.$6.R1.-1.))PR,$7.PHIA,(8.$9.R1.)P,(:.R4.$9.R2.R1.$=.)(;.R5.$9.R3.R2.$=.)")
(* [comment removed for export] *).
Proof. intros flip _ R HIA H. apply add_sub_mpi_stmtA_o_c_of_oz. exact H. Qed.
