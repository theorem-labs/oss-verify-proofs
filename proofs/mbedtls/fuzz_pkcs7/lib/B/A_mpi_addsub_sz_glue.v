(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_stmtA_sz A_mpi_opnd A_mpi_journey A_mpi_add_abs_W A_mpi_sub_abs A_mpi_add_sub A_mpi_add_int A_mpi_sub_int A_mpi_add_abs_sz A_mpi_sub_abs_sz A_mpi_add_sub_sz A_mpi_add_int_sz A_mpi_sub_int_sz.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_mpi_add_sub_stmtSZ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AEvtS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_addsub_sz_glue () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_int_sz.mpi_add_int_stmtA_z"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_ADD_INT"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_add_int_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_int_sz.mpi_sub_int_stmtA_z"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_SUB_INT"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_sub_int_stmtA_sz"].


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wrap_Rsz_add : forall LB dX dA dB r d, add_sub_mpi_Rsz 1 LB dX dA dB r d -> add_mpi_Rsz LB dX dA dB r d.
Proof. intros LB dX dA dB r d [V K]. split; [apply wrap_R_add; exact V| exact K]. Qed.
Lemma wrap_Rsz_sub : forall LB dX dA dB r d, add_sub_mpi_Rsz (-1) LB dX dA dB r d -> sub_mpi_Rsz LB dX dA dB r d.
Proof. intros LB dX dA dB r d [V K]. split; [apply wrap_R_sub; exact V| exact K]. Qed.


(* [comment removed for export] *)
Theorem A_mpi_add_int_sz_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_addsub_sz_glue ()) "PR,$0.PHIA,(1.$2.R1.)P,(3.$2.R2.R1.$4.)(5.$2.R3.R2.$4.)")
(* [comment removed for export] *).
Proof. intros R HIA H. unfold mpi_add_int_stmtA_sz, mpi_intop_stmtA_sz. unfold mpi_add_int_stmtA_z in H.
  intros until d.
  intros HH HK LFB MX MA SXA NST OA CRA CRAL XW BB XLS ST LOS SLO TOP SPA TPV MI RAE OXA OAA IMA BUD UW UWX UWA BUDF C24 E0 E1 E2.
  pose proof (arl_need_ecp_rt R) as NE. pose proof (arl_need_ecp_smalloc R) as NES.
  unfold mpi_intop_stmtA_r in H.
  eapply H with (dX := dX) (dA := dA) (b := b) (lo := lo) (d := d);
    first [ eassumption | exact BUD | exact BUDF | exact C24 | exact E0 | exact E1 | exact E2
          | (intros _ O; exact (IMA O)) | (intros O _; exact (IMA O))
          | (clear - LFB; lia) | (clear - SLO NE; lia) | (clear - SLO NES; lia)
          | match goal with |- ?g => idtac "INTOPSZ-LEFT:" g end ].
Qed.
Theorem A_mpi_sub_int_sz_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_addsub_sz_glue ()) "PR,$0.PHIA,(1.$2.R1.)P,(6.$2.R2.R1.$7.)(8.$2.R3.R2.$7.)")
(* [comment removed for export] *).
Proof. intros R HIA H. unfold mpi_sub_int_stmtA_sz, mpi_intop_stmtA_sz. unfold mpi_sub_int_stmtA_z in H.
  intros until d.
  intros HH HK LFB MX MA SXA NST OA CRA CRAL XW BB XLS ST LOS SLO TOP SPA TPV MI RAE OXA OAA IMA BUD UW UWX UWA BUDF C24 E0 E1 E2.
  pose proof (arl_need_ecp_rt R) as NE. pose proof (arl_need_ecp_smalloc R) as NES.
  unfold mpi_intop_stmtA_r in H.
  eapply H with (dX := dX) (dA := dA) (b := b) (lo := lo) (d := d);
    first [ eassumption | exact BUD | exact BUDF | exact C24 | exact E0 | exact E1 | exact E2
          | (intros _ O; exact (IMA O)) | (intros O _; exact (IMA O))
          | (clear - LFB; lia) | (clear - SLO NE; lia) | (clear - SLO NES; lia)
          | match goal with |- ?g => idtac "INTOPSZ-LEFT:" g end ].
Qed.
