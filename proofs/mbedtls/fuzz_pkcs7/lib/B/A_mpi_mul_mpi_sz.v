(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_mul_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_stmtA_sz A_mpi_copy A_mpi_mul_mpi_W A_mpi_mul_mpi_defs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AEvtS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_mul_mpi_sz () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_mpi_defs.mpi_mul_mpi_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_mul_mpi_stmtA_sz"].


Lemma mpi_mul_mpi_stmtA_sz_of : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_sz ()) "PR,$0.PHIA,(1.$2.R1.)PENTRY,$3.P,(4.$2.R3.R2.R1.)(5.$2.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros R HIA ENTRY H. unfold mpi_mul_mpi_stmtA_sz, mpi_binop_stmtA_sz. intros until slo.
  intros HH HK LFB MX MA MB SXA SXB SAB NST _ OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO _ TOP SPA TPV MI RAE OXA OAA OBA IA IB BUD UW UWX _ _ BUDF C24 E0 E1 E2.
  pose proof (arl_need_ecp_rt R) as NER. pose proof (arl_need_ecp_smalloc R) as NES.
  assert (EP : mul_mpi_PHI dX dA dB = mul_mpi_PHIn (md_n dA) (md_n dB)) by (unfold mul_mpi_PHI, mul_mpi_PHIn, copy_PHI, mul_mid_PHI; lia).
  assert (EF : mul_mpi_FR d = mul_mpi_FRn d) by (unfold mul_mpi_FR, mul_mpi_FRn, copy_FR, mul_mid_FR, calls_FR, fr_charge; lia).
  eapply aevtS_mono.
  - unfold A_mpi_mul_mpi_defs.mpi_mul_mpi_stmtA in H.
    eapply H with (dX := dX) (dA := dA) (dB := dB) (lo := lo) (d := d);
      first [ eassumption | reflexivity
            | (clear - LFB; lia) | (clear - SLO NER; lia) | (clear - SLO NES; lia)
            | (intros ES _; first [exact (IA ES) | exact (IB ES)])
            | (rewrite EP; exact BUD) | (rewrite EF; exact BUDF)
            | match goal with |- ?g => idtac "MULSZ-LEFT:" g end ].
  - cbv beta. intros c PO. unfold mpi_binop_postA in *.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & mo' & h' & LB' & dX' & r & PO).
    dexists y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m', mo', h', LB', dX', r.
    rewrite <- EP, <- EF. exact PO.
Qed.
