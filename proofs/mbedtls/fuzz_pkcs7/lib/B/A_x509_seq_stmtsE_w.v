(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame HeapIface Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtStmts CrtParseStmts CrtExtStmts SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_alloc_lib A_crt_parse_stmts A_x509_seq_stmts A_x509_seq_stmtsE.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac drop_last H :=
  lazymatch type of H with
  | _ /\ (_ /\ _) => let a := fresh in let b := fresh in destruct H as [a b]; split; [exact a| drop_last b]
  | _ /\ _ => exact (proj1 H)
  end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_x509_seq_stmtsE_w () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.B.A_x509_seq_stmtsE.seq_parser_stmtE"; "RocqVerifyHarness.AgentSubmission.B.A_x509_seq_stmts.seq_parser_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_x509_seq_stmtsE.x509_akid_stmtE"; "RocqVerifyHarness.AgentSubmission.B.A_x509_seq_stmts.x509_akid_stmtA"].


Lemma seq_parser_stmtE_A : ltac2:(CDefT.buildp (gd_tbl_A_x509_seq_stmtsE_w ()) "Psegs,(0.$1.)PR,$2.PHIA,(3.R2.R1.)PPHI,P,$4.$4.PFFR,P,$4.P,$4.$4.PCNT,P,$4.$4.PSTK,$4.PLFM,$5.PXARG,P,(6.&40.)SpPENDR,P,$4.SpPENTRY,$4.P,(7.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(8.R<.R;.R:.R9.R8.R7.R6.R5.R4.R2.)")
(* [comment removed for export] *).
Proof.
  intros segs R HIA PHI FFR CNT STK LFM XARG ENDR ENTRY H. unfold seq_parser_stmtA. intros.
  eapply aevtS_mono; [eapply H; eassumption|].
  intros c PO. unfold seq_parser_postE in PO. unfold seq_parser_postA.
  ddestruct PO as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & HC).
  dexists x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26.
  drop_last HC.
Qed.

Lemma x509_akid_stmtE_A : ltac2:(CDefT.buildp (gd_tbl_A_x509_seq_stmtsE_w ()) "Psegs,(0.$1.)PR,$2.PHIA,(3.R2.R1.)PPHI,P,$4.$4.PFFR,P,$4.P,$4.$4.PCNT,P,$4.$4.PSTK,$4.PLFM,$5.PENTRY,$4.P,(9.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(:.R:.R9.R8.R7.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros segs R HIA PHI FFR CNT STK LFM ENTRY H. unfold x509_akid_stmtA. intros.
  eapply aevtS_mono; [eapply H; eassumption|].
  intros c PO. unfold x509_akid_postE in PO. unfold x509_akid_postA.
  ddestruct PO as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26
                  & x27 & x28 & x29 & x30 & x31 & x32 & x33 & x34 & HC).
  dexists x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34.
  drop_last HC.
Qed.
