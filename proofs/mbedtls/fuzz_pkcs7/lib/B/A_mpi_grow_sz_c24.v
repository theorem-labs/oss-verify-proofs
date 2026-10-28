(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_mpi_zeroize_and_free A_mpi_grow A_mpi_stmtA_c24 A_mpi_grow_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_grow_sz_c24 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_grow_c24.mpi_grow_stmtA_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_grow_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_MEMSET_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_FREE_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_grow.A_WRAP_CALLOC_GR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemcpy"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_grow.A_ASAN_MEMCPY_GR"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_GROW"].


Lemma mpi_grow_stmtA_sz_of_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_grow_sz_c24 ()) "PR,$0.PHIA,(1.$2.R1.)PENTRY,$3.P,(4.$2.R3.R2.R1.)(5.$2.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros R HIA ENTRY H. unfold mpi_grow_stmtA_sz. intros until d.
  intros HH HK MX NS NB XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA BUD UW UWX BUDF C24 E0 E1.
  unfold mpi_grow_stmtA_c, mpi_xop_stmtA_c in H.
  eapply H; first [ eassumption | (clear - C24; unfold C24_GROW, C24_GROW_c in *; lia) ].
Qed.

(* [comment removed for export] *)

Lemma A_mpi_grow_sz_spec_closed_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_grow_sz_c24 ()) "PR,$0.PHIA,(1.$2.R1.)P,(6.(7.R2.))P,(8.$3.(9.R3.)$:.)P,(8.$3.(;.R4.)$<.)P,(8.$3.(=.R5.)$>.)P,(8.$3.(?.R6.)$10.)P,Pm,P,(11.&40.)(12.(11.&8.))P,(13.R8.R1.)(14.R2.)P,(15.=(16.R8.))P,(15.=(17.R9.))P,(15.=(18.R:.))P,Ph,(19.$2.R;.R:.)PLB,(1:.$1;.)PLF,(1:.$1;.)Pm,P,(11.&40.)(12.(11.&8.))P,(1<.$2.R?.R>.R4.R3.R2.R1.)(1=.$3.(1>.(1?.$3.$3.)$3.(20.$3.$3.)R4.))P,(21.(15.(22.(23.R<.))(24.(23.R<.)))(15.(25.(23.R<.))(26.(23.R<.))))(5.$2.R=.R<.$27.)")
(* [comment removed for export] *).
Proof. intros. apply mpi_grow_stmtA_sz_of_c. eapply A_mpi_grow_spec_closed_c; eauto. Qed.
