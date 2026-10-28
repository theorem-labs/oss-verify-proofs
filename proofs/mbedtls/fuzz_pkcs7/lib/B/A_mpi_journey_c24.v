(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_journey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_journey_c24 () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.JCA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XJA"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "Stdlib.ZArith.BinInt.Z.add"].


Lemma xa_cnt24 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey_c24 ()) "Psegs,(0.$1.)PR,$2.PHIA,(3.R2.R1.)Ph,(4.R3.R2.R1.)PLB,(0.$5.)PLF,(0.$5.)Pm,P,(6.&40.)(7.(6.&8.))PdX,$8.Psp,(6.&40.)Plo,$9.PFS,$9.PFRAME,(0.$:.)P,(;.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)PEX,(0.$5.)Pv,$9.Pf,$9.Phc,(4.R10.R?.R>.)PLBc,(0.$5.)Pmc,P,(6.&40.)(7.(6.&8.))PdXc,$8.P,(<.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R7.R6.R5.R4.R3.R2.R1.)(=.(>.R4.)(?.(>.R11.)+1.))")
(* [comment removed for export] *).
Proof.
  intros segs R HIA h LB LF m dX sp lo FS FRAME JC EX v f hc LBc mc dXc J.
  pose proof (jca_HND _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ (xa_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)) as ND.
  rewrite map_app in ND. apply NoDup_app_remove_l in ND. apply NoDup_map_inv in ND.
  pose proof (xa_out _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as (_ & _ & O3 & _).
  assert (INC : incl LBc (LB ++ mpd_blk dXc)). { intros b Hb. apply in_or_app. apply O3. exact Hb. }
  pose proof (cnt24_incl _ _ ND INC) as C. rewrite cnt24_app in C.
  assert (C1 : cnt24 (mpd_blk dXc) <= 1).
  { unfold mpd_blk. destruct (md_own dXc); try (rewrite cnt24_nil; lia).
    pose proof (cnt24_cons_le (md_p dXc, 4 * md_n dXc) []) as C2. rewrite cnt24_nil in C2. exact (proj2 C2). }
  lia.
Qed.
