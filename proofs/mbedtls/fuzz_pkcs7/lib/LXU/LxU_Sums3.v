(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_x509_get_time.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxTac LxDex.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1 LxU_Sums2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxP_Sums3 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMG"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_time.U_X509_GET_TIME"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRw"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_Sum_getlen.q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XZ"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"].


(* [comment removed for export] *)
Definition SUM_gettimeP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_Sums3 ()) "(0.$1.$2.#?.#16.#1.(3.(4.$5.$6.)(7.$5.$6.+:.^1.)(3.(4.$5.$6.)(7.$5.$6.+;.^2.)(3.(4.$5.$6.)(7.$5.$6.+<.^3.)(3.(4.$5.$6.)(7.$5.$6.+2.^=.)(8.(4.$5.$6.))))))(3.(4.$6.$9.)(7.$6.$9.^?.#0.)(8.(4.$6.$9.)))(:.$6.)(3.$;.(<.(=.^1.)(3.$>.(?.&8.(=.^4.))(8.$>.)))(3.$;.(<.(=.^3.)(3.$>.(?.&4.(=.^7.))(3.$>.(?.&4.(=.^8.))(3.$>.(?.&4.(=.^9.))(3.$>.(?.&4.(=.^:.))(3.$>.(?.&4.(=.^;.))(3.$>.(?.&4.(=.^<.))(8.$>.))))))))(8.$;.)))(10.(4.$6.$6.)(7.$6.$6.^>.^=.))(3.(4.(4.$6.$6.)$6.)(7.(4.$6.$6.)$6.(7.$6.$6.^5.^6.)^1.)(8.(4.(4.$6.$6.)$6.)))(8.$;.)(3.$11.(12.(=.^5.)(=.^4.))(3.$11.(12.(=.^4.)(=.^2.))(3.$11.(12.(=.^2.)(13.(=.^5.)(=.^6.)))(3.$11.(14.(13.(=.^5.)(=.^6.))(15.(16.+2.+3?.)))(3.$11.(17.(=.^1.)(15.+8.)(=.^3.)(15.+18.))(3.$11.(17.(=.^1.)(15.+8.)(=.^5.)(=.^6.))(3.$11.(17.(=.^3.)(15.+18.)(=.^5.)(=.^6.))(3.$11.(18.(19.^1.)&3.)(3.$11.(18.(19.^3.)&2.)(3.$11.(14.(15.=)(=.^1.))(3.$11.(14.(15.=)(=.^3.))(3.$11.(14.(15.=)(=.^5.))(3.$11.(12.(=.^>.)(13.(=.^=.)(15.-30.)))(3.$11.(12.(=.^?.)(=.^>.))(3.$11.(18.(19.^=.)&4.)(3.$11.(1:.(13.(=.^1.)(15.+8.))(=.^>.)(=.^=.)(=.^1.))(3.$11.(1:.(13.(=.^3.)(15.+18.))(=.^>.)(=.^=.)(=.^3.))(3.$11.(1:.(13.(=.^5.)(=.^6.))(=.^>.)(=.^=.)(=.^5.))(3.$11.(12.(15.=)(=.^=.))(3.$11.(14.(=.^=.)(15.(16.+2.+40.)))(8.$11.)))))))))))))))))))))(3.(4.$1;.$1;.)(7.$1;.$1;.(=.^1.)(13.(=.^1.)(15.+8.)))(3.(4.$1;.$1;.)(7.$1;.$1;.(=.^3.)(13.(=.^3.)(15.+18.)))(3.(4.$1;.$1;.)(7.$1;.$1;.(13.(=.^=.)(15.-30.))(=.^=.))(8.(4.$1;.$1;.)))))(3.(4.$5.$6.)(7.$5.$6.+:.^10.)(3.(4.$5.$6.)(7.$5.$6.+5.^18.)(3.(4.$5.$6.)(7.$5.$6.+6.^19.)(3.(4.$5.$6.)(7.$5.$6.+7.^1:.)(3.(4.$5.$6.)(7.$5.$6.+;.^1;.)(3.(4.$5.$6.)(7.$5.$6.+<.^1<.)(3.(4.$5.$6.)(7.$5.$6.+=.^1=.)(3.(4.$5.$6.)(7.$5.$6.+>.^1>.)(3.(4.$5.$6.)(7.$5.$6.+?.^1?.)(3.(4.$5.$6.)(7.$5.$6.+10.^20.)(3.(4.$5.$6.)(7.$5.$6.+11.^21.)(3.(4.$5.$6.)(7.$5.$6.+1<.^22.)(3.(4.$5.$6.)(7.$5.$6.+1=.^23.)(3.(4.$5.$6.)(7.$5.$6.+1>.^24.)(3.(4.$5.$6.)(7.$5.$6.+1?.^25.)(8.(4.$5.$6.)))))))))))))))))(3.$;.(<.(=.^1.)(3.$>.(?.&8.(=.^11.))(8.$>.)))(3.$;.(<.(=.^3.)(3.$>.(?.&4.(=.^12.))(3.$>.(?.&4.(=.^13.))(3.$>.(?.&4.(=.^14.))(3.$>.(?.&4.(=.^15.))(3.$>.(?.&4.(=.^16.))(3.$>.(?.&4.(=.^17.))(8.$>.))))))))(3.$;.(1<.(=.^>.)(=.^=.))(8.$;.))))(3.$11.(14.(15.-3000.)(=.^10.))(3.$11.(12.(=.^10.)(15.=))(3.$11.(12.(=.^4.)(=.^11.))(3.$11.(12.(=.^11.)(=.^2.))(3.$11.(12.(15.=)(=.^12.))(3.$11.(12.(=.^12.)(15.(1=.$1>.+1.)))(3.$11.(12.(15.=)(=.^13.))(3.$11.(12.(=.^13.)(15.(1=.$1>.+1.)))(3.$11.(12.(15.=)(=.^14.))(3.$11.(12.(=.^14.)(15.(1=.$1>.+1.)))(3.$11.(12.(15.=)(=.^15.))(3.$11.(12.(=.^15.)(15.(1=.$1>.+1.)))(3.$11.(12.(15.=)(=.^16.))(3.$11.(12.(=.^16.)(15.(1=.$1>.+1.)))(3.$11.(12.(15.=)(=.^17.))(3.$11.(12.(=.^17.)(15.(1=.$1>.+1.)))(8.$11.))))))))))))))))))")
(* [comment removed for export] *).

Lemma sum_gettimeP_valid {L : heap_layout} : forall AL, summary_validG usegs AL [alloc_ceiling] SUM_gettimeP.
Proof.
  intros AL. unfold SUM_gettimeP, q. lx_sum_unfold.
  intros PP END TM P BUF LEN Y0 MO0 D0 H0 MI0 S0 SP LO ACL bs CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI GB R10 R11 R12 R2 STK HPP HTM [HBUF HLEN] PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  pose proof (@U_x509_get_time_spec L) as SP0. unfold x509_get_time_stmt, U_X509_GET_TIME in SP0.
  subst ACL.
  assert (USP : bv_unsigned x2 = SP) by (rewrite R2; apply unsigned_lit; lia).
  rewrite <- USP in STK, PR13, PR15, PR16, PR17, PR18.
  eapply evt_cut.
  { eapply (SP0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP TM P END BUF LO bs
              (Z_to_bv 64 Y0) (Z_to_bv 64 MO0) (Z_to_bv 64 D0) (Z_to_bv 64 H0) (Z_to_bv 64 MI0) (Z_to_bv 64 S0));
      unfold time_cells; first [eassumption | cbn in *; lia | idtac]. }
  clear SP0. intros ms' POST. unfold x509_get_time_post, time_cells in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & y & mo & d & h & mi & s & -> & MU & WM & MI' & -> & Hr & HPP' & HTM' & STK' & Hp').
  rewrite USP in MU, STK'.
  apply evt_done.
  pose proof (lx_urange y) as R1. pose proof (lx_urange mo) as R2'. pose proof (lx_urange d) as R3. pose proof (lx_urange h) as R4.
  pose proof (lx_urange mi) as R5. pose proof (lx_urange s) as R6.
  lx_sum_post.
Qed.

Definition SUMS3 : list summary := [SUM_getlenP; SUM_gettagP; SUM_getboolP; SUM_getintP; SUM_getbsnullP; SUM_mpiinitP; SUM_gettimeP].
Lemma sums3_ok {L : heap_layout} : forall AL, Forall (summary_okG usegs AL [alloc_ceiling]) SUMS3.
Proof.
  intros AL. unfold SUMS3. repeat constructor; apply apply_summary_soundG;
    auto using sum_getlenP_validG, sum_gettagP_validG, sum_getboolP_valid, sum_getintP_valid, sum_getbsnullP_valid, sum_mpiinitP_validG, sum_gettimeP_valid.
Qed.
(* [comment removed for export] *)
