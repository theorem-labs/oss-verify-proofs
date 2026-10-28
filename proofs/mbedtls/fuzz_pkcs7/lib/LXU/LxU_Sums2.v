(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_len U_asn1_get_tag U_asn1_get_bool U_asn1_get_int U_asn1_get_bitstring_null U_mpi_init.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxTac LxDex.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxP_Sums2 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMG"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_bool.U_ASN1_GET_BOOL"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRw"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_Sum_getlen.q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XZ"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_int.U_ASN1_GET_INT"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_bitstring_null.U_ASN1_GET_BITSTRING_NULL"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"].


(* [comment removed for export] *)
Definition SUM_getboolP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_Sums2 ()) "(0.$1.$2.#:.#11.#1.(3.(4.$5.$6.)(7.$5.$6.+:.^1.)(3.(4.$5.$6.)(7.$5.$6.+;.^2.)(3.(4.$5.$6.)(7.$5.$6.+<.^3.)(3.(4.$5.$6.)(7.$5.$6.+2.^8.)(8.(4.$5.$6.))))))(3.(4.$6.$9.)(7.$6.$9.^:.#0.)(8.(4.$6.$9.)))(:.$6.)(3.$;.(<.(=.^1.)(3.$>.(?.&8.(=.^4.))(8.$>.)))(3.$;.(<.(=.^3.)(3.$>.(?.&4.(=.^7.))(8.$>.)))(8.$;.)))(10.(4.$6.$6.)(7.$6.$6.^9.^8.))(3.(4.(4.$6.$6.)$6.)(7.(4.$6.$6.)$6.(7.$6.$6.^5.^6.)^1.)(8.(4.(4.$6.$6.)$6.)))(8.$;.)(3.$11.(12.(=.^5.)(=.^4.))(3.$11.(12.(=.^4.)(=.^2.))(3.$11.(12.(=.^2.)(13.(=.^5.)(=.^6.)))(3.$11.(14.(13.(=.^5.)(=.^6.))(15.(16.+2.+3?.)))(3.$11.(17.(=.^1.)(15.+8.)(=.^3.)(15.+4.))(3.$11.(17.(=.^1.)(15.+8.)(=.^5.)(=.^6.))(3.$11.(17.(=.^3.)(15.+4.)(=.^5.)(=.^6.))(3.$11.(18.(19.^1.)&3.)(3.$11.(18.(19.^3.)&2.)(3.$11.(14.(15.=)(=.^1.))(3.$11.(14.(15.=)(=.^3.))(3.$11.(14.(15.=)(=.^5.))(3.$11.(12.(=.^9.)(13.(=.^8.)(15.-20.)))(3.$11.(12.(=.^:.)(=.^9.))(3.$11.(18.(19.^8.)&4.)(3.$11.(1:.(13.(=.^1.)(15.+8.))(=.^9.)(=.^8.)(=.^1.))(3.$11.(1:.(13.(=.^3.)(15.+4.))(=.^9.)(=.^8.)(=.^3.))(3.$11.(1:.(13.(=.^5.)(=.^6.))(=.^9.)(=.^8.)(=.^5.))(3.$11.(12.(15.=)(=.^8.))(3.$11.(14.(=.^8.)(15.(16.+2.+40.)))(8.$11.)))))))))))))))))))))(3.(4.$1;.$1;.)(7.$1;.$1;.(=.^1.)(13.(=.^1.)(15.+8.)))(3.(4.$1;.$1;.)(7.$1;.$1;.(=.^3.)(13.(=.^3.)(15.+4.)))(3.(4.$1;.$1;.)(7.$1;.$1;.(13.(=.^8.)(15.-20.))(=.^8.))(8.(4.$1;.$1;.)))))(3.(4.$5.$6.)(7.$5.$6.+:.^;.)(3.(4.$5.$6.)(7.$5.$6.+5.^>.)(3.(4.$5.$6.)(7.$5.$6.+6.^?.)(3.(4.$5.$6.)(7.$5.$6.+7.^10.)(3.(4.$5.$6.)(7.$5.$6.+;.^11.)(3.(4.$5.$6.)(7.$5.$6.+<.^12.)(3.(4.$5.$6.)(7.$5.$6.+=.^13.)(3.(4.$5.$6.)(7.$5.$6.+>.^14.)(3.(4.$5.$6.)(7.$5.$6.+?.^15.)(3.(4.$5.$6.)(7.$5.$6.+10.^16.)(3.(4.$5.$6.)(7.$5.$6.+11.^17.)(3.(4.$5.$6.)(7.$5.$6.+1<.^18.)(3.(4.$5.$6.)(7.$5.$6.+1=.^19.)(3.(4.$5.$6.)(7.$5.$6.+1>.^1:.)(3.(4.$5.$6.)(7.$5.$6.+1?.^1;.)(8.(4.$5.$6.)))))))))))))))))(3.$;.(<.(=.^1.)(3.$>.(?.&8.(=.^<.))(8.$>.)))(3.$;.(<.(=.^3.)(3.$>.(?.&4.(=.^=.))(8.$>.)))(3.$;.(1<.(=.^9.)(=.^8.))(8.$;.))))(3.$11.(14.(15.-7?.)(=.^;.))(3.$11.(12.(=.^;.)(15.=))(3.$11.(12.(=.^4.)(=.^<.))(3.$11.(12.(=.^<.)(=.^2.))(3.$11.(1:.(13.(=.^;.)(15.+1.))(15.=)(13.(=.^4.)(15.+3.))(=.^<.))(3.$11.(12.(15.=)(=.^=.))(3.$11.(12.(=.^=.)(15.(1=.$1>.+1.)))(8.$11.)))))))))")
(* [comment removed for export] *).

Lemma sum_getboolP_valid {L : heap_layout} : forall AL, summary_validG usegs AL [alloc_ceiling] SUM_getboolP.
Proof.
  intros AL. unfold SUM_getboolP, q. lx_sum_unfold.
  intros PP END VALP P BUF LEN VV SP LO ACL bs CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI GB R10 R11 R12 R2 STK HPP HVALP [HBUF HLEN] PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  pose proof (@U_asn1_get_bool_spec L) as SP0. unfold asn1_get_bool_stmt, U_ASN1_GET_BOOL in SP0.
  subst ACL.
  assert (USP : bv_unsigned x2 = SP) by (rewrite R2; apply unsigned_lit; lia).
  rewrite <- USP in STK, PR13, PR15, PR16, PR17, PR18.
  eapply evt_cut.
  { eapply (SP0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP VALP P END BUF LO bs (Z_to_bv 64 VV));
      first [eassumption | cbn in *; lia | idtac]. }
  clear SP0. intros ms' POST. unfold asn1_get_bool_post in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & v & -> & MU & WM & MI' & -> & Hr & HPP' & HVALP' & STK' & Hp' & HL0).
  rewrite USP in MU, STK'.
  apply evt_done. pose proof (lx_urange v) as VR.
  lx_sum_post.
Qed.

(* [comment removed for export] *)
Definition SUM_getintP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_Sums2 ()) "(0.$1?.$2.#:.#11.#1.(3.(4.$5.$6.)(7.$5.$6.+:.^1.)(3.(4.$5.$6.)(7.$5.$6.+;.^2.)(3.(4.$5.$6.)(7.$5.$6.+<.^3.)(3.(4.$5.$6.)(7.$5.$6.+2.^8.)(8.(4.$5.$6.))))))(3.(4.$6.$9.)(7.$6.$9.^:.#0.)(8.(4.$6.$9.)))(:.$6.)(3.$;.(<.(=.^1.)(3.$>.(?.&8.(=.^4.))(8.$>.)))(3.$;.(<.(=.^3.)(3.$>.(?.&4.(=.^7.))(8.$>.)))(8.$;.)))(10.(4.$6.$6.)(7.$6.$6.^9.^8.))(3.(4.(4.$6.$6.)$6.)(7.(4.$6.$6.)$6.(7.$6.$6.^5.^6.)^1.)(8.(4.(4.$6.$6.)$6.)))(8.$;.)(3.$11.(12.(=.^5.)(=.^4.))(3.$11.(12.(=.^4.)(=.^2.))(3.$11.(12.(=.^2.)(13.(=.^5.)(=.^6.)))(3.$11.(14.(13.(=.^5.)(=.^6.))(15.(16.+2.+3?.)))(3.$11.(17.(=.^1.)(15.+8.)(=.^3.)(15.+4.))(3.$11.(17.(=.^1.)(15.+8.)(=.^5.)(=.^6.))(3.$11.(17.(=.^3.)(15.+4.)(=.^5.)(=.^6.))(3.$11.(18.(19.^1.)&3.)(3.$11.(18.(19.^3.)&2.)(3.$11.(14.(15.=)(=.^1.))(3.$11.(14.(15.=)(=.^3.))(3.$11.(14.(15.=)(=.^5.))(3.$11.(12.(=.^9.)(13.(=.^8.)(15.-20.)))(3.$11.(12.(=.^:.)(=.^9.))(3.$11.(18.(19.^8.)&4.)(3.$11.(1:.(13.(=.^1.)(15.+8.))(=.^9.)(=.^8.)(=.^1.))(3.$11.(1:.(13.(=.^3.)(15.+4.))(=.^9.)(=.^8.)(=.^3.))(3.$11.(1:.(13.(=.^5.)(=.^6.))(=.^9.)(=.^8.)(=.^5.))(3.$11.(12.(15.=)(=.^8.))(3.$11.(14.(=.^8.)(15.(16.+2.+40.)))(8.$11.)))))))))))))))))))))(3.(4.$1;.$1;.)(7.$1;.$1;.(=.^1.)(13.(=.^1.)(15.+8.)))(3.(4.$1;.$1;.)(7.$1;.$1;.(=.^3.)(13.(=.^3.)(15.+4.)))(3.(4.$1;.$1;.)(7.$1;.$1;.(13.(=.^8.)(15.-20.))(=.^8.))(8.(4.$1;.$1;.)))))(3.(4.$5.$6.)(7.$5.$6.+:.^;.)(3.(4.$5.$6.)(7.$5.$6.+5.^>.)(3.(4.$5.$6.)(7.$5.$6.+6.^?.)(3.(4.$5.$6.)(7.$5.$6.+7.^10.)(3.(4.$5.$6.)(7.$5.$6.+;.^11.)(3.(4.$5.$6.)(7.$5.$6.+<.^12.)(3.(4.$5.$6.)(7.$5.$6.+=.^13.)(3.(4.$5.$6.)(7.$5.$6.+>.^14.)(3.(4.$5.$6.)(7.$5.$6.+?.^15.)(3.(4.$5.$6.)(7.$5.$6.+10.^16.)(3.(4.$5.$6.)(7.$5.$6.+11.^17.)(3.(4.$5.$6.)(7.$5.$6.+1<.^18.)(3.(4.$5.$6.)(7.$5.$6.+1=.^19.)(3.(4.$5.$6.)(7.$5.$6.+1>.^1:.)(3.(4.$5.$6.)(7.$5.$6.+1?.^1;.)(8.(4.$5.$6.)))))))))))))))))(3.$;.(<.(=.^1.)(3.$>.(?.&8.(=.^<.))(8.$>.)))(3.$;.(<.(=.^3.)(3.$>.(?.&4.(=.^=.))(8.$>.)))(3.$;.(1<.(=.^9.)(=.^8.))(8.$;.))))(3.$11.(14.(15.-7?.)(=.^;.))(3.$11.(12.(=.^;.)(15.=))(3.$11.(12.(=.^4.)(=.^<.))(3.$11.(12.(=.^<.)(=.^2.))(3.$11.(1:.(13.(=.^;.)(15.+1.))(15.=)(13.(=.^4.)(15.+3.))(=.^<.))(3.$11.(12.(15.=)(=.^=.))(3.$11.(12.(=.^=.)(15.(1=.$1>.+1.)))(8.$11.)))))))))")
(* [comment removed for export] *).

Lemma sum_getintP_valid {L : heap_layout} : forall AL, summary_validG usegs AL [alloc_ceiling] SUM_getintP.
Proof.
  intros AL. unfold SUM_getintP, q. lx_sum_unfold.
  intros PP END VALP P BUF LEN VV SP LO ACL bs CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI GB R10 R11 R12 R2 STK HPP HVALP [HBUF HLEN] PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  pose proof (@U_asn1_get_int_spec L) as SP0. unfold asn1_get_int_stmt, U_ASN1_GET_INT in SP0.
  subst ACL.
  assert (USP : bv_unsigned x2 = SP) by (rewrite R2; apply unsigned_lit; lia).
  rewrite <- USP in STK, PR13, PR15, PR16, PR17, PR18.
  eapply evt_cut.
  { eapply (SP0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP VALP P END BUF LO bs (Z_to_bv 64 VV));
      first [eassumption | cbn in *; lia | idtac]. }
  clear SP0. intros ms' POST. unfold asn1_get_int_post in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & v & -> & MU & WM & MI' & -> & Hr & HPP' & HVALP' & STK' & Hp' & HL0).
  rewrite USP in MU, STK'.
  apply evt_done. pose proof (lx_urange v) as VR.
  lx_sum_post.
Qed.

(* [comment removed for export] *)
Definition SUM_getbsnullP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_Sums2 ()) "(0.$20.$2.#:.#11.#1.(3.(4.$5.$6.)(7.$5.$6.+:.^1.)(3.(4.$5.$6.)(7.$5.$6.+;.^2.)(3.(4.$5.$6.)(7.$5.$6.+<.^3.)(3.(4.$5.$6.)(7.$5.$6.+2.^8.)(8.(4.$5.$6.))))))(3.(4.$6.$9.)(7.$6.$9.^:.#0.)(8.(4.$6.$9.)))(:.$6.)(3.$;.(<.(=.^1.)(3.$>.(?.&8.(=.^4.))(8.$>.)))(3.$;.(<.(=.^3.)(3.$>.(?.&8.(=.^7.))(8.$>.)))(8.$;.)))(10.(4.$6.$6.)(7.$6.$6.^9.^8.))(3.(4.(4.$6.$6.)$6.)(7.(4.$6.$6.)$6.(7.$6.$6.^5.^6.)^1.)(8.(4.(4.$6.$6.)$6.)))(8.$;.)(3.$11.(12.(=.^5.)(=.^4.))(3.$11.(12.(=.^4.)(=.^2.))(3.$11.(12.(=.^2.)(13.(=.^5.)(=.^6.)))(3.$11.(14.(13.(=.^5.)(=.^6.))(15.(16.+2.+3?.)))(3.$11.(17.(=.^1.)(15.+8.)(=.^3.)(15.+8.))(3.$11.(17.(=.^1.)(15.+8.)(=.^5.)(=.^6.))(3.$11.(17.(=.^3.)(15.+8.)(=.^5.)(=.^6.))(3.$11.(18.(19.^1.)&3.)(3.$11.(18.(19.^3.)&3.)(3.$11.(14.(15.=)(=.^1.))(3.$11.(14.(15.=)(=.^3.))(3.$11.(14.(15.=)(=.^5.))(3.$11.(12.(=.^9.)(13.(=.^8.)(15.-20.)))(3.$11.(12.(=.^:.)(=.^9.))(3.$11.(18.(19.^8.)&4.)(3.$11.(1:.(13.(=.^1.)(15.+8.))(=.^9.)(=.^8.)(=.^1.))(3.$11.(1:.(13.(=.^3.)(15.+8.))(=.^9.)(=.^8.)(=.^3.))(3.$11.(1:.(13.(=.^5.)(=.^6.))(=.^9.)(=.^8.)(=.^5.))(3.$11.(12.(15.=)(=.^8.))(3.$11.(14.(=.^8.)(15.(16.+2.+40.)))(8.$11.)))))))))))))))))))))(3.(4.$1;.$1;.)(7.$1;.$1;.(=.^1.)(13.(=.^1.)(15.+8.)))(3.(4.$1;.$1;.)(7.$1;.$1;.(=.^3.)(13.(=.^3.)(15.+8.)))(3.(4.$1;.$1;.)(7.$1;.$1;.(13.(=.^8.)(15.-20.))(=.^8.))(8.(4.$1;.$1;.)))))(3.(4.$5.$6.)(7.$5.$6.+:.^;.)(3.(4.$5.$6.)(7.$5.$6.+5.^>.)(3.(4.$5.$6.)(7.$5.$6.+6.^?.)(3.(4.$5.$6.)(7.$5.$6.+7.^10.)(3.(4.$5.$6.)(7.$5.$6.+;.^11.)(3.(4.$5.$6.)(7.$5.$6.+<.^12.)(3.(4.$5.$6.)(7.$5.$6.+=.^13.)(3.(4.$5.$6.)(7.$5.$6.+>.^14.)(3.(4.$5.$6.)(7.$5.$6.+?.^15.)(3.(4.$5.$6.)(7.$5.$6.+10.^16.)(3.(4.$5.$6.)(7.$5.$6.+11.^17.)(3.(4.$5.$6.)(7.$5.$6.+1<.^18.)(3.(4.$5.$6.)(7.$5.$6.+1=.^19.)(3.(4.$5.$6.)(7.$5.$6.+1>.^1:.)(3.(4.$5.$6.)(7.$5.$6.+1?.^1;.)(8.(4.$5.$6.)))))))))))))))))(3.$;.(<.(=.^1.)(3.$>.(?.&8.(=.^<.))(8.$>.)))(3.$;.(<.(=.^3.)(3.$>.(?.&8.(=.^=.))(8.$>.)))(3.$;.(1<.(=.^9.)(=.^8.))(8.$;.))))(3.$11.(14.(15.-7?.)(=.^;.))(3.$11.(12.(=.^;.)(15.=))(3.$11.(12.(=.^4.)(=.^<.))(3.$11.(12.(=.^<.)(=.^2.))(3.$11.(1:.(13.(=.^;.)(15.+1.))(15.=)(13.(=.^4.)(15.+3.))(=.^<.))(3.$11.(1:.(13.(=.^;.)(15.+1.))(15.=)(=.^=.)(13.(=.^2.)(21.-1.(=.^<.))))(3.$11.(12.(15.=)(=.^=.))(3.$11.(12.(=.^=.)(15.(1=.$1>.+1.)))(8.$11.))))))))))")
(* [comment removed for export] *).

Lemma sum_getbsnullP_valid {L : heap_layout} : forall AL, summary_validG usegs AL [alloc_ceiling] SUM_getbsnullP.
Proof.
  intros AL. unfold SUM_getbsnullP, q. lx_sum_unfold.
  intros PP END LENP P BUF LEN LV SP LO ACL bs CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI GB R10 R11 R12 R2 STK HPP HLENP [HBUF HLEN] PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  pose proof (@U_asn1_get_bitstring_null_spec L) as SP0. unfold asn1_get_bitstring_null_stmt, U_ASN1_GET_BITSTRING_NULL in SP0.
  subst ACL.
  assert (USP : bv_unsigned x2 = SP) by (rewrite R2; apply unsigned_lit; lia).
  rewrite <- USP in STK, PR13, PR15, PR16, PR17, PR18.
  eapply evt_cut.
  { eapply (SP0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP LENP P END BUF LO bs (Z_to_bv 64 LV));
      first [eassumption | cbn in *; lia | idtac]. }
  clear SP0. intros ms' POST. unfold asn1_get_bitstring_null_post in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & Lw & -> & MU & WM & MI' & -> & Hr & HPP' & HLENP' & STK' & Hp' & HL0).
  rewrite USP in MU, STK'.
  apply evt_done. pose proof (lx_urange Lw) as LR.
  lx_sum_post.
Qed.

(* [comment removed for export] *)
Lemma sum_getlenP_validG {L : heap_layout} : forall AL, summary_validG usegs AL [alloc_ceiling] SUM_getlenP.
Proof.
  intros AL. unfold SUM_getlenP, q. lx_sum_unfold.
  intros PP END LENP P BUF LEN LV bs CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI R10 R11 R12 _ HPP HLENP [HBUF HLEN] PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  pose proof U_asn1_get_len_spec as SP. unfold asn1_get_len_stmt, U_ASN1_GET_LEN in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP LENP P END BUF bs (Z_to_bv 64 LV));
      first [eassumption | cbn in *; lia | idtac]. }
  clear SP. intros ms' POST. unfold asn1_get_len_post in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & Lw & -> & MU & WM & MI' & -> & Hr & HPP' & HLENP' & Hp' & HL0).
  apply evt_done. pose proof (lx_urange Lw) as LR.
  lx_sum_post.
Qed.
Lemma sum_gettagP_validG {L : heap_layout} : forall AL, summary_validG usegs AL [alloc_ceiling] SUM_gettagP.
Proof.
  intros AL. unfold SUM_gettagP, q. lx_sum_unfold.
  intros PP END LENP P BUF LEN LV TAG bs CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI R10 R11 R12 R13 _ HPP HLENP [HBUF HLEN] PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  pose proof U_asn1_get_tag_spec as SP. unfold asn1_get_tag_stmt, U_ASN1_GET_TAG in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP LENP P END BUF bs (Z_to_bv 64 LV) TAG);
      first [eassumption | cbn in *; lia | idtac]. }
  clear SP. intros ms' POST. unfold asn1_get_tag_post in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & Lw & -> & MU & WM & MI' & -> & Hr & HPP' & HLENP' & Hp' & HL0).
  apply evt_done. pose proof (lx_urange Lw) as LR.
  lx_sum_post.
Qed.

(* [comment removed for export] *)
Lemma sum_mpiinitP_validG {L : heap_layout} : forall AL, summary_validG usegs AL [alloc_ceiling] SUM_mpiinitP.
Proof.
  intros AL. unfold SUM_mpiinitP, q. lx_sum_unfold.
  intros X P0 S0 N0 PAD CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI R10 _ HX PR1 PR2.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  pose proof U_mpi_init_spec as SP. unfold mpi_init_stmt, U_MPI_INIT in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m X P0 N0 (Z_to_bv 64 S0) (Z_to_bv 64 PAD));
      first [eassumption | cbn in *; lia | idtac]. }
  clear SP. intros ms' POST. unfold mpi_init_post in POST.
  destruct POST as (a1' & m' & -> & MU & WM & MI' & HX').
  apply evt_done. unfold mpi_cells in HX'.
  lx_sum_post.
Qed.

(* [comment removed for export] *)
Definition SUMS2 : list summary := [SUM_getlenP; SUM_gettagP; SUM_getboolP; SUM_getintP; SUM_getbsnullP; SUM_mpiinitP].
Lemma sums2_ok {L : heap_layout} : forall AL, Forall (summary_okG usegs AL [alloc_ceiling]) SUMS2.
Proof.
  intros AL. unfold SUMS2. repeat constructor; apply apply_summary_soundG;
    auto using sum_getlenP_validG, sum_gettagP_validG, sum_getboolP_valid, sum_getintP_valid, sum_getbsnullP_valid, sum_mpiinitP_validG.
Qed.
(* [comment removed for export] *)
