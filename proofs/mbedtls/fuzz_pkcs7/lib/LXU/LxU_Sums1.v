(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_len U_asn1_get_tag U_mpi_init.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxTac LxDex.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Export LxU_Sum_getlen.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxP_Sums1 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LX.LxSum.SUM"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_tag.U_ASN1_GET_TAG"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRw"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_Sum_getlen.q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XZ"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_init.U_MPI_INIT"].


(* [comment removed for export] *)
Definition SUM_gettagP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_Sums1 ()) "(0.$1.$2.#8.#11.#1.(3.(4.$5.$6.)(7.$5.$6.+:.^1.)(3.(4.$5.$6.)(7.$5.$6.+;.^2.)(3.(4.$5.$6.)(7.$5.$6.+<.^3.)(3.(4.$5.$6.)(7.$5.$6.+=.^8.)(8.(4.$5.$6.))))))(9.$6.)(3.$:.(;.(<.^1.)(3.$=.(>.&8.(<.^4.))(8.$=.)))(3.$:.(;.(<.^3.)(3.$=.(>.&8.(<.^7.))(8.$=.)))(8.$:.)))(9.(4.$6.$6.))(3.(4.(4.$6.$6.)$6.)(7.(4.$6.$6.)$6.(7.$6.$6.^5.^6.)^1.)(8.(4.(4.$6.$6.)$6.)))(8.$:.)(3.$?.(10.(<.^5.)(<.^4.))(3.$?.(10.(<.^4.)(<.^2.))(3.$?.(10.(<.^2.)(11.(<.^5.)(<.^6.)))(3.$?.(12.(11.(<.^5.)(<.^6.))(13.(14.+2.+3?.)))(3.$?.(15.(<.^1.)(13.+8.)(<.^3.)(13.+8.))(3.$?.(15.(<.^1.)(13.+8.)(<.^5.)(<.^6.))(3.$?.(15.(<.^3.)(13.+8.)(<.^5.)(<.^6.))(3.$?.(16.(17.^1.)&3.)(3.$?.(16.(17.^3.)&3.)(3.$?.(12.(13.=)(<.^1.))(3.$?.(12.(13.=)(<.^3.))(3.$?.(12.(13.=)(<.^5.))(8.$?.)))))))))))))(3.(4.$18.$18.)(7.$18.$18.(<.^1.)(11.(<.^1.)(13.+8.)))(3.(4.$18.$18.)(7.$18.$18.(<.^3.)(11.(<.^3.)(13.+8.)))(8.(4.$18.$18.))))(3.(4.$5.$6.)(7.$5.$6.+:.^9.)(3.(4.$5.$6.)(7.$5.$6.+5.^<.)(3.(4.$5.$6.)(7.$5.$6.+6.^=.)(3.(4.$5.$6.)(7.$5.$6.+7.^>.)(3.(4.$5.$6.)(7.$5.$6.+;.^?.)(3.(4.$5.$6.)(7.$5.$6.+<.^10.)(3.(4.$5.$6.)(7.$5.$6.+=.^11.)(3.(4.$5.$6.)(7.$5.$6.+>.^12.)(3.(4.$5.$6.)(7.$5.$6.+?.^13.)(3.(4.$5.$6.)(7.$5.$6.+10.^14.)(3.(4.$5.$6.)(7.$5.$6.+11.^15.)(3.(4.$5.$6.)(7.$5.$6.+1<.^16.)(3.(4.$5.$6.)(7.$5.$6.+1=.^17.)(3.(4.$5.$6.)(7.$5.$6.+1>.^18.)(3.(4.$5.$6.)(7.$5.$6.+1?.^19.)(8.(4.$5.$6.)))))))))))))))))(3.$:.(;.(<.^1.)(3.$=.(>.&8.(<.^:.))(8.$=.)))(3.$:.(;.(<.^3.)(3.$=.(>.&8.(<.^;.))(8.$=.)))(8.$:.)))(3.$?.(12.(13.-7?.)(<.^9.))(3.$?.(10.(<.^9.)(13.=))(3.$?.(10.(<.^4.)(<.^:.))(3.$?.(10.(<.^:.)(<.^2.))(3.$?.(19.(11.(<.^9.)(13.+1.))(13.=)(11.(<.^4.)(13.+2.))(<.^:.))(3.$?.(19.(11.(<.^9.)(13.+1.))(13.=)(<.^;.)(11.(<.^2.)(1:.-1.(<.^:.))))(3.$?.(10.(13.=)(<.^;.))(3.$?.(10.(<.^;.)(13.(1;.$1<.+1.)))(8.$?.))))))))))")
(* [comment removed for export] *).

Lemma sum_gettagP_valid : forall AL, summary_valid usegs AL SUM_gettagP.
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
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & L & -> & MU & WM & MI' & -> & Hr & HPP' & HLENP' & Hp' & HL0).
  apply evt_done. pose proof (lx_urange L) as LR.
  lx_sum_post.
Qed.

(* [comment removed for export] *)
Definition SUM_mpiinitP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_Sums1 ()) "(0.$1=.$2.#5.#1.#0.(3.(4.$5.$6.)(7.$5.$6.+:.^1.)(8.(4.$5.$6.)))(9.$6.)(3.$:.(;.(<.^1.)(3.$=.(>.&8.(<.^2.))(3.$=.(>.&2.(<.^3.))(3.$=.(>.&2.(<.^4.))(3.$=.(>.&4.(<.^5.))(8.$=.))))))(8.$:.))(9.(4.$6.$6.))(8.(4.(4.$6.$6.)$6.))(8.$:.)(3.$?.(16.(17.^1.)&3.)(3.$?.(12.(13.=)(<.^1.))(8.$?.)))(3.(4.$18.$18.)(7.$18.$18.(<.^1.)(11.(<.^1.)(13.+10.)))(8.(4.$18.$18.)))(3.(4.$5.$6.)(7.$5.$6.+;.^6.)(8.(4.$5.$6.)))(3.$:.(;.(<.^1.)(3.$=.(>.&8.(13.=))(3.$=.(>.&2.(13.+1.))(3.$=.(>.&2.(13.=))(3.$=.(>.&4.(<.^5.))(8.$=.))))))(8.$:.))(8.$?.))")
(* [comment removed for export] *).

Lemma sum_mpiinitP_valid : forall AL, summary_valid usegs AL SUM_mpiinitP.
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
Definition SUMS1 : list summary := [SUM_getlenP; SUM_gettagP; SUM_mpiinitP].
Lemma sums1_ok : forall AL, Forall (summary_ok usegs AL) SUMS1.
Proof.
  intros AL. unfold SUMS1. repeat constructor; apply apply_summary_sound; auto using sum_getlenP_valid, sum_gettagP_valid, sum_mpiinitP_valid.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
