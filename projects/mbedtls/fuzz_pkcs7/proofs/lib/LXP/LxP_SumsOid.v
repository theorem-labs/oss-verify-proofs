(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA AEvt HeapIface PropExec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxRun LxDenot LxSoundRun LxTac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_SumsCrt2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxP_SumsOid () : Init.string Init.list := ["OSSVerify.KrLib.LX.LxSum.SUM"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.LX.LxMem.mfact"; "OSSVerify.KrLib.LX.LxDec.pfact"; "OSSVerify.KrLib.LX.LxDec.FEq"; "OSSVerify.KrLib.LXP.LxP_SumsCrt2.q"; "OSSVerify.KrLib.LX.LxDec.FLe"; "OSSVerify.KrLib.LX.LxExpr.EAdd"; "OSSVerify.KrLib.LX.LxDec.FLt"; "OSSVerify.KrLib.LX.LxExpr.ELit"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.LX.LxExpr.expr"].


(* [comment removed for export] *)
Definition SUM_bcmpCP (pc : Z) : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsOid ()) "(0.O1.$1.#6.#5.#2.(2.(3.$4.$5.)(6.$4.$5.+:.^1.)(2.(3.$4.$5.)(6.$4.$5.+;.^2.)(2.(3.$4.$5.)(6.$4.$5.+<.^3.)(7.(3.$4.$5.)))))(8.$5.)(7.$9.)(8.(3.$5.$5.))(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^1.^4.)^1.)(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^5.^6.)^2.)(7.(3.(3.$5.$5.)$5.))))(7.$9.)(2.$:.(;.(<.^4.)(<.^3.))(2.$:.(=.(<.^5.)(<.^2.))(2.$:.(=.(>.(<.^2.)(<.^3.))(>.(<.^5.)(<.^6.)))(2.$:.(?.(10.=)(<.^3.))(2.$:.(=.(10.=)(<.^1.))(2.$:.(?.(>.(<.^1.)(<.^3.))(10.(11.+2.+40.)))(2.$:.(?.(10.=)(<.^5.))(2.$:.(=.(>.(<.^5.)(<.^6.))(10.(11.+2.+40.)))(7.$:.)))))))))(7.(3.$12.$12.))(2.(3.$4.$5.)(6.$4.$5.+:.^7.)(2.(3.$4.$5.)(6.$4.$5.+;.^8.)(2.(3.$4.$5.)(6.$4.$5.+<.^9.)(2.(3.$4.$5.)(6.$4.$5.+=.^:.)(2.(3.$4.$5.)(6.$4.$5.+>.^;.)(7.(3.$4.$5.)))))))(7.$9.)(2.$:.(=.(10.-??.)(<.^7.))(2.$:.(=.(<.^7.)(10.+??.))(7.$:.))))")
(* [comment removed for export] *).

Lemma sum_bcmpCP_valid : forall pc AL, memcmp_stmt psegs pc -> summary_valid psegs AL (SUM_bcmpCP pc).
Proof.
  intros pc AL BC. unfold SUM_bcmpCP, q. lx_sum_unfold.
  intros P1 P2 NN L1 BUF BLEN xs bs CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI R10 R11 R12 _ [HB1 HL1] [HB2 HL2] E1 Q1 Q2 Q0 Q3 A1 A3 A4.
  apply (evt_evtA_all psegs AL CS _ _ ALLCS).
  destruct (bytes_at_sliceK m BUF bs P2 NN HB2 ltac:(lia) ltac:(lia) ltac:(lia)) as [PBY PLEN].
  pose proof BC as SP. unfold memcmp_stmt in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m xs _);
      subst x10 x11 x12; rewrite ?lx_uw64 by (unfold two64; lia); first [eassumption | lia]. }
  clear SP. intros ms' POST. unfold memcmp_post in POST.
  destruct POST as (a0' & a1' & a2' & a3' & a4' & r & -> & -> & Hr & _).
  apply evt_done. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl psegs m) as WM.
  lx_sum_post.
Qed.

Lemma sum_bcmpCP_ok : forall pc AL, memcmp_stmt psegs pc -> summary_ok psegs AL (SUM_bcmpCP pc).
Proof. intros. apply apply_summary_sound. apply sum_bcmpCP_valid. assumption. Qed.
