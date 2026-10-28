(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_alg_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxTac LxDex.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1 LxU_Sums2 LxU_Sums3.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_LxP_Sums4 () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.summary"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "Stdlib.Lists.List.forallb"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.nat"; "Stdlib.Arith.PeanoNat.Nat.ltb"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.su_gbind"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_validG"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMX"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_alg_A.U_ASN1_GET_ALG"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRw"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_Sum_getlen.q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XZ"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr3z"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_Sum_getlen.SUM_getlenP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_Sums1.SUM_gettagP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_Sums2.SUM_getboolP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_Sums2.SUM_getintP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_Sums2.SUM_getbsnullP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_Sums1.SUM_mpiinitP"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_Sums3.SUM_gettimeP"; "SUM_getalgP"; "SUM_getalgP0"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lxp_sum_validG_ext : ltac2:(CDefT.buildp (gd_tbl_LxP_Sums4 ()) "Psegs,(0.$1.)PAL,$2.PGS,(0.$3.)PGSX,(0.$3.)Psu,$4.P,(5.$6.(7.(8.$9.$:.)Ljn,(8.$9.$:.)(;.(<.$9.$:.R1.)(=.$3.R4.))(>.R1.))$?.)P,(10.R6.R5.R4.R2.)(10.R7.R6.(11.$3.R5.R4.)R3.)")
(* [comment removed for export] *).
Proof. intros segs AL GS GSX su Hgb V. exact (summary_validG_ext segs AL GS GSX su Hgb V). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_getalgP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_Sums4 ()) "(12.$13.$14.#14.#18.#1.(15.(8.$3.$9.)(16.$3.$9.+:.^1.)(15.(8.$3.$9.)(16.$3.$9.+;.^2.)(15.(8.$3.$9.)(16.$3.$9.+<.^3.)(15.(8.$3.$9.)(16.$3.$9.+=.^4.)(15.(8.$3.$9.)(16.$3.$9.+2.^8.)(17.(8.$3.$9.)))))))(15.(8.$9.$:.)(16.$9.$:.^:.#0.)(15.(8.$9.$:.)(16.$9.$:.^;.#1.)(15.(8.$9.$:.)(16.$9.$:.^<.#2.)(17.(8.$9.$:.)))))(18.$9.)(15.$19.(1:.(1;.^1.)(15.$1<.(1=.&8.(1;.^5.))(17.$1<.)))(15.$19.(1:.(1;.^3.)(15.$1<.(1=.&4.(1;.^=.))(15.$1<.(1=.&4.(1;.^>.))(15.$1<.(1=.&8.(1;.^?.))(15.$1<.(1=.&8.(1;.^10.))(17.$1<.))))))(15.$19.(1:.(1;.^4.)(15.$1<.(1=.&4.(1;.^11.))(15.$1<.(1=.&4.(1;.^12.))(15.$1<.(1=.&8.(1;.^13.))(15.$1<.(1=.&8.(1;.^14.))(17.$1<.))))))(17.$19.))))(1>.(8.$9.$9.)(16.$9.$9.^9.^8.))(15.(8.(8.$9.$9.)$9.)(16.(8.$9.$9.)$9.(16.$9.$9.^6.^7.)^1.)(17.(8.(8.$9.$9.)$9.)))(17.$19.)(15.$1?.(20.(1;.^6.)(1;.^5.))(15.$1?.(20.(1;.^5.)(1;.^2.))(15.$1?.(20.(1;.^2.)(21.(1;.^6.)(1;.^7.)))(15.$1?.(22.(21.(1;.^6.)(1;.^7.))(23.(24.+2.+3?.)))(15.$1?.(25.(1;.^1.)(23.+8.)(1;.^3.)(23.+18.))(15.$1?.(25.(1;.^1.)(23.+8.)(1;.^4.)(23.+18.))(15.$1?.(25.(1;.^3.)(23.+18.)(1;.^4.)(23.+18.))(15.$1?.(25.(1;.^1.)(23.+8.)(1;.^6.)(1;.^7.))(15.$1?.(25.(1;.^3.)(23.+18.)(1;.^6.)(1;.^7.))(15.$1?.(25.(1;.^4.)(23.+18.)(1;.^6.)(1;.^7.))(15.$1?.(26.(27.^1.)&3.)(15.$1?.(26.(27.^3.)&3.)(15.$1?.(26.(27.^4.)&3.)(15.$1?.(22.(23.=)(1;.^1.))(15.$1?.(22.(23.=)(1;.^3.))(15.$1?.(22.(23.=)(1;.^4.))(15.$1?.(22.(23.=)(1;.^6.))(15.$1?.(20.(1;.^9.)(21.(1;.^8.)(23.-40.)))(15.$1?.(20.(1;.^:.)(1;.^9.))(15.$1?.(26.(27.^8.)&4.)(15.$1?.(28.(21.(1;.^1.)(23.+8.))(1;.^9.)(1;.^8.)(1;.^1.))(15.$1?.(28.(21.(1;.^3.)(23.+18.))(1;.^9.)(1;.^8.)(1;.^3.))(15.$1?.(28.(21.(1;.^4.)(23.+18.))(1;.^9.)(1;.^8.)(1;.^4.))(15.$1?.(28.(21.(1;.^6.)(1;.^7.))(1;.^9.)(1;.^8.)(1;.^6.))(15.$1?.(28.(21.(1;.^1.)(23.+8.))(1;.^;.)(1;.^<.)(1;.^1.))(15.$1?.(28.(21.(1;.^3.)(23.+18.))(1;.^;.)(1;.^<.)(1;.^3.))(15.$1?.(28.(21.(1;.^4.)(23.+18.))(1;.^;.)(1;.^<.)(1;.^4.))(15.$1?.(20.(23.=)(1;.^8.))(15.$1?.(22.(1;.^8.)(23.(24.+2.+40.)))(17.$1?.))))))))))))))))))))))))))))))(15.(8.$29.$29.)(16.$29.$29.(1;.^1.)(21.(1;.^1.)(23.+8.)))(15.(8.$29.$29.)(16.$29.$29.(1;.^3.)(21.(1;.^3.)(23.+18.)))(15.(8.$29.$29.)(16.$29.$29.(1;.^4.)(21.(1;.^4.)(23.+18.)))(15.(8.$29.$29.)(16.$29.$29.(21.(1;.^8.)(23.-40.))(1;.^8.))(17.(8.$29.$29.))))))(15.(8.$3.$9.)(16.$3.$9.+:.^15.)(15.(8.$3.$9.)(16.$3.$9.+5.^1?.)(15.(8.$3.$9.)(16.$3.$9.+6.^20.)(15.(8.$3.$9.)(16.$3.$9.+7.^21.)(15.(8.$3.$9.)(16.$3.$9.+;.^22.)(15.(8.$3.$9.)(16.$3.$9.+<.^23.)(15.(8.$3.$9.)(16.$3.$9.+=.^24.)(15.(8.$3.$9.)(16.$3.$9.+>.^25.)(15.(8.$3.$9.)(16.$3.$9.+?.^26.)(15.(8.$3.$9.)(16.$3.$9.+10.^27.)(15.(8.$3.$9.)(16.$3.$9.+11.^28.)(15.(8.$3.$9.)(16.$3.$9.+1<.^29.)(15.(8.$3.$9.)(16.$3.$9.+1=.^2:.)(15.(8.$3.$9.)(16.$3.$9.+1>.^2;.)(15.(8.$3.$9.)(16.$3.$9.+1?.^2<.)(17.(8.$3.$9.)))))))))))))))))(15.$19.(1:.(1;.^1.)(15.$1<.(1=.&8.(1;.^16.))(17.$1<.)))(15.$19.(1:.(1;.^3.)(15.$1<.(1=.&4.(1;.^17.))(15.$1<.(1=.&4.(1;.^18.))(15.$1<.(1=.&8.(1;.^19.))(15.$1<.(1=.&8.(1;.^1:.))(17.$1<.))))))(15.$19.(1:.(1;.^4.)(15.$1<.(1=.&4.(1;.^1;.))(15.$1<.(1=.&4.(1;.^1<.))(15.$1<.(1=.&8.(1;.^1=.))(15.$1<.(1=.&8.(1;.^1>.))(17.$1<.))))))(15.$19.(2:.(1;.^9.)(1;.^8.))(17.$19.)))))(15.$1?.(22.(23.-7?.)(1;.^15.))(15.$1?.(20.(1;.^15.)(23.=))(15.$1?.(20.(1;.^5.)(1;.^16.))(15.$1?.(20.(1;.^16.)(1;.^2.))(15.$1?.(20.(23.=)(1;.^17.))(15.$1?.(20.(1;.^17.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^18.))(15.$1?.(20.(1;.^18.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^19.))(15.$1?.(20.(1;.^19.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^1:.))(15.$1?.(20.(1;.^1:.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^1;.))(15.$1?.(20.(1;.^1;.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^1<.))(15.$1?.(20.(1;.^1<.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^1=.))(15.$1?.(20.(1;.^1=.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^1>.))(15.$1?.(20.(1;.^1>.)(23.(2;.$2<.+1.)))(15.$1?.(28.(21.(1;.^15.)(23.+1.))(23.=)(1;.^6.)(1;.^1:.))(15.$1?.(28.(21.(1;.^15.)(23.+1.))(23.=)(21.(1;.^1:.)(1;.^19.))(1;.^16.))(15.$1?.(2=.(1;.^1>.)(21.(1;.^15.)(23.+1.))(23.=)(1;.^6.)(1;.^1>.))(15.$1?.(2=.(1;.^1>.)(21.(1;.^15.)(23.+1.))(23.=)(21.(1;.^1>.)(1;.^1=.))(1;.^16.))(15.$1?.(2=.(1;.^1>.)(21.(1;.^15.)(23.+1.))(23.=)(1;.^16.)(21.(1;.^1>.)(1;.^1=.)))(15.$1?.(2=.(1;.^1=.)(21.(1;.^15.)(23.+1.))(23.=)(23.+1.)(1;.^1>.))(15.$1?.(2=.(1;.^1;.)(21.(1;.^15.)(23.+1.))(23.=)(23.+1.)(1;.^1>.))(17.$1?.))))))))))))))))))))))))))))(15.$:.#0.(17.$:.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition SUM_getalgP0 : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_Sums4 ()) "(12.$13.$14.#10.#18.#1.(15.(8.$3.$9.)(16.$3.$9.+:.^1.)(15.(8.$3.$9.)(16.$3.$9.+;.^2.)(15.(8.$3.$9.)(16.$3.$9.+<.^3.)(15.(8.$3.$9.)(16.$3.$9.+=.^4.)(15.(8.$3.$9.)(16.$3.$9.+2.^8.)(17.(8.$3.$9.)))))))(15.(8.$9.$:.)(16.$9.$:.^:.#0.)(15.(8.$9.$:.)(16.$9.$:.^;.#1.)(15.(8.$9.$:.)(16.$9.$:.^<.#2.)(17.(8.$9.$:.)))))(18.$9.)(15.$19.(1:.(1;.^1.)(15.$1<.(1=.&8.(1;.^5.))(17.$1<.)))(15.$19.(1:.(1;.^3.)(15.$1<.(1=.&4.(1;.^=.))(15.$1<.(1=.&4.(1;.^>.))(15.$1<.(1=.&8.(1;.^?.))(15.$1<.(1=.&8.(1;.^10.))(17.$1<.))))))(15.$19.(1:.(1;.^4.)(15.$1<.(1=.&8.(23.=))(15.$1<.(1=.&8.(23.=))(15.$1<.(1=.&8.(23.=))(17.$1<.)))))(17.$19.))))(1>.(8.$9.$9.)(16.$9.$9.^9.^8.))(15.(8.(8.$9.$9.)$9.)(16.(8.$9.$9.)$9.(16.$9.$9.^6.^7.)^1.)(17.(8.(8.$9.$9.)$9.)))(17.$19.)(15.$1?.(20.(1;.^6.)(1;.^5.))(15.$1?.(20.(1;.^5.)(1;.^2.))(15.$1?.(20.(1;.^2.)(21.(1;.^6.)(1;.^7.)))(15.$1?.(22.(21.(1;.^6.)(1;.^7.))(23.(24.+2.+3?.)))(15.$1?.(25.(1;.^1.)(23.+8.)(1;.^3.)(23.+18.))(15.$1?.(25.(1;.^1.)(23.+8.)(1;.^4.)(23.+18.))(15.$1?.(25.(1;.^3.)(23.+18.)(1;.^4.)(23.+18.))(15.$1?.(25.(1;.^1.)(23.+8.)(1;.^6.)(1;.^7.))(15.$1?.(25.(1;.^3.)(23.+18.)(1;.^6.)(1;.^7.))(15.$1?.(25.(1;.^4.)(23.+18.)(1;.^6.)(1;.^7.))(15.$1?.(26.(27.^1.)&3.)(15.$1?.(26.(27.^3.)&3.)(15.$1?.(26.(27.^4.)&3.)(15.$1?.(22.(23.=)(1;.^1.))(15.$1?.(22.(23.=)(1;.^3.))(15.$1?.(22.(23.=)(1;.^4.))(15.$1?.(22.(23.=)(1;.^6.))(15.$1?.(20.(1;.^9.)(21.(1;.^8.)(23.-40.)))(15.$1?.(20.(1;.^:.)(1;.^9.))(15.$1?.(26.(27.^8.)&4.)(15.$1?.(28.(21.(1;.^1.)(23.+8.))(1;.^9.)(1;.^8.)(1;.^1.))(15.$1?.(28.(21.(1;.^3.)(23.+18.))(1;.^9.)(1;.^8.)(1;.^3.))(15.$1?.(28.(21.(1;.^4.)(23.+18.))(1;.^9.)(1;.^8.)(1;.^4.))(15.$1?.(28.(21.(1;.^6.)(1;.^7.))(1;.^9.)(1;.^8.)(1;.^6.))(15.$1?.(28.(21.(1;.^1.)(23.+8.))(1;.^;.)(1;.^<.)(1;.^1.))(15.$1?.(28.(21.(1;.^3.)(23.+18.))(1;.^;.)(1;.^<.)(1;.^3.))(15.$1?.(28.(21.(1;.^4.)(23.+18.))(1;.^;.)(1;.^<.)(1;.^4.))(15.$1?.(20.(23.=)(1;.^8.))(15.$1?.(22.(1;.^8.)(23.(24.+2.+40.)))(17.$1?.))))))))))))))))))))))))))))))(15.(8.$29.$29.)(16.$29.$29.(1;.^1.)(21.(1;.^1.)(23.+8.)))(15.(8.$29.$29.)(16.$29.$29.(1;.^3.)(21.(1;.^3.)(23.+18.)))(15.(8.$29.$29.)(16.$29.$29.(1;.^4.)(21.(1;.^4.)(23.+18.)))(15.(8.$29.$29.)(16.$29.$29.(21.(1;.^8.)(23.-40.))(1;.^8.))(17.(8.$29.$29.))))))(15.(8.$3.$9.)(16.$3.$9.+:.^11.)(15.(8.$3.$9.)(16.$3.$9.+5.^1;.)(15.(8.$3.$9.)(16.$3.$9.+6.^1<.)(15.(8.$3.$9.)(16.$3.$9.+7.^1=.)(15.(8.$3.$9.)(16.$3.$9.+;.^1>.)(15.(8.$3.$9.)(16.$3.$9.+<.^1?.)(15.(8.$3.$9.)(16.$3.$9.+=.^20.)(15.(8.$3.$9.)(16.$3.$9.+>.^21.)(15.(8.$3.$9.)(16.$3.$9.+?.^22.)(15.(8.$3.$9.)(16.$3.$9.+10.^23.)(15.(8.$3.$9.)(16.$3.$9.+11.^24.)(15.(8.$3.$9.)(16.$3.$9.+1<.^25.)(15.(8.$3.$9.)(16.$3.$9.+1=.^26.)(15.(8.$3.$9.)(16.$3.$9.+1>.^27.)(15.(8.$3.$9.)(16.$3.$9.+1?.^28.)(17.(8.$3.$9.)))))))))))))))))(15.$19.(1:.(1;.^1.)(15.$1<.(1=.&8.(1;.^12.))(17.$1<.)))(15.$19.(1:.(1;.^3.)(15.$1<.(1=.&4.(1;.^13.))(15.$1<.(1=.&4.(1;.^14.))(15.$1<.(1=.&8.(1;.^15.))(15.$1<.(1=.&8.(1;.^16.))(17.$1<.))))))(15.$19.(1:.(1;.^4.)(15.$1<.(1=.&4.(1;.^17.))(15.$1<.(1=.&4.(1;.^18.))(15.$1<.(1=.&8.(1;.^19.))(15.$1<.(1=.&8.(1;.^1:.))(17.$1<.))))))(15.$19.(2:.(1;.^9.)(1;.^8.))(17.$19.)))))(15.$1?.(22.(23.-7?.)(1;.^11.))(15.$1?.(20.(1;.^11.)(23.=))(15.$1?.(20.(1;.^5.)(1;.^12.))(15.$1?.(20.(1;.^12.)(1;.^2.))(15.$1?.(20.(23.=)(1;.^13.))(15.$1?.(20.(1;.^13.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^14.))(15.$1?.(20.(1;.^14.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^15.))(15.$1?.(20.(1;.^15.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^16.))(15.$1?.(20.(1;.^16.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^17.))(15.$1?.(20.(1;.^17.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^18.))(15.$1?.(20.(1;.^18.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^19.))(15.$1?.(20.(1;.^19.)(23.(2;.$2<.+1.)))(15.$1?.(20.(23.=)(1;.^1:.))(15.$1?.(20.(1;.^1:.)(23.(2;.$2<.+1.)))(15.$1?.(28.(21.(1;.^11.)(23.+1.))(23.=)(1;.^6.)(1;.^16.))(15.$1?.(28.(21.(1;.^11.)(23.+1.))(23.=)(21.(1;.^16.)(1;.^15.))(1;.^12.))(15.$1?.(2=.(1;.^1:.)(21.(1;.^11.)(23.+1.))(23.=)(1;.^6.)(1;.^1:.))(15.$1?.(2=.(1;.^1:.)(21.(1;.^11.)(23.+1.))(23.=)(21.(1;.^1:.)(1;.^19.))(1;.^12.))(15.$1?.(2=.(1;.^1:.)(21.(1;.^11.)(23.+1.))(23.=)(1;.^12.)(21.(1;.^1:.)(1;.^19.)))(15.$1?.(2=.(1;.^19.)(21.(1;.^11.)(23.+1.))(23.=)(23.+1.)(1;.^1:.))(15.$1?.(2=.(1;.^17.)(21.(1;.^11.)(23.+1.))(23.=)(23.+1.)(1;.^1:.))(17.$1?.))))))))))))))))))))))))))))(15.$:.#0.(17.$:.)))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38559550480.3000007S1z1A1B". (* [comment removed for export] *)
Lemma lxp_uw64 : forall z, 0 <= z -> z <= two64 - 1 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z A B. apply unsigned_lit. unfold two64 in B. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section SOG.
  Context {L : heap_layout}.
  Variable MSF : Z.
  Hypothesis GA : asn1_get_alg_stmt usegs L U_ASN1_GET_ALG MSF.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Variable OPS : list (mem -> Prop).
  Hypothesis O0 : nth 0 OPS (fun _ => True) = statics_ok usegs L.
  Let GS4 : list Z := [alloc_ceiling; hl_data_lo L; hl_data_hi L].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0100@L10080462640.144L10080462640.151L12161533383.22 L12459831739.14 L13071194087.10 L13950453531.144L13950453531.151L14281088506.10 L15260915864.0  L15824345493.25 L15824346142.22 L16451060569.22 L16451061458.25 L20243917769.144L20243917769.151L20630679444.144L20630679444.151L21910927408.144L22372407886.144L22372407886.151L22804866563.10 L25273393476.2  L25273412207.151L28203547420.22 L28203548311.25 L28285773730.25 L30035642994.105L30084834608.144L30084834608.151L35174387812.16 L35176311407.151L35980939678.25 L36088593770.151L36088641089.2  L37782002751.16 L38709599012.10 L39107896096.25 L39280637297.0  L43192147922.22 L46362028405.22 L47846551420.10 L4819348681.144 L49755000201.10 L50202834992.144L50243717505.25 L50506983216.144L50506983216.151L5068751233.22  L52813803977.144L52813803977.151L58377790768.144L58377790768.151L60142021513.10 L61462588617.144L61490557645.144L61490557645.151L62633770346.151L64891089353.144L64891089353.151L65323765461.17 L67528838909.144L67528838909.151L8167680969.144 L8167680969.151 00000[01F01U01Y01k02R03903P03Q03a04104:04W05K06?06n07]08G09609e0:70:?0:g0;<0;Q0;n0<X0=L0>@0>R0?:0?O0@70@?0@i0A@0AU0AV0A`0B20BI0C30CG0D10DA0Dl0EW0Ef0FQ0G<0H00Hd0I80Ib0JI0K00KX0LC0Ln0M_0M`0Ma0NU0OIS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5alen'2RcS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5alen'2RcS2bs1r2p'5plen'S2bsS3BUF1r4apw'2Hr2RNS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA1r2HrS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA1r2HrS1r2p'5plen'4ppw'2Hr2RNSS3BUF2bs1r2ap2F1S3BUF2bs1r2ap2F1S2bs1r2ReS3BUF2bs3NZ41r5ptag'2pp2Re2FbS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5atag'2Ra5apad'2RbS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5atag'2Ra5apad'2RbS2PP3END3ALG3PAR1P2bs2x23AL13AL23AL33SPA2p'3Hp'S2PP3END3ALG3PAR1P2bs2x23AL13AL23AL33SPA2p'3Hp'S2PP3ALG3PAR2bs2x23AL13AL23AL33SPA4ppw'2RhS2PP3END3ALG3PAR1P2bs2x23AL13AL23AL33SPA2p'3Hp'S2PP3END3ALG3PAR1P2bs2x23AL13AL23AL33SPA2p'3Hp'S3BUF1r4ppw'2Hr2RNS2pp3PPRS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA2pp2RhS2bs1r2p'5alen'2ap2F2S2bs1r2p'5alen'2ap2F2S3BUF2bs3NZ41r5plen'2pp2Rg2FbS2PP3ALG3PAR2SP2bs3AL13AL23AL33SPA3SP03SP1S2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5ptag'2Re5ppad'2RfS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5ptag'2Re5ppad'2RfS3BUF2bs3NZ42ap2F1S2PP3ALG3PAR2bs2x23AL13AL23AL33SPA2ap2RdS2bs1r2p'5plen'2pp2FeS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA2pp2RhS2pp3PPRS3END1P3BUF2bs2B42B32p'5alen'2ap3Hp'2Rc2F2S1r2p'5alen'4apw'2Hr2RNS2bs1r2p'5plen'2pp2FeSS3BUF2bs1rS2bs1r5plen'2Rg2FlS1r2p'5plen'4ppw'2Hr2RNS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA4apw'2RdS1r5plen'4ppw'2Hr2RNS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA4apw'2RdS3BUF2bs1r2pp2FbS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5plen'2RgS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5plen'2RgS2bs1r2p'5plen'S2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5plen'2RgS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5plen'2RgS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5atag'2Ra5apad'2RbS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5atag'2Ra5apad'2RbS1r5ptag'4ppw'2Hr2RNS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA4ppw'2RhS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA1r2HrS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA1r2HrS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA2ap2RdS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5alen'2RcS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5alen'2RcS3END1P3BUF2bs2B42B33NZ42p'5plen'2pp3Hp'2Rg2Fb2FeFFS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5ptag'2Re5ppad'2RfS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5ptag'2Re5ppad'2Rf". (* [comment removed for export] *)
  Lemma sum_getalgP_okO : forall AL CS, summary_okO usegs AL GS4 OPS CS SUM_getalgP.
  Proof.
    intros AL CS. apply apply_summary_soundO. unfold SUM_getalgP, q. unfold GS4. lx_sum_unfold.
    intros PP END ALG PAR P BUF LEN SP LO ACL DLO DHI' ATAG APAD ALEN APW PTAG PPAD PLEN PPW bs F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros ALLCS _ MI GB0 GB1 GB2 R10 R11 R12 R13 R2 STK HPP HALG HPAR [HBUF HLEN].
    intros B1 B2 B3 B4 D1 D1b D1c D2 D3 D3b AL1 AL2 AL3 NZ1 NZ2 NZ3 NZ4 SLO ACLLO SPA DS1 DS2 DS3 DS4 OD1 OD2 OD3 SP0 SP1 OQ0.
    change (nth 0 OPS (fun _ => True) m) in OQ0. rewrite O0 in OQ0.
    subst ACL DLO DHI' LEN.
    apply (evt_evtA_all usegs AL CS _ _ ALLCS).
    assert (USP : bv_unsigned x2 = SP) by (rewrite R2; apply unsigned_lit; lia).
    rewrite <- USP in STK, SLO, DS1, DS2, DS3, DS4, SPA.
    pose proof GA as SPc. unfold asn1_get_alg_stmt in SPc.
    eapply evt_cut.
    { eapply (SPc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP ALG PAR P END BUF LO bs
                (Z_to_bv 64 ATAG) (Z_to_bv 64 APAD) (Z_to_bv 64 ALEN) (Z_to_bv 64 APW) (Z_to_bv 64 PTAG) (Z_to_bv 64 PPAD) (Z_to_bv 64 PLEN) (Z_to_bv 64 PPW));
        first [eassumption | cbn in *; lia | idtac]. }
    clear SPc. intros ms' POST. unfold asn1_get_alg_post in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' &
                      atag' & apad' & alen' & apw' & ptag' & ppad' & plen' & ppw' & -> & MU & WM & MI' & -> & Hr & HPP' & HALG' & HPAR' & ST' & SOK' & Hp' & HL0).
    rewrite USP in MU, ST'.
    apply evt_done.
    pose proof (lx_urange atag') as Ra. pose proof (lx_urange apad') as Rb. pose proof (lx_urange alen') as Rc. pose proof (lx_urange apw') as Rd.
    pose proof (lx_urange ptag') as Re. pose proof (lx_urange ppad') as Rf. pose proof (lx_urange plen') as Rg. pose proof (lx_urange ppw') as Rh.
    (* [comment removed for export] *)
    destruct (Z.eq_dec r 0) as [R0|RN].
    - destruct (HL0 R0) as (ap & pp & Eap & Epp & F1 & F2 & F3).
      rewrite Eap, Epp in *. rewrite (lxp_uw64 ap) in * by (clear - F1 F2 Hp' B1 B2 B3 B4 NZ4 Rc; unfold two64; lia).
      assert (PPR : 0 <= pp <= two64 - 1).
      { clear - F3 Hp' B1 B2 B3 B4 NZ4 Rg. destruct F3 as [(-> & _ & _)|(Fb & Fe)]; unfold two64; lia. }
      rewrite (lxp_uw64 pp) in * by (clear - PPR; lia).
      assert (SF : (r + 1 <= 0 \/ BUF <= ap) /\ (r + 1 <= 0 \/ ap + bv_unsigned alen' <= p')
                   /\ (pp = 0 \/ r + 1 <= 0 \/ BUF <= pp)
                   /\ (pp = 0 \/ r + 1 <= 0 \/ pp + bv_unsigned plen' <= p')
                   /\ (pp = 0 \/ r + 1 <= 0 \/ p' <= pp + bv_unsigned plen')
                   /\ (bv_unsigned plen' = 0 \/ r + 1 <= 0 \/ 1 <= pp)
                   /\ (bv_unsigned (Z_to_bv 64 0) = 0 -> bv_unsigned ptag' = 0 \/ r + 1 <= 0 \/ 1 <= pp)).
      { clear - R0 F1 F2 F3 Hp' B1 B2 B3 B4 NZ4 Rc Rg Re.
        destruct F3 as [(-> & Fl & ->)|(Fb & Fe)]; repeat split; lia. }
      rewrite (lxp_uw64 0) in SF by (unfold two64; clear; lia).
      destruct SF as (SF1 & SF2 & SF3 & SF4 & SF5 & SF6 & SF7). specialize (SF7 eq_refl).
      clear D1 D1b D1c D2 D3 D3b DS1 DS2 DS3 DS4 OD1 OD2 OD3 HL0 F3.
      lx_sum_post.
      all: try (lazymatch goal with |- ?f 0%nat OPS ?d ?mm => change (nth 0%nat OPS d mm); rewrite O0; exact SOK' end).
    - assert (SF : (r + 1 <= 0 \/ BUF <= bv_unsigned apw') /\ (r + 1 <= 0 \/ bv_unsigned apw' + bv_unsigned alen' <= p')
                 /\ (bv_unsigned ppw' = 0 \/ r + 1 <= 0 \/ BUF <= bv_unsigned ppw')
                 /\ (bv_unsigned ppw' = 0 \/ r + 1 <= 0 \/ bv_unsigned ppw' + bv_unsigned plen' <= p')
                 /\ (bv_unsigned ppw' = 0 \/ r + 1 <= 0 \/ p' <= bv_unsigned ppw' + bv_unsigned plen')
                 /\ (bv_unsigned plen' = 0 \/ r + 1 <= 0 \/ 1 <= bv_unsigned ppw')
                 /\ (bv_unsigned ptag' = 0 \/ r + 1 <= 0 \/ 1 <= bv_unsigned ppw')) by (clear - RN Hr; repeat split; lia).
      destruct SF as (SF1 & SF2 & SF3 & SF4 & SF5 & SF6 & SF7).
      clear D1 D1b D1c D2 D3 D3b DS1 DS2 DS3 DS4 OD1 OD2 OD3 HL0.
      lx_sum_post.
      all: try (lazymatch goal with |- ?f 0%nat OPS ?d ?mm => change (nth 0%nat OPS d mm); rewrite O0; exact SOK' end).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0100@L10080462640.140L10080462640.147L12161533383.22 L12459831739.14 L13071194087.10 L13950453531.140L13950453531.147L14281088506.10 L15260915864.0  L15824345493.25 L15824346142.22 L16451060569.22 L16451061458.25 L20243917769.140L20243917769.147L20630679444.140L20630679444.147L21910927408.140L22372407886.140L22372407886.147L22804866563.10 L25273393476.2  L25273412207.147L28203547420.22 L28203548311.25 L28285773730.25 L30035642994.101L30084834608.140L30084834608.147L35174387812.16 L35176311407.147L35980939678.25 L36088593770.147L36088641089.2  L37782002751.16 L38709599012.10 L39107896096.25 L39280637297.0  L43192147922.22 L46362028405.22 L47846551420.10 L4819348681.140 L49755000201.10 L50202834992.140L50243717505.25 L50506983216.140L50506983216.147L5068751233.22  L52813803977.140L52813803977.147L58377790768.140L58377790768.147L60142021513.10 L61462588617.140L61490557645.140L61490557645.147L62633770346.147L64891089353.140L64891089353.147L65323765461.17 L67528838909.140L67528838909.147L8167680969.140 L8167680969.147 00000[01F01U01Y01k02R03903P03Q03a04104:04W05K06?06n07]08G09609e0:70:?0:g0;<0;Q0;n0<X0=L0>@0>R0?:0?O0@70@?0@i0A@0AU0AV0A`0B20BI0C30CG0D10DA0Dl0EW0Ef0FQ0G<0H00Hd0I80Ib0JI0K00KX0LC0Ln0M_0M`0Ma0NU0OIS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5alen'2RcS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5alen'2RcS2bs1r2p'5plen'S2bsS3BUF1r4apw'2Hr2RNS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA1r2HrS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA1r2HrS1r2p'5plen'4ppw'2Hr2RNSS3BUF2bs1r2ap2F1S3BUF2bs1r2ap2F1S2bs1r2ReS3BUF2bs3NZ41r5ptag'2pp2Re2FbS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5atag'2Ra5apad'2RbS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5atag'2Ra5apad'2RbS2PP3END3ALG3PAR1P2bs2x23AL13AL23AL33SPA2p'3Hp'S2PP3END3ALG3PAR1P2bs2x23AL13AL23AL33SPA2p'3Hp'S2PP3ALG3PAR2bs2x23AL13AL23AL33SPA4ppw'2RhS2PP3END3ALG3PAR1P2bs2x23AL13AL23AL33SPA2p'3Hp'S2PP3END3ALG3PAR1P2bs2x23AL13AL23AL33SPA2p'3Hp'S3BUF1r4ppw'2Hr2RNS2pp3PPRS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA2pp2RhS2bs1r2p'5alen'2ap2F2S2bs1r2p'5alen'2ap2F2S3BUF2bs3NZ41r5plen'2pp2Rg2FbS2PP3ALG3PAR2SP2bs3AL13AL23AL33SPA3SP03SP1S2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5ptag'2Re5ppad'2RfS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5ptag'2Re5ppad'2RfS3BUF2bs3NZ42ap2F1S2PP3ALG3PAR2bs2x23AL13AL23AL33SPA2ap2RdS2bs1r2p'5plen'2pp2FeS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA2pp2RhS2pp3PPRS3END1P3BUF2bs2B42B32p'5alen'2ap3Hp'2Rc2F2S1r2p'5alen'4apw'2Hr2RNS2bs1r2p'5plen'2pp2FeSS3BUF2bs1rS2bs1r5plen'2Rg2FlS1r2p'5plen'4ppw'2Hr2RNS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA4apw'2RdS1r5plen'4ppw'2Hr2RNS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA4apw'2RdS3BUF2bs1r2pp2FbS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5plen'2RgS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5plen'2RgS2bs1r2p'5plen'S2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5plen'2RgS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5plen'2RgS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5atag'2Ra5apad'2RbS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5atag'2Ra5apad'2RbS1r5ptag'4ppw'2Hr2RNS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA4ppw'2RhS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA1r2HrS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA1r2HrS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA2ap2RdS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5alen'2RcS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5alen'2RcS3END1P3BUF2bs2B42B33NZ42p'5plen'2pp3Hp'2Rg2Fb2FeFFS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5ptag'2Re5ppad'2RfS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5ptag'2Re5ppad'2Rf". (* [comment removed for export] *)
  Lemma sum_getalgP0_okO : forall AL CS, summary_okO usegs AL GS4 OPS CS SUM_getalgP0.
  Proof.
    intros AL CS. apply apply_summary_soundO. unfold SUM_getalgP0, q. unfold GS4. lx_sum_unfold.
    intros PP END ALG PAR P BUF LEN SP LO ACL DLO DHI' ATAG APAD ALEN APW bs F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros ALLCS _ MI GB0 GB1 GB2 R10 R11 R12 R13 R2 STK HPP HALG HPAR [HBUF HLEN].
    intros B1 B2 B3 B4 D1 D1b D1c D2 D3 D3b AL1 AL2 AL3 NZ1 NZ2 NZ3 NZ4 SLO ACLLO SPA DS1 DS2 DS3 DS4 OD1 OD2 OD3 SP0 SP1 OQ0.
    change (nth 0 OPS (fun _ => True) m) in OQ0. rewrite O0 in OQ0.
    subst ACL DLO DHI' LEN.
    apply (evt_evtA_all usegs AL CS _ _ ALLCS).
    assert (USP : bv_unsigned x2 = SP) by (rewrite R2; apply unsigned_lit; lia).
    rewrite <- USP in STK, SLO, DS1, DS2, DS3, DS4, SPA.
    (* [comment removed for export] *)
    apply (rw_cells_reshape usegs _ _ _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in HPAR;
      [| cbn; repeat split; exact I | vm_compute; reflexivity].
    pose proof GA as SPc. unfold asn1_get_alg_stmt in SPc.
    eapply evt_cut.
    { eapply (SPc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP ALG PAR P END BUF LO bs
                (Z_to_bv 64 ATAG) (Z_to_bv 64 APAD) (Z_to_bv 64 ALEN) (Z_to_bv 64 APW) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0));
        first [eassumption | cbn in *; lia | idtac]. }
    clear SPc. intros ms' POST. unfold asn1_get_alg_post in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' &
                      atag' & apad' & alen' & apw' & ptag' & ppad' & plen' & ppw' & -> & MU & WM & MI' & -> & Hr & HPP' & HALG' & HPAR' & ST' & SOK' & Hp' & HL0).
    rewrite USP in MU, ST'.
    apply evt_done.
    pose proof (lx_urange atag') as Ra. pose proof (lx_urange apad') as Rb. pose proof (lx_urange alen') as Rc. pose proof (lx_urange apw') as Rd.
    pose proof (lx_urange ptag') as Re. pose proof (lx_urange ppad') as Rf. pose proof (lx_urange plen') as Rg. pose proof (lx_urange ppw') as Rh.
    (* [comment removed for export] *)
    destruct (Z.eq_dec r 0) as [R0|RN].
    - destruct (HL0 R0) as (ap & pp & Eap & Epp & F1 & F2 & F3).
      rewrite Eap, Epp in *. rewrite (lxp_uw64 ap) in * by (clear - F1 F2 Hp' B1 B2 B3 B4 NZ4 Rc; unfold two64; lia).
      assert (PPR : 0 <= pp <= two64 - 1).
      { clear - F3 Hp' B1 B2 B3 B4 NZ4 Rg. destruct F3 as [(-> & _ & _)|(Fb & Fe)]; unfold two64; lia. }
      rewrite (lxp_uw64 pp) in * by (clear - PPR; lia).
      assert (SF : (r + 1 <= 0 \/ BUF <= ap) /\ (r + 1 <= 0 \/ ap + bv_unsigned alen' <= p')
                   /\ (pp = 0 \/ r + 1 <= 0 \/ BUF <= pp)
                   /\ (pp = 0 \/ r + 1 <= 0 \/ pp + bv_unsigned plen' <= p')
                   /\ (pp = 0 \/ r + 1 <= 0 \/ p' <= pp + bv_unsigned plen')
                   /\ (bv_unsigned plen' = 0 \/ r + 1 <= 0 \/ 1 <= pp)
                   /\ (bv_unsigned (Z_to_bv 64 0) = 0 -> bv_unsigned ptag' = 0 \/ r + 1 <= 0 \/ 1 <= pp)).
      { clear - R0 F1 F2 F3 Hp' B1 B2 B3 B4 NZ4 Rc Rg Re.
        destruct F3 as [(-> & Fl & ->)|(Fb & Fe)]; repeat split; lia. }
      rewrite (lxp_uw64 0) in SF by (unfold two64; clear; lia).
      destruct SF as (SF1 & SF2 & SF3 & SF4 & SF5 & SF6 & SF7). specialize (SF7 eq_refl).
      clear D1 D1b D1c D2 D3 D3b DS1 DS2 DS3 DS4 OD1 OD2 OD3 HL0 F3.
      lx_sum_post.
      all: try (lazymatch goal with |- ?f 0%nat OPS ?d ?mm => change (nth 0%nat OPS d mm); rewrite O0; exact SOK' end).
    - assert (SF : (r + 1 <= 0 \/ BUF <= bv_unsigned apw') /\ (r + 1 <= 0 \/ bv_unsigned apw' + bv_unsigned alen' <= p')
                 /\ (bv_unsigned ppw' = 0 \/ r + 1 <= 0 \/ BUF <= bv_unsigned ppw')
                 /\ (bv_unsigned ppw' = 0 \/ r + 1 <= 0 \/ bv_unsigned ppw' + bv_unsigned plen' <= p')
                 /\ (bv_unsigned ppw' = 0 \/ r + 1 <= 0 \/ p' <= bv_unsigned ppw' + bv_unsigned plen')
                 /\ (bv_unsigned plen' = 0 \/ r + 1 <= 0 \/ 1 <= bv_unsigned ppw')
                 /\ (bv_unsigned ptag' = 0 \/ r + 1 <= 0 \/ 1 <= bv_unsigned ppw')) by (clear - RN Hr; repeat split; lia).
      destruct SF as (SF1 & SF2 & SF3 & SF4 & SF5 & SF6 & SF7).
      clear D1 D1b D1c D2 D3 D3b DS1 DS2 DS3 DS4 OD1 OD2 OD3 HL0.
      lx_sum_post.
      all: try (lazymatch goal with |- ?f 0%nat OPS ?d ?mm => change (nth 0%nat OPS d mm); rewrite O0; exact SOK' end).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac okO4 V := intros AL CS; apply apply_summary_soundO; apply summary_validG_O;
                       apply (lxp_sum_validG_ext usegs AL [alloc_ceiling] [hl_data_lo L; hl_data_hi L]); [reflexivity | apply V].
  Lemma sum_getlenP_okO4 : forall AL CS, summary_okO usegs AL GS4 OPS CS SUM_getlenP.     Proof. okO4 (@sum_getlenP_validG L). Qed.
  Lemma sum_gettagP_okO4 : forall AL CS, summary_okO usegs AL GS4 OPS CS SUM_gettagP.     Proof. okO4 (@sum_gettagP_validG L). Qed.
  Lemma sum_getboolP_okO4 : forall AL CS, summary_okO usegs AL GS4 OPS CS SUM_getboolP.   Proof. okO4 (@sum_getboolP_valid L). Qed.
  Lemma sum_getintP_okO4 : forall AL CS, summary_okO usegs AL GS4 OPS CS SUM_getintP.     Proof. okO4 (@sum_getintP_valid L). Qed.
  Lemma sum_getbsnullP_okO4 : forall AL CS, summary_okO usegs AL GS4 OPS CS SUM_getbsnullP. Proof. okO4 (@sum_getbsnullP_valid L). Qed.
  Lemma sum_mpiinitP_okO4 : forall AL CS, summary_okO usegs AL GS4 OPS CS SUM_mpiinitP.   Proof. okO4 (@sum_mpiinitP_validG L). Qed.
  Lemma sum_gettimeP_okO4 : forall AL CS, summary_okO usegs AL GS4 OPS CS SUM_gettimeP.   Proof. okO4 (@sum_gettimeP_valid L). Qed.
End SOG.

Definition SUMS4 : list summary := ltac2:(CDefT.buildp (gd_tbl_LxP_Sums4 ()) "(15.$4.$2>.(15.$4.$2?.(15.$4.$30.(15.$4.$31.(15.$4.$32.(15.$4.$33.(15.$4.$34.(15.$4.$35.(15.$4.$36.(17.$4.))))))))))")
(* [comment removed for export] *).
Lemma sums4_ok {L : heap_layout} (MSF : Z) :
  asn1_get_alg_stmt usegs L U_ASN1_GET_ALG MSF -> const_at L MSF 8 -> hl_data_hi L <= alloc_ceiling ->
  forall AL, Forall (summary_okO usegs AL [alloc_ceiling; hl_data_lo L; hl_data_hi L] [statics_ok usegs L] (fun _ : Z => True)) SUMS4.
Proof.
  intros GA CA DHI AL. unfold SUMS4.
  repeat constructor; auto using sum_getlenP_okO4, sum_gettagP_okO4, sum_getboolP_okO4, sum_getintP_okO4, sum_getbsnullP_okO4,
    sum_mpiinitP_okO4, sum_gettimeP_okO4.
  - apply (sum_getalgP_okO MSF GA CA DHI). reflexivity.
  - apply (sum_getalgP0_okO MSF GA CA DHI). reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
