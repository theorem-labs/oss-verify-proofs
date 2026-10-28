(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA AEvt HeapIface PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_asn1_get_alg_A U_oid.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxRun LxDenot LxSoundRun LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_SumsHeapO LxU_SumsCrt2.
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
Ltac2 gd_tbl_LxP_SumsPk () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMX"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_alg_A.U_ASN1_GET_ALG"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRw"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsCrt2.q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XZ"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr3z"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okO"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "SUM_agetalgP"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_hress"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okMR"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"].


(* [comment removed for export] *)
Definition SUM_agetalgP : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsPk ()) "(0.$1.$2.#14.#18.#1.(3.(4.$5.$6.)(7.$5.$6.+:.^1.)(3.(4.$5.$6.)(7.$5.$6.+;.^2.)(3.(4.$5.$6.)(7.$5.$6.+<.^3.)(3.(4.$5.$6.)(7.$5.$6.+=.^4.)(3.(4.$5.$6.)(7.$5.$6.+2.^8.)(8.(4.$5.$6.)))))))(3.(4.$6.$9.)(7.$6.$9.^:.#2.)(3.(4.$6.$9.)(7.$6.$9.^;.#7.)(3.(4.$6.$9.)(7.$6.$9.^<.#8.)(3.(4.$6.$9.)(7.$6.$9.^12.#2.)(8.(4.$6.$9.))))))(:.$6.)(3.$;.(<.(=.^1.)(3.$>.(?.&8.(=.^5.))(8.$>.)))(3.$;.(<.(=.^3.)(3.$>.(?.&4.(=.^=.))(3.$>.(?.&4.(=.^>.))(3.$>.(?.&8.(=.^?.))(3.$>.(?.&8.(=.^10.))(8.$>.))))))(3.$;.(<.(=.^4.)(3.$>.(?.&8.(=.^11.))(3.$>.(?.&8.(=.^13.))(3.$>.(?.&8.(=.^14.))(8.$>.)))))(8.$;.))))(10.(4.$6.$6.)(7.$6.$6.^9.^8.))(3.(4.(4.$6.$6.)$6.)(7.(4.$6.$6.)$6.(7.$6.$6.^6.^7.)^1.)(8.(4.(4.$6.$6.)$6.)))(8.$;.)(3.$11.(12.(=.^6.)(=.^5.))(3.$11.(12.(=.^5.)(=.^2.))(3.$11.(12.(=.^2.)(13.(=.^6.)(=.^7.)))(3.$11.(14.(13.(=.^6.)(=.^7.))(15.(16.+2.+3?.)))(3.$11.(17.(=.^1.)(15.+8.)(=.^3.)(15.+18.))(3.$11.(17.(=.^1.)(15.+8.)(=.^4.)(15.+18.))(3.$11.(17.(=.^3.)(15.+18.)(=.^4.)(15.+18.))(3.$11.(17.(=.^1.)(15.+8.)(=.^6.)(=.^7.))(3.$11.(17.(=.^3.)(15.+18.)(=.^6.)(=.^7.))(3.$11.(17.(=.^4.)(15.+18.)(=.^6.)(=.^7.))(3.$11.(18.(19.^1.)&3.)(3.$11.(18.(19.^3.)&3.)(3.$11.(18.(19.^4.)&3.)(3.$11.(14.(15.=)(=.^1.))(3.$11.(14.(15.=)(=.^3.))(3.$11.(14.(15.=)(=.^4.))(3.$11.(14.(15.=)(=.^6.))(3.$11.(12.(=.^9.)(13.(=.^8.)(15.-40.)))(3.$11.(12.(=.^:.)(=.^9.))(3.$11.(18.(19.^8.)&4.)(3.$11.(1:.(13.(=.^1.)(15.+8.))(=.^9.)(=.^8.)(=.^1.))(3.$11.(1:.(13.(=.^3.)(15.+18.))(=.^9.)(=.^8.)(=.^3.))(3.$11.(1:.(13.(=.^4.)(15.+18.))(=.^9.)(=.^8.)(=.^4.))(3.$11.(1:.(13.(=.^6.)(=.^7.))(=.^9.)(=.^8.)(=.^6.))(3.$11.(12.(=.^<.)(=.^:.))(3.$11.(1:.(13.(=.^1.)(15.+8.))(=.^;.)(=.^<.)(=.^1.))(3.$11.(1:.(13.(=.^3.)(15.+18.))(=.^;.)(=.^<.)(=.^3.))(3.$11.(1:.(13.(=.^4.)(15.+18.))(=.^;.)(=.^<.)(=.^4.))(3.$11.(12.(15.=)(=.^8.))(3.$11.(14.(=.^8.)(15.(16.+2.+40.)))(8.$11.)))))))))))))))))))))))))))))))(3.(4.$1;.$1;.)(7.$1;.$1;.(=.^1.)(13.(=.^1.)(15.+8.)))(3.(4.$1;.$1;.)(7.$1;.$1;.(=.^3.)(13.(=.^3.)(15.+18.)))(3.(4.$1;.$1;.)(7.$1;.$1;.(=.^4.)(13.(=.^4.)(15.+18.)))(3.(4.$1;.$1;.)(7.$1;.$1;.(13.(=.^8.)(15.-40.))(=.^8.))(8.(4.$1;.$1;.))))))(3.(4.$5.$6.)(7.$5.$6.+:.^15.)(3.(4.$5.$6.)(7.$5.$6.+5.^1?.)(3.(4.$5.$6.)(7.$5.$6.+6.^20.)(3.(4.$5.$6.)(7.$5.$6.+7.^21.)(3.(4.$5.$6.)(7.$5.$6.+;.^22.)(3.(4.$5.$6.)(7.$5.$6.+<.^23.)(3.(4.$5.$6.)(7.$5.$6.+=.^24.)(3.(4.$5.$6.)(7.$5.$6.+>.^25.)(3.(4.$5.$6.)(7.$5.$6.+?.^26.)(3.(4.$5.$6.)(7.$5.$6.+10.^27.)(3.(4.$5.$6.)(7.$5.$6.+11.^28.)(3.(4.$5.$6.)(7.$5.$6.+1<.^29.)(3.(4.$5.$6.)(7.$5.$6.+1=.^2:.)(3.(4.$5.$6.)(7.$5.$6.+1>.^2;.)(3.(4.$5.$6.)(7.$5.$6.+1?.^2<.)(8.(4.$5.$6.)))))))))))))))))(3.$;.(<.(=.^1.)(3.$>.(?.&8.(=.^16.))(8.$>.)))(3.$;.(<.(=.^3.)(3.$>.(?.&4.(=.^17.))(3.$>.(?.&4.(=.^18.))(3.$>.(?.&8.(=.^19.))(3.$>.(?.&8.(=.^1:.))(8.$>.))))))(3.$;.(<.(=.^4.)(3.$>.(?.&4.(=.^1;.))(3.$>.(?.&4.(=.^1<.))(3.$>.(?.&8.(=.^1=.))(3.$>.(?.&8.(=.^1>.))(8.$>.))))))(3.$;.(1<.(=.^9.)(=.^8.))(8.$;.)))))(3.$11.(14.(15.-7?.)(=.^15.))(3.$11.(12.(=.^15.)(15.=))(3.$11.(12.(=.^5.)(=.^16.))(3.$11.(12.(=.^16.)(=.^2.))(3.$11.(12.(15.=)(=.^17.))(3.$11.(12.(=.^17.)(15.(1=.$1>.+1.)))(3.$11.(12.(15.=)(=.^18.))(3.$11.(12.(=.^18.)(15.(1=.$1>.+1.)))(3.$11.(12.(15.=)(=.^19.))(3.$11.(12.(=.^19.)(15.(1=.$1>.+1.)))(3.$11.(12.(15.=)(=.^1:.))(3.$11.(12.(=.^1:.)(15.(1=.$1>.+1.)))(3.$11.(12.(15.=)(=.^1;.))(3.$11.(12.(=.^1;.)(15.(1=.$1>.+1.)))(3.$11.(12.(15.=)(=.^1<.))(3.$11.(12.(=.^1<.)(15.(1=.$1>.+1.)))(3.$11.(12.(15.=)(=.^1=.))(3.$11.(12.(=.^1=.)(15.(1=.$1>.+1.)))(3.$11.(12.(15.=)(=.^1>.))(3.$11.(12.(=.^1>.)(15.(1=.$1>.+1.)))(3.$11.(1:.(13.(=.^15.)(15.+1.))(15.=)(=.^6.)(=.^1:.))(3.$11.(1:.(13.(=.^15.)(15.+1.))(15.=)(13.(=.^1:.)(=.^19.))(=.^16.))(3.$11.(1?.(=.^1>.)(13.(=.^15.)(15.+1.))(15.=)(=.^6.)(=.^1>.))(3.$11.(1?.(=.^1>.)(13.(=.^15.)(15.+1.))(15.=)(13.(=.^1>.)(=.^1=.))(=.^16.))(3.$11.(1?.(=.^1>.)(13.(=.^15.)(15.+1.))(15.=)(=.^16.)(13.(=.^1>.)(=.^1=.)))(3.$11.(1?.(=.^1=.)(13.(=.^15.)(15.+1.))(15.=)(15.+1.)(=.^1>.))(3.$11.(1?.(=.^1;.)(13.(=.^15.)(15.+1.))(15.=)(15.+1.)(=.^1>.))(8.$11.))))))))))))))))))))))))))))(3.$9.#0.(8.$9.)))")
(* [comment removed for export] *).


Section Valid.
  Variable L : heap_layout.

  Section AAlg.
    Variable MSF : Z.
    Hypothesis GA : asn1_get_alg_stmt usegs L U_ASN1_GET_ALG MSF.
    Hypothesis CA : const_at L MSF 8.
    Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
    Variable OPS : list (mem -> Prop).
    Hypothesis O0 : nth 0 OPS (fun _ => True) = statics_ok usegs L.

    Local Ltac2 Set LiaOrc.tbl := fun () => "00o0@L10080462640.150L10080462640.157L12161533383.22 L12459831739.14 L13071194087.10 L13950453531.150L13950453531.157L14281088506.10 L15824345493.25 L15824346142.22 L20243917769.150L20243917769.157L20630679444.150L20630679444.157L21462821282.25 L21910927408.150L22372407886.150L22372407886.157L22804866563.10 L25273393476.2  L25273412207.157L26887523608.22 L28203547420.22 L28203548311.25 L28285773730.25 L30039753270.111L30084834608.150L30084834608.157L35174387812.16 L35176311407.157L35980939678.25 L36088593770.157L36088641089.2  L37782002751.16 L38709599012.10 L39107896096.25 L43192147922.22 L46362028405.22 L47846551420.10 L4819348681.150 L49755000201.10 L50202834992.150L50243717505.25 L50506983216.150L50506983216.157L5068751233.22  L52813803977.150L52813803977.157L53519195086.22 L58377790768.150L58377790768.157L60142021513.10 L61462588617.150L61490557645.150L61490557645.157L62633770346.157L64891089353.150L64891089353.157L65323765461.17 L67528838909.150L67528838909.157L8167680969.150 L8167680969.157 00000[01F01U01Y01k02R03903P03`04004d05X06G07607S08=08l09[09m0:50:]0:c0;80;M0;j0<T0=H0><0>N0?60?K0@30@;0@e0A<0AQ0A[0Am0BD0Bn0CB0Cl0D<0Dg0ER0Ea0FL0G70G;0Go0Hc0I70Ia0JH0Jo0KW0LB0Lm0M^0M_0M`0NT0OHS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5alen'2RcS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5alen'2RcS2bs1r2p'5plen'S2bsS3BUF1r4apw'2Hr2RNS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA1r2HrS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA1r2HrS1r2p'5plen'4ppw'2Hr2RNS3BUF2bs1r2ap2F1S3BUF2bs1r2ap2F1S2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5atag'2Ra5apad'2RbS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5atag'2Ra5apad'2RbS2PP3END3ALG3PAR1P2bs2x23AL13AL23AL33SPA2p'3Hp'S2PP3END3ALG3PAR1P2bs2x23AL13AL23AL33SPA2p'3Hp'S3BUF2bs3NZ41r5ptag'2pp2Re2FbS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA4ppw'2RhS2PP3END3ALG3PAR1P2bs2x23AL13AL23AL33SPA2p'3Hp'S2PP3END3ALG3PAR1P2bs2x23AL13AL23AL33SPA2p'3Hp'S3BUF1r4ppw'2Hr2RNS2pp3PPRS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA2pp2RhS2bs1rS2bs1r2p'5alen'2ap2F2S2bs1r2p'5alen'2ap2F2S3BUF2bs3NZ41r5plen'2pp2Rg2FbS2PP3ALG3PAR2SP2bs3AL13AL23AL33SPA3SP03SP1S2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5ptag'2Re5ppad'2RfS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5ptag'2Re5ppad'2RfS3BUF2bs3NZ42ap2F1S2PP3ALG3PAR2bs2x23AL13AL23AL33SPA2ap2RdS2bs1r2p'5plen'2pp2FeS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA2pp2RhS2pp3PPRS3END1P3BUF2bs2B42B32p'5alen'2ap3Hp'2Rc2F2S1r2p'5alen'4apw'2Hr2RNS2bs1r2p'5plen'2pp2FeS3BUF2bs1rS2bs1r5plen'2Rg2FlS1r2p'5plen'4ppw'2Hr2RNS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA4apw'2RdS1r5plen'4ppw'2Hr2RNS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA4apw'2RdS3BUF2bs1r2pp2FbS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5plen'2RgS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5plen'2RgS2bs1r2p'5plen'S2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5plen'2RgS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5plen'2RgS2bsS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5atag'2Ra5apad'2RbS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5atag'2Ra5apad'2RbS1r5ptag'4ppw'2Hr2RNS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA4ppw'2RhS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA1r2HrS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA1r2HrS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA2ap2RdS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5alen'2RcS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5alen'2RcS3END1P3BUF2bs2B42B33NZ42p'5plen'2pp3Hp'2Rg2Fb2FeFFS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5ptag'2Re5ppad'2RfS2PP3ALG3PAR2bs2x23AL13AL23AL33SPA5ptag'2Re5ppad'2Rf". (* [comment removed for export] *)
    Lemma sum_agetalgP_okO : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsPk ()) "PAL,$20.PCS,P,$5.SpPg0,$5.Pg1,$5.Pg3,$5.Pg4,$5.Pg5,$5.Pg6,$5.PGSX,(21.$5.)(22.$23.R9.(3.$5.R7.(3.$5.R6.(3.$5.(24.VL,)(3.$5.R5.(3.$5.R4.(3.$5.R3.(3.$5.R2.(3.$5.(25.VL,)(3.$5.(26.VL,)R1.)))))))))VOPS,R8.$27.)")
(* [comment removed for export] *).
    Proof.
      intros AL CS g0 g1 g3 g4 g5 g6 GSX. apply apply_summary_soundO. unfold SUM_agetalgP, q. lx_sum_unfold.
      intros PP END ALG PAR P BUF LEN SP LO ACL DLO DHI' ATAG APAD ALEN APW PTAG PPAD PLEN PPW bs F fc m.
      intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
      intros ALLCS _ MI GB0 GB1 GB2 GB3 R10 R11 R12 R13 R2 STK HPP HALG HPAR [HBUF HLEN].
      intros B1 B2 B3 B4 D1 D1b D1c D2 D3 D3b AL1 AL2 AL3 NZ1 NZ2 NZ3 NZ4 SLO ACLLO SPA DS1 DS2 DS3 DS4 DHX OD1 OD2 OD3 SP0 SP1 OQ0.
      change (nth 0 OPS (fun _ => True) m) in OQ0. rewrite O0 in OQ0.
      subst ACL DLO DHI' LEN PPAD.
      (* [comment removed for export] *)
      assert (HPARt : rw_cells usegs m PAR [C4 (Z_to_bv 64 PTAG); C4 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 PTAG : word) / 2^32)); C8 (Z_to_bv 64 PLEN); C8 (Z_to_bv 64 PPW)]).
      { eapply rw_cells_reshape; [exact HPAR| cbn -[le4 le8 Z.pow Z.div]; repeat split; reflexivity
                                | cbn -[le4 le8 Z.pow Z.div]; rewrite (le8_split4 (Z_to_bv 64 PTAG)), ?app_nil_r, <- ?app_assoc; reflexivity]. }
      clear HPAR.
      apply (evt_evtA_all usegs AL CS _ _ ALLCS).
      assert (USP : bv_unsigned x2 = SP) by (rewrite R2; apply unsigned_lit; lia).
      rewrite <- USP in STK, SLO, DS1, DS2, DS3, DS4, SPA.
      pose proof GA as SPc. unfold asn1_get_alg_stmt in SPc.
      eapply evt_cut.
      { eapply (SPc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m PP ALG PAR P END BUF LO bs
                  (Z_to_bv 64 ATAG) (Z_to_bv 64 APAD) (Z_to_bv 64 ALEN) (Z_to_bv 64 APW) (Z_to_bv 64 PTAG) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 PTAG : word) / 2^32)) (Z_to_bv 64 PLEN) (Z_to_bv 64 PPW));
          first [eassumption | cbn in *; lia | idtac]. }
      clear SPc. intros ms' POST. unfold asn1_get_alg_post in POST.
      destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' &
                        atag' & apad' & alen' & apw' & ptag' & ppad' & plen' & ppw' & -> & MU & WM & MI' & -> & Hr & HPP' & HALG' & HPAR' & ST' & SOK' & Hp' & HL0).
      rewrite USP in MU, ST'.
      apply evt_done.
      pose proof (lx_urange atag') as Ra. pose proof (lx_urange apad') as Rb. pose proof (lx_urange alen') as Rc. pose proof (lx_urange apw') as Rd.
      pose proof (lx_urange ptag') as Re. pose proof (lx_urange ppad') as Rf. pose proof (lx_urange plen') as Rg. pose proof (lx_urange ppw') as Rh.
      destruct (Z.eq_dec r 0) as [R0|RN].
      - destruct (HL0 R0) as (ap & pp & Eap & Epp & F1 & F2 & F3).
        rewrite Eap, Epp in *. rewrite (lx_uw64 ap) in * by (clear - F1 F2 Hp' B1 B2 B3 B4 NZ4 Rc; unfold two64; lia).
        assert (PPR : 0 <= pp <= two64 - 1).
        { clear - F3 Hp' B1 B2 B3 B4 NZ4 Rg. destruct F3 as [(-> & _ & _)|(Fb & Fe)]; unfold two64; lia. }
        rewrite (lx_uw64 pp) in * by (clear - PPR; lia).
        assert (SF : (r + 1 <= 0 \/ BUF <= ap) /\ (r + 1 <= 0 \/ ap + bv_unsigned alen' <= p')
                     /\ (pp = 0 \/ r + 1 <= 0 \/ BUF <= pp)
                     /\ (pp = 0 \/ r + 1 <= 0 \/ pp + bv_unsigned plen' <= p')
                     /\ (pp = 0 \/ r + 1 <= 0 \/ p' <= pp + bv_unsigned plen')
                     /\ (bv_unsigned plen' = 0 \/ r + 1 <= 0 \/ 1 <= pp)
                     /\ (bv_unsigned ptag' = 0 \/ r + 1 <= 0 \/ 1 <= pp)).
        { clear - R0 F1 F2 F3 Hp' B1 B2 B3 B4 NZ4 Rc Rg Re.
          destruct F3 as [(-> & Fl & ->)|(Fb & Fe)]; repeat split; rewrite ?unsigned_lit by lia; lia. }
        destruct SF as (SF1 & SF2 & SF3 & SF4 & SF5 & SF6 & SF7).
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

    Lemma sum_agetalgP_MR : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsPk ()) "PAL,$20.Plo,$5.PTOP,$5.PLAWS,(21.P,(21.(4.$5.$5.))P,P,(28.&40.)(29.(28.&8.))P,P,(28.&40.)(29.(28.&8.))Sp)PPROPS,(21.P,(21.$5.)Sp)PLB0,(21.(4.$5.$5.))PHP,P,(21.(4.$5.$5.))P,P,(28.&40.)(29.(28.&8.))P,$2:.SpPCW,P,(21.(4.$5.$5.))P,$5.SpPLH,(21.P,(21.(4.$5.$5.))P,$5.P,(21.(4.$5.$5.))P,P,(28.&40.)(29.(28.&8.))P,P,(28.&40.)(29.(28.&8.))Sp)PHRS,$2;.PTGT,P,$2:.P,$2<.SpPCS,P,$5.Sp(2=.$23.R<.(3.$5.R:.(3.$5.(2>.VL,)(3.$5.(24.VL,)(3.$5.(2?.VL,)(3.$5.(30.VL,)(3.$5.(31.VL,)(3.$5.R;.(3.$5.(25.VL,)(3.$5.(26.VL,)(8.$5.))))))))))VOPS,R9.R8.R7.R6.R5.R4.R3.R2.R1.$27.)")
(* [comment removed for export] *).
    Proof. intros. apply summary_okO_MR. apply sum_agetalgP_okO. Qed.
  End AAlg.
End Valid.
