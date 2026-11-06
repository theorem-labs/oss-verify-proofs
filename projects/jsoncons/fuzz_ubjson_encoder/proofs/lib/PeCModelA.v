(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5KnA L5LazyA L5DefsA L5CoreA
     PmLayout PmLayoutA PmModel PmStatics PmStaticsA PmSpecs PmSpecsA PeCLayout PeCSink PeCStatics PeCModel PeCSinkA PeCStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef UbjRefFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeCModelA () := "C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeCModelA4PECA9crun_preAC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCModel3PEC5clinkC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef4s_ecC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeCModelA4PECA9ec_stateAC13~~~I47Corelib4Init5Logic2eq00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA3o_pC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA4accAC13~~~I47Corelib4Init5Logic3and00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM5p_srcC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCModel3PEC:content_okC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM4p_tbC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM4p_tgC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM5tb_okC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;PeCStaticsA5PESTA7err_okAC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PmStaticsA5PMSTA8base_okAC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK6o_sinkC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCSinkA5PESKA8sink_atAC13~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA3o_vC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56u64_atC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeCModelA4PECA7enc_atAC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA4o_isC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM6iss_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM9parser_atC13~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCSinkA5PESKA<sink_policyA00C13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec6UbjRef2st00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM3pst00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM4vstr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmModel2PM4strm00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeCModel3PEC3enc00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK4sink00C13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeCModelA4PECA9RDR_BYTESC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA4annAC13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECA.
Section WithImage.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable E : pe_addrs.
Variable L : asan_layout.
Variable ar : asan_run.

Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation HV := (PMSPA.HV L ar).
Abbreviation scA := (PMSPA.scA L).
Abbreviation parser_at := (PM.parser_at segs A accA annA).
Abbreviation iss_at := (PM.iss_at segs A accA).
Abbreviation sink_atA := (PESKA.sink_atA segs L ar).

(* [comment removed for export] *)
Definition frame_ok5 (FF : list fframe) (fb : Z) : Prop := (exists rs, In (fb, 5, rs) FF) /\ fb mod 2048 = 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enc_atA (M : word -> option byte) (ov fb : Z) (en : PEC.enc) : Prop :=
  L5.u64_at segs M ov (pe_vt E) /\ L5.u64_at segs M (ov + 8) (PESK.o_sink E fb) /\ L5.u32_at segs M (ov + 16) UbjRef.MAX_DEPTH
  /\ L5.u64_at segs M (ov + 24) (PEC.en_b en)
  /\ L5.u64_at segs M (ov + 32) (PEC.en_b en + PEC.ESZ * Z.of_nat (length (PEC.en_stk en)))
  /\ L5.u64_at segs M (ov + 40) (PEC.en_b en + PEC.ESZ * PEC.ecap (PEC.en_k en))
  /\ L5.u32_at segs M (ov + 48) (PEC.en_depth en)
  /\ L5.defined M ov 56 /\ accA M ov 56
  /\ 0 <= PEC.en_k en <= 12 /\ Z.of_nat (length (PEC.en_stk en)) <= PEC.ecap (PEC.en_k en) /\ 0 <= PEC.en_depth en <= UbjRef.MAX_DEPTH + 1
  /\ (PEC.en_k en = 0 -> PEC.en_b en = 0)
  /\ (0 < PEC.en_k en ->
        PEC.en_b en mod 8 = 0 /\ L5.defined M (PEC.en_b en) (PEC.ESZ * PEC.ecap (PEC.en_k en)) /\ ablock_range L ar (PEC.en_b en) (PEC.ESZ * PEC.ecap (PEC.en_k en))
        /\ accA M (PEC.en_b en) (PEC.ESZ * Z.of_nat (length (PEC.en_stk en)))
        /\ annA M (PEC.en_b en) (PEC.ESZ * Z.of_nat (length (PEC.en_stk en))) (PEC.ESZ * PEC.ecap (PEC.en_k en)))
  /\ (forall i, (i < length (PEC.en_stk en))%nat -> PEC.eitem_at segs M (PEC.en_b en + PEC.ESZ * Z.of_nat i) (nth i (PEC.en_stk en) (EI 0 0 0))).

(* [comment removed for export] *)
Definition ec_stateA (M : word -> option byte) (fb : Z) (e : bool) (cat : Z) : Prop :=
  if e then exists v, 1 <= v <= 64 /\ PMSPA.ec_at segs M (PMSPA.o_ec A fb) v (pa_errcat_obj A)
  else PMSPA.ec_at segs M (PMSPA.o_ec A fb) 0 cat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RDR_BYTES : Z := 392.      (* [comment removed for export] *)

Definition crun_preA (P : PESKA.sink_policyA) (M : word -> option byte) (fb : Z) (p : list Z) (X : UbjRef.st)
           (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool) (cat : Z) : Prop :=
  parser_at M (PMSPA.o_p A fb) (PMSPA.o_is A fb) s /\ iss_at M (PMSPA.o_is A fb) str sm
  /\ enc_atA M (PMSPA.o_v A fb) fb en /\ L5.u64_at segs M (PMSPA.o_p A fb + 384) (PMSPA.o_v A fb)
  /\ sink_atA P M (PESK.o_sink E fb) k
  /\ PMSTA.base_okA segs A M /\ PESTA.err_okA segs A AA E M e /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s)
  /\ PEC.content_ok segs A M fb p (PM.p_src s) str sm
  /\ PEC.clink p X s sm en k
  /\ ec_stateA M fb (s_ec X) cat
  /\ (s_ec X = true -> e = true)
  /\ accA M (PMSPA.o_p A fb) RDR_BYTES.

(* [comment removed for export] *)
Definition pot_allA (P : PESKA.sink_policyA) (s : PM.pst) (en : PEC.enc) (k : PESK.sink) : credit :=
  PEC.credit_add (scA (PM.pot_parser HV s)) (PEC.credit_add (scA (PEC.pot_estack HV (PEC.en_k en))) (PESKA.spa_pot P (PESK.sk_c k))).
Definition pot_encA (P : PESKA.sink_policyA) (en : PEC.enc) (k : PESK.sink) : credit :=
  PEC.credit_add (scA (PEC.pot_estack HV (PEC.en_k en))) (PESKA.spa_pot P (PESK.sk_c k)).

(* [comment removed for export] *)
Lemma crun_preA_clink P M fb p X s str sm en k e cat : crun_preA P M fb p X s str sm en k e cat -> PEC.clink p X s sm en k.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCModelA ()) ["WithImage"] "h01Mh11Ph21Xh33cath41eh52enh62fbh71kh81ph91sh:2smh;3strh<1Hp;1p;<p;6p;4p;3p;2p;8p;7p-1p10000p4p710p8g000Gj12Tg000lj16Tg001Jj15Tg001mj1RTg002Oj1NTg002ol<?Tg004Bj6>Tg005Oj1<Tg006Zj4;Tg007mj37Tg008Gj29Tg009TR0j3:Tg00:bj20Tg00;=j1QTg00<Hj8PTg00=Zj1MTg00>dj1LTg00?nj2KTg00A9j6@Tg00BMj3ATg00Caj2BTg00Doj7=Tg00FAj1CTg00Ffj1DTg00GDj2ETg00Gaj2FTg00Hnj4GTg00J9j4HTg00KJj2ITg00LXj7JTg00Mdj88Tg00O3j34Tg00ONj3OTf0R1#2#2p=1f4R2f3R3f2R4f1R5;4134p=3g00OiR6g00QAR7#2#1R8#2#1#6#5%68#5#R[R8g00QfR9%N9R:g00RDR;g00SOR<g00TZR=g00UfR>g00W2R?g00X?R@g00YMRAf;RBf:RCf9RDf8REf7RFf6RGf5RHP2P3P4P5P1M<?PDPEPFPHP2P3E>RIPBPC%<ERJP5C;g00YmRK97AJA7A3K[p,1ARK/9CRJg00ZM5:B'0'0RLp,4segsRMPKPBPCPD%QFPGPHGPRN10ILRL%MF%LF'KRI10NLRLPMPKp,2AAp,1ERNPBP4E@RO10ILRLAAMKBRI10OLRLPMp,1Lp,2arf<PB1BNCP3F=RN10ILRLPMPB%C7#2#1#1#1#D,EJ1FKCR7CGRI10NLRLPBP7PCP2CHR710ILRLPMPKP0PB1IKCRIPGPHFJRN107LRLPMPKP0g00[`PBPJPIPFG810NL;41D3D3D3D33OW<X39X4AX7@X5?X:>X;=X9<X2;X8:X69X08X16PBPCPDPEPFPGPHP2P3P4P5P1O<X39W4W7W5W:W;W9W2W8W6W0W1o"). Qed.
Lemma crun_preA_content P M fb p X s str sm en k e cat : crun_preA P M fb p X s str sm en k e cat -> PEC.content_ok segs A M fb p (PM.p_src s) str sm.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCModelA ()) ["WithImage"] "h01Mh11Ph21Xh33cath41eh52enh62fbh71kh81ph91sh:2smh;3strh<1Hp;1p;<p;8p;6p;4p;3p;2p;7g000Gj12Tg000lj15Tg001Jj16Tg001mj1QTg002Oj1MTg002ol<>Tg00;=j1=Tg00<Hj8;Tg004Bj6:Tg005Oj17Tg006Zj49Tg007mj34Tg008Gj2PTg009TR0j3OTg00:bj20Tg00=Zj1LTg00>dj1KTg00?nj2BTg00A9j6?Tg00BMj3@Tg00Caj2ATg00Doj7<Tg00FAj1CTg00Ffj1DTg00GDj2ETg00Gaj2FTg00Hnj4GTg00J9j4HTg00KJj2ITg00LXj7JTg00Mdj88Tg00O3j31Tg00ONj3NTf0R1#2#2p=3g00OiR2g00QAR3#2#3R4#2#3#5#6%54#6#Q[R4g00QfR5%M5R6g00RDR7g00SOR8g00TZR9g00UfR:g00W2R;g00X?R<g00YMR=f;R>f:R?f9R@f8RAf7RBf6RCf5RDf4REf3RFf2RGf1RHP1M<>p,4segsRIp,1ARJP>P?P@%=BPCPDG;RKP@PAPBPDPEPFE:P>P?%7ARLPHC9g00YmRM94=LA4=FM[1PJ?RMg00ZM5O>'0'0'0RL%LB%KB'BRN10KLRLPIPJp,2AAp,1ERKP>PGE?RO10NLRLA@IJ>RN10OLRLPIp,1Lp,2arf<P>1AK?PFF<RK10NLRLPIP>%C3#2#3#3#3#D,EM1FJ?R3CGRN10KLRLP>P3P?PECHR310NLRLPIPJP0P>1IJ?RNPCPDFJRK103LRLPIPJP0g00[`P>PMPNPBG810KL;11313131313131313NW<X35X4=X7<X5;X::X;9X98X27X86X65X04X12P>P?P@PAPBPCPDPEPFPGPHP1O<X35W4W7W5W:W;W9W2W8W6W0W1o"). Qed.
Lemma crun_preA_rdr P M fb p X s str sm en k e cat : crun_preA P M fb p X s str sm en k e cat -> accA M (PMSPA.o_p A fb) RDR_BYTES.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCModelA ()) ["WithImage"] "h01Mh11Ph21Xh33cath41eh52enh62fbh71kh81ph91sh:2smh;3strh<1Hp;1p;<p;3p;2p;4p;6p;8p;7g000Gj13Tg000lj16Tg001Jj15Tg001mj1QTg002Oj1MTg002ol<?Tg005Oj1>Tg007mj34Tg008Gj2;Tg009TR0j3:Tg006Zj48Tg00:bj20Tg004Bj6PTg00;=j1OTg00<Hj8NTg00=Zj1LTg00>dj1KTg00?nj2ETg00A9j6@Tg00BMj3ATg00Caj2BTg00Doj7=Tg00FAj1CTg00Ffj1DTg00GDj2<Tg00Gaj2FTg00Hnj4GTg00J9j4HTg00KJj2ITg00LXj7JTg00Mdj89Tg00O3j37Tf0R1#3#3p=2f4R2f3R3f2R4f1R5;7137p=1g00OiR6g00QAR7#3#2R8#3#2#6#5%68#5#Q[R8g00QfR9%M9R:g00RDR;g00SOR<g00TZR=g00UfR>g00W2R?g00X?R@g00YMRAf;RBf:RCf9RDf8REf7RFf6RGf5RHP2P3P4P5P1M<?%>ERIg00YmRJ54AA4A3J[RJp,1ARK/;CRLg00ZM5:BRMPBPCPIP5C8RI10JMRMPDPEPFPHP2P3EPRJ10IMRMp,4segsRIPKPBPCPD%OFPGPHGNRN10JMRM%LF%KF'ERJ10NMRMPIPKp,2AAp,1ERNPBP4E@RO10JMRMAAIKBRJ10OMRMPIp,1Lp,2arf<PB1BNCP3F=RN10JMRMPIPB%C7#3#2#2#2#D,<L1FKCR7CGRJ10NMRMPBP7PCP2CHR710JMRMPIPKP0PB1IKCRJPGPHFJRN107MRMPIPKP0g00[`PBPLPJPFG910NMP1D1D1D1D1D1D1W<X39X4AX7@X5?X:>X;=X9<X2;X8:X69X08X16PBPCPDPEPFPGPHP2P3P4P5P1O<X39W4W7W5W:W;W9W2W8W6W0W1o"). Qed.
End WithImage.
End PECA.
