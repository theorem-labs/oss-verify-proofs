(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsA
L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecsA PmSpecsAX PmSpecsAa
PmModelFactsA PmStepA PmStep PmParStep PmASrcKit PmAParKit PmAUarK PmAUar PmParKit2 PmAParseD PmAParseK PmAParseK3 PmAParseK4 PmAParseK6.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAParseK9 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAParseD.PMALPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAParseK6.PMALPK6."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit2.PMPK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "0Aw2"; "0Awa"; "1app"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1prod"; "2and"; "2eq"; "3Z"; "0F"; "0FF"]; ["0HI"; "0K"; "0L"; "0LBX"; "0LK"; "0LK1"; "0LK2"; "0LK2'"; "0LKa"; "4Model"; "5bvmap"; "0M"; "0M1"; "0M2"; "0M2'"; "0Ma"]; ["0Q"; "0R"; "0R1"; "0R2"; "0Ra"; "6credit"; "7fframe"; "9ra_ok"; "8SCFG"; ":aframe"; ":alinv"; ":apctx"; ":lmem"; ":lregs"; ";epost"; ";jpost"]; ["<AADDR_A"; "<ADDR_A"; "=PST"; "=inv"; "=mode_flag"; "=p_src"; "=p_stk"; "=ps_mode"; "=pst"; "=pstate"; "=srcst"; "=stack_shape"; "=strm"; "=unread"; "=vstr"; ">lp_mu"]; [">lp_w"; "?cfg"; "?ec_at"; "?o_ec"; "?o_p"; "?push_rel"; "?run_pre"; "?run_spec_r"; "?src_step"; "@FPState"; "@getr"; "ATSet"; "Bsrealizes"; "Cloaded_segments"; "0S1"; "0SCFG_P"]; ["Dadd"; "Dle"; "Dlt"; "Dmul"; "Dof_nat"; "Dsub"; "0ar"; "0args"; "0cat"; "0cr"; "0cr1"; "0cr2"; "0cra"; "0dn"; "0dp"; "0e"]; ["0e1"; "0e2"; "0ea"; "0fb"; "0fl"; "0fx1"; "0fx2"; "0fxa"; "0h"; "0mo"; "0model"; "0model1"; "0model2"; "0model2'"; "0modela"; "0p"]; ["0p'"; "0pc"; "0pre"; "0prog"; "0r"; "0rr"; "0s"; "0s1"; "0s2"; "0sa"; "0sm"; "0sm1"; "0sm2"; "0sma"; "0sp"; "0src"]; ["EZ_to_bv"; "Ebv"; "0str"; "0tb"; "0tg"; "0vb"; "0vk"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMALPK9.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Lemma unread_nonneg : ltac2:(TCodec.tc2 tcn__PmAParseK9 "Q6'T1yR0%211'9y8%511%311p051'='QH'QN'QL'5&R6&R=&QA&Q@r6r5r4r3r2r1%:9987654321&RAz&QM&QE%11:%3219%6251p081pV0D1pWFF1pX6H1pW>J1pV8L1pQHN1").
Proof. intros M fb s str sm e.
intros (PA & IA & _). pose proof (PMASK.iss_size_ltA _ _ _ _ IA) as Z.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & G2 & _) & _). unfold PM.unread. lia.
Qed.
Lemma mu_strict : ltac2:(TCodec.tc2 tcn__PmAParseK9 "Q?'QH'QL&QK&QFr5%211%411r3%511%711&RAz&QM&QEr4%211%4219%7261'<'QJr6%811r8%:11%63531&RB%>25Fr7%?11%A217%5241&QO%125<r:r9%4221%;241p071p0>1p0F1p0O1p0Q31pWJQ91pWBQ;1pWDQ<1pWHQ<1pTNQ>1").
Proof. intros S1 sm1 sa s2 sm2. intros S1s S2s U0 E U. rewrite E in U. exact (PMPK2.lp_mu_lt_U S1 sm1 s2 sm2 S1s S2s U0 U). Qed.
Lemma mu_pushv_top : ltac2:(TCodec.tc2 tcn__PmAParseK9 "S3'='QJ'QN'7'QI%211'QL'QH&QK&4r6(6r5(8%11:%43;31%73<61%911&QFr3%211%=11&RB&RE&R@&RC+TP0&R0%11Br7%311%8231%7261&QD&QG%11I%311%=251%419%611%A231z%D221&RA&QM&QE%11Q2r4%4221%6281%51Q8%721Q7r?%921H%;231&R5(QBrCrBrAr@r>r=r<r;r9%QG3QN1QD%QJ3QO31%<9;:98@7651r8%?42Q91QL&QO%123Q;rD%QO3R6:QL%R23R7<1%D93CBA@H?>1%621<%QH261p091p0J1p0Q01p0Q81p0QN1p0R31pWJR?1pWBR?1pWHRA1pW2RD1pW0RE1pW6RE1pX>RK1pX<RL1pX:RM1pX8RL1pX0RN1pUNS01pULS11pVDS21").
Proof. intros mo dn dp src tb tg vb vk pre p p' sm1 s2 sm2.
intros S1s S2s DX U0 U PR.
apply (PMPK2.lp_mu_pushv _ _ (PM.PST mo dn dp src tb tg vb vk (pre ++ [p'])) sm1); [exact S1s| exact S2s| | cbn [PM.p_src]; lia| exact U0| exact U| exact PR].
cbn [PM.p_stk]. rewrite (PMPK2.lp_X_set_top pre p p'). lia.
Qed.
Lemma mu_key : ltac2:(TCodec.tc2 tcn__PmAParseK9 "Q?'QH'QL&QK&QFr5%211%411r3%511%711&RAz&QM&QEr4%211%4219%7261'<'QJr6%811r8%:11%63531&RB%>25Fr7%?11%A217%5241&QO%125<r:r9%4221%;241p071p0>1p0F1p0O1p0Q31pWJQ91pWBQ;1pWDQ<1pWHQ<1pTNQ>1").
Proof. intros S1 sm1 sa s2 sm2. exact (mu_strict S1 sm1 sa s2 sm2). Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Lemma vcall_j : ltac2:(TCodec.tc2 tcn__PmAParseK9 "X3&R;&Jy5'T1yR0%211%5241'9y8%611%311p061'I'7':'=%2211%411&Q6%611&Q5'QH'QN'QL'5!p051p0<1p0F1p064p071p0:1p0;1p0K1'R9p0>6&R7vR?&R=&QA&Q@vBvRFv@r@r?r=r<%<;;:987654321&Q;rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJrIrHrG%BENJIHA@?>=<;:987654321&Q9rFrErDrC%5BQ0ONGFEDCBA@?;74321&Q<rQ8r;r:r9r8r7r6r5%9JQ:Q9Q88Q1Q0ONMLKJHFEDCBQ47654321';&RAz%221?+9%42A1%6231&Q=rQ:&R4%12QGQ5&R3%12QIQ7%665QDQ:31Q2'<&R:&T0&RDu1%211%42S61%62QM1%62S6Q3%93S621&Q7%11Q7rB%Q931QIR1&QCr>%211&R2%E2R=R0%25R?Q=1OR0rQJrQBrQ@%L2RB1%K2RC2%Q065Q=421OrQKrQIrQHrQGrQFrQErQDrQCrQArQ?rQ>rQ=rQ<rQ;r4r3r2%R3JS4S3S2AG@?>=<;:987654QOQNQMQLQK321&Q?rQMrQL%3LS<S8S7S621EKDCBA@?J=I<;:9R4R2R1R0QO76'R<&Q8%11S?&R1%16S@S8S7S3R:R9rQN%64SB421p081p0=1p0Q01pUFT81pV2T51pWHT71pW@T:1p4T?1pQ<T>1pVHTF1pQJTH1pR6TN1pV<T31%QF1J%S:5MS1LS0K&QM&QE%11Q0%321Q0%RG2RF1&R8%51S<%61RM%3421S;Q6%S:2S0ROp021p071p0=1p0?1pWJTO1pWBU21pR8UB1&Q:r1%2LTBTAT@Q;QOR5QNQMQLQKQJQIR4QGR3QFQEQDQCS=S<S;S:S9QAQ@Q?1%SL2S:QB+e`m0%Q96THT?SB1SAS@rQO%Q>4TJQ<21p051p071pUHU?1pV4U<1pWJU>1pWBUA1p6UF1pQ@UE1pVLUM1pQNUO1pR8V51pV>U:1%QH6U7T=T<TBT;T8%QL4U8QJ1R<p031p0H1p0Q<1p0RM1p0S11p0S51p0S81p0S;1p0SF1p0SN1p0T61p0TA1p0TH1p0U<1pR2UJ1pUJV:1pV6V71pWLV91pWDV<1p8VA1pQBV@1pVNVH1pR0VJ1pR:W01pV@V51pW8V71pU@V=1pW<VK1pVBVL1pW4VM1pVJW11pQLW31pQ>VL1pV:W11pNW21pV0VJ1pWFVL1pX6VN1pW>W01pUBW71pV8W81pW:W91pWNW:1pUDW61p2W:1pQ:W91pQ0W:1pQ8W=1pVFWC1pQHWE1pR4WK1pQ4X21").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 pc h rr args prog fxa Ra Ma modela LKa Awa sa sma ea cra Q.
intros CALLEE CTX G LM Hh LR G1 RA ARG INV1 EC1 AFT PQ IHQ.
pose proof LR as (X2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X3 & X4).
apply (PMALPK3.alp_call_run L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 pc h args prog fxa Ra Ma modela LKa Awa sa sma ea cra rr
CALLEE CTX G LM Hh G1 RA X2 X3 X4 ARG INV1 EC1).
intros fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 RP2 POST2 LM2.
apply (AFT fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 (PMALPK4.lregs_pres R Ra R2 sp _ _ F LR RP2) LM2).
destruct POST2 as (RPR2 & STP2 & _ & [(v & Hv & ECv & _)|(EC2 & INV2 & PP2)]).
- left. exists v, (pa_errcat_obj PMA.AD). split; [exact Hv| exact ECv].
- right. split; [exact EC2|]. split; [exact INV2|].
intros fx3 R3 model3 LI3. exact (IHQ fx3 R3 M2' model3 LK2' Aw2 s2 sm2 e2 cr2 LI3 (PQ R2 s2 sm2 INV2 PP2 (unread_nonneg _ _ _ _ _ _ RPR2) STP2)).
Qed.
Lemma vcall_e : ltac2:(TCodec.tc2 tcn__PmAParseK9 "X3&R;&Jy5'T1yR0%211%5241'9y8%611%311p061'I'7':'=%2211%411&Q6%611&Q5'QH'QN'QL'5!p051p0<1p0F1p064p071p0:1p0;1p0K1'R9p0>6&R7vR?&R=&QA&Q@vBvRFv@r@r?r=r<%<;;:987654321&Q;rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJrIrHrG%BENJIHA@?>=<;:987654321&Q9rFrErDrC%5BQ0ONGFEDCBA@?;74321&Q<rQ8r;r:r9r8r7r6r5%9JQ:Q9Q88Q1Q0ONMLKJHFEDCBQ47654321';&RAz%221?+9%42A1%6231&Q=rQ:&R4%12QGQ5&R3%12QIQ7%665QDQ:31Q2'<&R:&T0&RDu1%211%42S61%62QM1%62S6Q3%93S621&Q7%11Q7rB%Q931QIR1&QCr>%211&R2%E2R=R0%25R?Q=1OR0rQJrQBrQ@%L2RB1%K2RC2%Q065Q=421OrQKrQIrQHrQGrQFrQErQDrQCrQArQ?rQ>rQ=rQ<rQ;r4r3r2%R3JS4S3S2AG@?>=<;:987654QOQNQMQLQK321&Q>rQMrQL%3LS<S8S7S621EKDCBA@?J=I<;:9R4R2R1R0QO76'R<&Q8%11S?&R1%16S@S8S7S3R:R9rQN%64SB421p081p0=1p0Q01pUFT81pV2T51pWHT71pW@T:1p4T?1pQ<T>1pVHTF1pQJTH1pR6TN1pV<T31%QF1J%S:5MS1LS0K&QM&QE%11Q0%321Q0%RG2RF1&R8%51S<%61RM%3421S;Q6%S:2S0ROp021p071p0=1p0?1pWJTO1pWBU21pR8UB1&Q:r1%2LTBTAT@Q;QOR5QNQMQLQKQJQIR4QGR3QFQEQDQCS=S<S;S:S9QAQ@Q?1%SL2S:QB+e`m0%Q96THT?SB1SAS@rQO%Q>4TJQ<21p051p071pUHU?1pV4U<1pWJU>1pWBUA1p6UF1pQ@UE1pVLUM1pQNUO1pR8V51pV>U:1%QH6U7T=T<TBT;T8%QL4U8QJ1R<p031p0H1p0Q<1p0RM1p0S11p0S51p0S81p0S;1p0SF1p0SN1p0T61p0TA1p0TH1p0U<1pR2UJ1pUJV:1pV6V71pWLV91pWDV<1p8VA1pQBV@1pVNVH1pR0VJ1pR:W01pV@V51pW8V71pU@V=1pW<VK1pVBVL1pW4VM1pVJW11pQLW31pQ>VL1pV:W11pNW21pV0VJ1pWFVL1pX6VN1pW>W01pUBW71pV8W81pW:W91pWNW:1pUDW61p2W:1pQ:W91pQ0W:1pQ8W=1pVFWC1pQHWE1pR4WK1pQ4X21").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 pc h rr args prog fxa Ra Ma modela LKa Awa sa sma ea cra Q.
intros CALLEE CTX G LM Hh LR G1 RA ARG INV1 EC1 AFT PQ IHQ.
pose proof LR as (X2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X3 & X4).
apply (PMALPK3.alp_call_run L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 pc h args prog fxa Ra Ma modela LKa Awa sa sma ea cra rr
CALLEE CTX G LM Hh G1 RA X2 X3 X4 ARG INV1 EC1).
intros fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 RP2 POST2 LM2.
apply (AFT fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 (PMALPK4.lregs_pres R Ra R2 sp _ _ F LR RP2) LM2).
destruct POST2 as (RPR2 & STP2 & _ & [(v & Hv & ECv & MO & _)|(EC2 & INV2 & PP2)]).
- left. exists v, (pa_errcat_obj PMA.AD). split; [exact Hv| split; [exact ECv| exact MO]].
- right. split; [exact EC2|]. split; [exact INV2|].
intros fx3 R3 model3 LI3. exact (IHQ fx3 R3 M2' model3 LK2' Aw2 s2 sm2 e2 cr2 LI3 (PQ R2 s2 sm2 INV2 PP2 (unread_nonneg _ _ _ _ _ _ RPR2) STP2)).
Qed.
End WithHeap.
End PMALPK9.
