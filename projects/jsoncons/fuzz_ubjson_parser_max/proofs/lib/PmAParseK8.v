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
PmModelFactsA PmStepA PmStep PmParStep PmASrcKit PmAParKit PmAUarK PmAUar PmParKit2 PmParKit PmAParseD PmAParseK PmAParseK4 PmAParseK5 PmAParseK7 PmAParseX PmAParseP5.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAParseK8 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAParseD.PMALPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "1app"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1prod"; "2and"; "2eq"; "2iff"; "3Z"; "0F"; "0FF"; "0HI"]; ["0K"; "0L"; "0LBX"; "0LK"; "0LK1"; "0LK2"; "4Model"; "5bvmap"; "0M"; "0M1"; "0M2"; "0M2'"; "0R"; "0R1"; "0R2"; "6credit"]; ["7fframe"; "8SCFG"; "9aframe"; "9alinv"; "9apctx"; "9lmem"; "9lregs"; ":ADDR_A"; ";PS"; ";PST"; ";inv"; ";mode_bottom"; ";mode_counted"; ";mode_indef"; ";pst"; ";pstate"]; [";pstate_ok"; ";srcst"; ";strm"; ";vstr"; "<cfg"; "<ec_at"; "<o_ec"; "<o_p"; "=make_ec_spec"; ">FPState"; ">getr"; "?TSet"; "@srealizes"; "Aloaded_segments"; "0SCFG_P"; "Ble"]; ["Bof_nat"; "0ar"; "0c"; "0cat"; "0cq"; "0cr"; "0cr1"; "0dn1"; "0dp1"; "0e"; "0e1"; "0fb"; "0fl"; "0fx1"; "0fx2"; "0i"]; ["0l"; "0m"; "0m'"; "0mo1"; "0model"; "0model1"; "0model2"; "0model2'"; "0pre"; "0r"; "0s"; "0s1"; "0sm"; "0sm1"; "0sp"; "0src1"]; ["CZ_to_bv"; "Cbv"; "0str"; "0t"; "0tb1"; "0tg1"; "0ti"; "0tl"; "0tt"; "0v"; "0vb1"; "0vk1"; "0vq"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMALPK8.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Lemma pstate_ok_mode : ltac2:(TCodec.tc2 tcn__PmAParseK8 "Q4'<&Q@(Q8r5r3r2r1%544321%711&;&Q<r6%211%31:%5221&Q=r7%211%317%:221&Q;r8%211%317%?221%G449>F%I11p031p091p0?1p0F1pU0O1pV8Q01pU2Q11pU6Q21pU4Q31").
Proof. intros m m' l t i.
intros (T0 & [(Hm & X)|[(Hm & X)|(Hm & X)]]) E1 E2 E3; split; [exact T0| |exact T0| |exact T0|]; cbn [PM.ps_mode] in *.
- left. split; [apply E1; exact Hm| exact X].
- right; left. split; [apply E2; exact Hm| exact X].
- right; right. split; [apply E3; exact Hm| exact X].
Qed.
Ltac miff := unfold PM.mode_counted, PM.mode_indef, PM.mode_bottom; let X := fresh "X" in split; intros X; clear - X; Lia.lia.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Lemma mkec_exit : ltac2:(TCodec.tc2 tcn__PmAParseK8 "U4&QK&Gy5'S1yR0%211%5241'7y8%611%311p061'F'5'8'<%2211%411&Q0%611&O'Q>'QC'QB'3'QI&QHvQNvAvR1v?%544321&Q4rQ4rQ3rQ2rQ1rQ0rOrNrMrLrKrJrIrHrGrFrErD%BEGFEDA@?>=<;:987654321&Q2rCrBrAr@%5BLKJGFEDCBA@?;74321&Q6rQ5r?&QG&Q7%221D&QF%123F%8676I31A&Q5rQ6r>r=r<r;r:r9r8%9JQ?Q>Q=8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321':&QJ&S0&R0u1%211%42R@1%62M1+ebfH%72RA1%:3RA31u:%911%;2RG1%=2Q51%L2NQD%>2RH1%A3RH31u;%@11%B2RN1%D2Q=1%D2RNJ%G3RN21'9&QO+1%221Q0+R0%42Q21%6231&QE&QM%Q>2Q@R9%352QM1Q7Q6'QL&Q1%11RF&QD+ej[D%268R6R51R4R3rQ=%74:521p091p0>1p0F1p0M1p0Q51p0QA1p0QL1p0R61p0R=1p0S11pT:SB1pVJSC1pVDSD1pT>S@1pTFS=1pULS?1pUHSB1p4SG1pQ:SF1pU<SN1pQDT01pQLT61pTLSD1pU>T21pQFT41pQ<SM1pTJT21pLT31pTDSK1pUJSM1pV6SO1pUFT11pT8T81pTHT91pUDT:1pUNT;1pT<T71p2T;1pQ8T:1pNT;1pQ6T>1pU:TD1pQBTF1pQJTL1pQ2U31").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v vq cq.
intros MKE CTX G LR LM G1 G10 G11 Hv EC1.
pose proof LR as (X2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X3 & X4).
apply (PMALPK7.mkec_call L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 0xacad8 v vq cq MKE CTX G LM G1 ltac:(split; [clear; lia| reflexivity]) X2 X3 X4 G10 G11 Hv EC1).
intros fx2 R2 M2' model2' LK2' Aw2 RP2 LM2 EC2.
pose proof (PMALPK4.lregs_pres R R1 R2 sp _ _ F LR RP2) as LR2.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M2' model2' LK2' Aw2 s1 sm1 true cr1 v (pa_errcat_obj PMA.AD) CTX G LM2 EC2) as LF.
pose proof LR2 as LR0.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw2 model2') M2') in *.
PMALPK5.lf_open LF. PMALPK5.lr_open LR2.
cfeed P (PMALPP5.alpZ_conc fx2 R2 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PMALPP5.aligned; assumption]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & _ & MO3).
apply (PMALPK7.more0_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M2' model2' LK2' Aw2 s1 sm1 true cr1 fx2 fx3 R2 R3 0xacad8 0xac2a0 M3v v (pa_errcat_obj PMA.AD) CTX G LM2 MS3 MG3 FRZ3 MO3 EC2).
intros M3 model3 LM3 EC3.
apply (PMALPX.parse_exit L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx3 R3 M3 model3 LK2' Aw2 (PMPK.set_more s1 0) sm1 true cr1 v (pa_errcat_obj PMA.AD) CTX G); [| exact LM3| exact EC3].
apply (PMALPK4.lregs_ks R R2 R3 sp op oec F PMALPP5.KS_alpZ LR0 KS3). PMALPK4.ksinc.
Qed.
Lemma after_keye_5 : ltac2:(TCodec.tc2 tcn__PmAParseK8 "T5&QK&Gy5'S1yR0%211%5241'7y8%611%311p061'F'5'8'<%2211%411&Q0%611&O'Q>'QC'QB'3'QI&Q4vQNvAvR1v?rQ2rQ1rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrB%FEEDCBA@?>=<;:987654321&Q2rAr@r?r>%5BJIHGFEDCBA@?;74321&Q6rQ3r=&QG&Q7%221D&QF%123F%8676I31A&Q5rQ4r<r;r:r9r8r7r6%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321'9&QO+1%2215+R0%4271%6231&QE&QM%F2HQ>%352Q01=<'QL&Q1%11QL&QD+eaj4%268Q;Q81Q7Q6rQ8%74:521p091p0>1p0F1p0Q11p0Q;1p0QB1pT6RD1pVDRE1pT>RA1pTFR>1pULR@1pUHRC1p4RH1pQ:RG1pU<RO1pQDS11pQLS71pTLRE1pU>S31pQFS51pQ<RN1pTJS31pLS41pTDRL1pUJRN1pV6S01pUFS21pT8S91pTHS:1pUDS;1pUNS<1pT<S81p2S<1pQ8S;1pNS<1pQ6S?1pU:SE1pQBSG1pQJSM1pQ2T41").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c.
intros CTX G LR LM Hv EC1.
pose proof LR as LR0.
pose proof CTX as CTX0. destruct CTX0 as (HH & _ & _ & _ & _ & _ & FOK & _).
pose proof LM as (BI & _). pose proof BI as (HH1 & _).
assert (FOK' : PMSPA.frame_okA ((F, 1, sp - 256 + 32) :: FF) fb) by exact (PMAUAR.frame_okA_push FF fb F 1 (sp - 256 + 32) FOK).
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb v c HH1 FOK' EC1) as (_ & _ & _ & _ & EV & _).
assert (Hv' : 0 <= v < 2 ^ 64) by (clear - Hv; lia).
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
cfeed P (PMALPP5.alpK5e_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 56%nat => v | _ => 0 end)) ltac:(first [assumption | unfold PMALPP5.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMALPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xac744 0xac2a0 M2v K G LM MS2 FRZ2).
intros model1' LM'.
apply (PMALPX.parse_exit L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 v c CTX G); [| exact LM'| exact EC1].
apply (PMALPK4.lregs_ks R R1 R2 sp op oec F PMALPP5.KS_alpK5e LR0 KS2). PMALPK4.ksinc.
Qed.
Lemma after_key0_5 : ltac2:(TCodec.tc2 tcn__PmAParseK8 "V1&QK&Gy5'S1yR0%211%5241'7y8%611%311p061'F'5'8'<%2211%411&Q0%611&O'Q>'QC'QB'3'QI'QA'Q?%?11&Q4vQNvAvR1v?rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrK%FEEDCBA@?>=<;:987654321&Q2rJrIrHrG%5BJIHGFEDCBA@?;74321&Q6rQ<rF&QG&Q7%221D&QF%123F%8676I31A&Q5rQ=rErDrC(Q9rBrAr@r?r>r=r<r;&2r:(4(Q8+5r9r8r7%544321(6%11R0%93R131%<3R2;1%F9EDCBA@?>1r6r5r4%OJR3R2R1NQ7R0QOQNQMQLQKQJQHQFQEQDQCQBQ6MLK4321&QE&QM%Q52Q7QLz%453Q?21QM&Q:%E4DIGC%G3R?1?%J3R@L1%Q49Q6Q5Q3Q2Q1Q0ON1%511&Q3rQDrQCrQBrQArQ@rQ?rQ>r3r2r1+6%Q641Q?Q>Q=%Q83S01Q0%Q;3S1QB1%QE9R7R6R5R1QHQGQFQD1%@LRORNRM?>=<;:9QJR3RKRJRIRHRGRFRE876R<R91Q@Q?Q>'QL&Q1%11S3&QD+e`m0%26Q0Q4Q31>=rQF%74Q2521p091pU@SL1pQHSN1pQNT41pTNSB1+eaj4%;6Q9RLRK1RHRG%?4Q:=1Mp041p0Q31p0Q:1p0Q@1p0RA1p0RK1p0S21pT>T21pTFSO1pULT11pV>T:1pVBT;1pV@T<1pUBT01pVHT>1pVFT?1pV<T@1pV:T:1pV0T71pTBTC1pT@TD1pU8TE1p4TD1pQ:TC1pU<TK1pQDTM1pQLU31pTLTA1pU>TO1pQFU11pQ<TJ1pTJTO1pLU01pTDTH1pUJTJ1pV6TL1pUFTN1pT8U51pTHU61pUDU71pUNU81pT<U41p2U81pQ8U71pNU81pQ6U;1pU:UA1pQBUC1pQJUI1pQ2V01").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CTX G LR LM EC1 INV1 IHX.
pose proof LR as LR0.
pose proof CTX as CTX0. destruct CTX0 as (HH & _ & _ & _ & _ & _ & FOK & _).
pose proof LM as (BI & _). pose proof BI as (HH1 & _).
assert (FOK' : PMSPA.frame_okA ((F, 1, sp - 256 + 32) :: FF) fb) by exact (PMAUAR.frame_okA_push FF fb F 1 (sp - 256 + 32) FOK).
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt ti])) sm1 e1 cr1 pre (PM.PS 5 tl tt ti) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb 0 cat HH1 FOK' EC1) as (_ & _ & _ & _ & EV & _).
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt ti])) sm1 e1 cr1 CTX G LM) as (_ & HD9 & _).
pose proof INV1 as (_ & ID1 & _ & SH1 & _). cbn [PM.p_done PM.p_stk] in ID1, HD9, SH1. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 5 tl tt ti) SH1) as (TOK & _).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & _). cbn [PM.ps_mode] in PT0.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
cfeed P (PMALPP5.alpK50_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 34%nat => T | _ => 0 end)) ltac:(first [assumption | unfold PMALPP5.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _ & _ & WM).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
pose proof (PMALPK7.pstate_mode_upd MV M2v T 5 tl tt ti 6 PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZ2 WM) as PT2.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 5 tl tt ti) (PM.PS 6 tl tt ti) sm1 e1 cr1 0 4
fx1 fx2 R1 R2 0xac744 0xac3a0 M2v 0 cat CTX G LM MS2 MG2 FRZ2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PT2 EC1).
intros M1' model1' LM' FR' EC'.
apply (IHX fx2 R2 M1' model1'). split; [| split; [| split; [exact EC'| exact LM']]].
+ apply (PMALPK4.lregs_ks R R1 R2 sp op oec F PMALPP5.KS_alpK50 LR0 KS2). PMALPK4.ksinc.
+ apply (PMALPK7.inv_set_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre _ _ INV1); [apply (pstate_ok_mode 5 6 tl tt ti TOK); miff| cbn [PM.ps_mode]; miff].
Qed.
Lemma after_keye_7 : ltac2:(TCodec.tc2 tcn__PmAParseK8 "T5&QK&Gy5'S1yR0%211%5241'7y8%611%311p061'F'5'8'<%2211%411&Q0%611&O'Q>'QC'QB'3'QI&Q4vQNvAvR1v?rQ2rQ1rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrB%FEEDCBA@?>=<;:987654321&Q2rAr@r?r>%5BJIHGFEDCBA@?;74321&Q6rQ3r=&QG&Q7%221D&QF%123F%8676I31A&Q5rQ4r<r;r:r9r8r7r6%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321'9&QO+1%2215+R0%4271%6231&QE&QM%F2HQ>%352Q01=<'QL&Q1%11QL&QD+ea`@%268Q;Q81Q7Q6rQ8%74:521p091p0>1p0F1p0Q11p0Q;1p0QB1pT6RD1pVDRE1pT>RA1pTFR>1pULR@1pUHRC1p4RH1pQ:RG1pU<RO1pQDS11pQLS71pTLRE1pU>S31pQFS51pQ<RN1pTJS31pLS41pTDRL1pUJRN1pV6S01pUFS21pT8S91pTHS:1pUDS;1pUNS<1pT<S81p2S<1pQ8S;1pNS<1pQ6S?1pU:SE1pQBSG1pQJSM1pQ2T41").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c.
intros CTX G LR LM Hv EC1.
pose proof LR as LR0.
pose proof CTX as CTX0. destruct CTX0 as (HH & _ & _ & _ & _ & _ & FOK & _).
pose proof LM as (BI & _). pose proof BI as (HH1 & _).
assert (FOK' : PMSPA.frame_okA ((F, 1, sp - 256 + 32) :: FF) fb) by exact (PMAUAR.frame_okA_push FF fb F 1 (sp - 256 + 32) FOK).
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb v c HH1 FOK' EC1) as (_ & _ & _ & _ & EV & _).
assert (Hv' : 0 <= v < 2 ^ 64) by (clear - Hv; lia).
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
cfeed P (PMALPP5.alpK7e_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 56%nat => v | _ => 0 end)) ltac:(first [assumption | unfold PMALPP5.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMALPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xac610 0xac2a0 M2v K G LM MS2 FRZ2).
intros model1' LM'.
apply (PMALPX.parse_exit L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 v c CTX G); [| exact LM'| exact EC1].
apply (PMALPK4.lregs_ks R R1 R2 sp op oec F PMALPP5.KS_alpK7e LR0 KS2). PMALPK4.ksinc.
Qed.
Lemma after_key0_7 : ltac2:(TCodec.tc2 tcn__PmAParseK8 "V1&QK&Gy5'S1yR0%211%5241'7y8%611%311p061'F'5'8'<%2211%411&Q0%611&O'Q>'QC'QB'3'QI'QA'Q?%?11&Q4vQNvAvR1v?rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrK%FEEDCBA@?>=<;:987654321&Q2rJrIrHrG%5BJIHGFEDCBA@?;74321&Q6rQ<rF&QG&Q7%221D&QF%123F%8676I31A&Q5rQ=rErDrC(Q9rBrAr@r?r>r=r<r;&2r:(4(Q8+7r9r8r7%544321(6%11R0%93R131%<3R2;1%F9EDCBA@?>1r6r5r4%OJR3R2R1NQ7R0QOQNQMQLQKQJQHQFQEQDQCQBQ6MLK4321&QE&QM%Q52Q7QLz%453Q?21QM&Q:%E4DIGC%G3R?1?%J3R@L1%Q49Q6Q5Q3Q2Q1Q0ON1%511&Q3rQDrQCrQBrQArQ@rQ?rQ>r3r2r1+8%Q641Q?Q>Q=%Q83S01Q0%Q;3S1QB1%QE9R7R6R5R1QHQGQFQD1%@LRORNRM?>=<;:9QJR3RKRJRIRHRGRFRE876R<R91Q@Q?Q>'QL&Q1%11S3&QD+e`m0%26Q0Q4Q31>=rQF%74Q2521p091pU@SL1pQHSN1pQNT41pTNSB1+ea`@%;6Q9RLRK1RHRG%?4Q:=1Mp041p0Q31p0Q:1p0Q@1p0RA1p0RK1p0S21pT>T21pTFSO1pULT11pV>T:1pVBT;1pV@T<1pUBT01pVHT>1pVFT?1pV<T@1pV:T:1pV0T71pTBTC1pT@TD1pU8TE1p4TD1pQ:TC1pU<TK1pQDTM1pQLU31pTLTA1pU>TO1pQFU11pQ<TJ1pTJTO1pLU01pTDTH1pUJTJ1pV6TL1pUFTN1pT8U51pTHU61pUDU71pUNU81pT<U41p2U81pQ8U71pNU81pQ6U;1pU:UA1pQBUC1pQJUI1pQ2V01").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CTX G LR LM EC1 INV1 IHX.
pose proof LR as LR0.
pose proof CTX as CTX0. destruct CTX0 as (HH & _ & _ & _ & _ & _ & FOK & _).
pose proof LM as (BI & _). pose proof BI as (HH1 & _).
assert (FOK' : PMSPA.frame_okA ((F, 1, sp - 256 + 32) :: FF) fb) by exact (PMAUAR.frame_okA_push FF fb F 1 (sp - 256 + 32) FOK).
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt ti])) sm1 e1 cr1 pre (PM.PS 7 tl tt ti) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb 0 cat HH1 FOK' EC1) as (_ & _ & _ & _ & EV & _).
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt ti])) sm1 e1 cr1 CTX G LM) as (_ & HD9 & _).
pose proof INV1 as (_ & ID1 & _ & SH1 & _). cbn [PM.p_done PM.p_stk] in ID1, HD9, SH1. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 7 tl tt ti) SH1) as (TOK & _).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & _). cbn [PM.ps_mode] in PT0.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
cfeed P (PMALPP5.alpK70_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 34%nat => T | _ => 0 end)) ltac:(first [assumption | unfold PMALPP5.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _ & _ & WM).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
pose proof (PMALPK7.pstate_mode_upd MV M2v T 7 tl tt ti 8 PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZ2 WM) as PT2.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 7 tl tt ti) (PM.PS 8 tl tt ti) sm1 e1 cr1 0 4
fx1 fx2 R1 R2 0xac610 0xac3a0 M2v 0 cat CTX G LM MS2 MG2 FRZ2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PT2 EC1).
intros M1' model1' LM' FR' EC'.
apply (IHX fx2 R2 M1' model1'). split; [| split; [| split; [exact EC'| exact LM']]].
+ apply (PMALPK4.lregs_ks R R1 R2 sp op oec F PMALPP5.KS_alpK70 LR0 KS2). PMALPK4.ksinc.
+ apply (PMALPK7.inv_set_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre _ _ INV1); [apply (pstate_ok_mode 7 8 tl tt ti TOK); miff| cbn [PM.ps_mode]; miff].
Qed.
Lemma after_keye_9 : ltac2:(TCodec.tc2 tcn__PmAParseK8 "T5&QK&Gy5'S1yR0%211%5241'7y8%611%311p061'F'5'8'<%2211%411&Q0%611&O'Q>'QC'QB'3'QI&Q4vQNvAvR1v?rQ2rQ1rQ0rOrNrMrLrKrJrIrHrGrFrErDrCrB%FEEDCBA@?>=<;:987654321&Q2rAr@r?r>%5BJIHGFEDCBA@?;74321&Q6rQ3r=&QG&Q7%221D&QF%123F%8676I31A&Q5rQ4r<r;r:r9r8r7r6%9JQ=Q<Q;8AQ:Q9Q8Q7Q6Q5Q4Q2Q0ONML@7654321'9&QO+1%2215+R0%4271%6231&QE&QM%F2HQ>%352Q01=<'QL&Q1%11QL&QD+ebU8%268Q;Q81Q7Q6rQ8%74:521p091p0>1p0F1p0Q11p0Q;1p0QB1pT6RD1pVDRE1pT>RA1pTFR>1pULR@1pUHRC1p4RH1pQ:RG1pU<RO1pQDS11pQLS71pTLRE1pU>S31pQFS51pQ<RN1pTJS31pLS41pTDRL1pUJRN1pV6S01pUFS21pT8S91pTHS:1pUDS;1pUNS<1pT<S81p2S<1pQ8S;1pNS<1pQ6S?1pU:SE1pQBSG1pQJSM1pQ2T41").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c.
intros CTX G LR LM Hv EC1.
pose proof LR as LR0.
pose proof CTX as CTX0. destruct CTX0 as (HH & _ & _ & _ & _ & _ & FOK & _).
pose proof LM as (BI & _). pose proof BI as (HH1 & _).
assert (FOK' : PMSPA.frame_okA ((F, 1, sp - 256 + 32) :: FF) fb) by exact (PMAUAR.frame_okA_push FF fb F 1 (sp - 256 + 32) FOK).
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 v c CTX G LM EC1) as LF.
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb v c HH1 FOK' EC1) as (_ & _ & _ & _ & EV & _).
assert (Hv' : 0 <= v < 2 ^ 64) by (clear - Hv; lia).
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
cfeed P (PMALPP5.alpK9e_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 56%nat => v | _ => 0 end)) ltac:(first [assumption | unfold PMALPP5.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _).
apply (PMALPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 e1 cr1 fx1 fx2 R1 R2 0xac8a8 0xac2a0 M2v K G LM MS2 FRZ2).
intros model1' LM'.
apply (PMALPX.parse_exit L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M1 model1' LK1 Aw1 s1 sm1 e1 cr1 v c CTX G); [| exact LM'| exact EC1].
apply (PMALPK4.lregs_ks R R1 R2 sp op oec F PMALPP5.KS_alpK9e LR0 KS2). PMALPK4.ksinc.
Qed.
Lemma after_key0_9 : ltac2:(TCodec.tc2 tcn__PmAParseK8 "V1&QK&Gy5'S1yR0%211%5241'7y8%611%311p061'F'5'8'<%2211%411&Q0%611&O'Q>'QC'QB'3'QI'QA'Q?%?11&Q4vQNvAvR1v?rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrLrK%FEEDCBA@?>=<;:987654321&Q2rJrIrHrG%5BJIHGFEDCBA@?;74321&Q6rQ<rF&QG&Q7%221D&QF%123F%8676I31A&Q5rQ=rErDrC(Q9rBrAr@r?r>r=r<r;&2r:(4(Q8+9r9r8r7%544321(6%11R0%93R131%<3R2;1%F9EDCBA@?>1r6r5r4%OJR3R2R1NQ7R0QOQNQMQLQKQJQHQFQEQDQCQBQ6MLK4321&QE&QM%Q52Q7QLz%453Q?21QM&Q:%E4DIGC%G3R?1?%J3R@L1%Q49Q6Q5Q3Q2Q1Q0ON1%511&Q3rQDrQCrQBrQArQ@rQ?rQ>r3r2r1+:%Q641Q?Q>Q=%Q83S01Q0%Q;3S1QB1%QE9R7R6R5R1QHQGQFQD1%@LRORNRM?>=<;:9QJR3RKRJRIRHRGRFRE876R<R91Q@Q?Q>'QL&Q1%11S3&QD+e`m0%26Q0Q4Q31>=rQF%74Q2521p091pU@SL1pQHSN1pQNT41pTNSB1+ebU8%;6Q9RLRK1RHRG%?4Q:=1Mp041p0Q31p0Q:1p0Q@1p0RA1p0RK1p0S21pT>T21pTFSO1pULT11pV>T:1pVBT;1pV@T<1pUBT01pVHT>1pVFT?1pV<T@1pV:T:1pV0T71pTBTC1pT@TD1pU8TE1p4TD1pQ:TC1pU<TK1pQDTM1pQLU31pTLTA1pU>TO1pQFU11pQ<TJ1pTJTO1pLU01pTDTH1pUJTJ1pV6TL1pUFTN1pT8U51pTHU61pUDU71pUNU81pT<U41p2U81pQ8U71pNU81pQ6U;1pU:UA1pQBUC1pQJUI1pQ2V01").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CTX G LR LM EC1 INV1 IHX.
pose proof LR as LR0.
pose proof CTX as CTX0. destruct CTX0 as (HH & _ & _ & _ & _ & _ & FOK & _).
pose proof LM as (BI & _). pose proof BI as (HH1 & _).
assert (FOK' : PMSPA.frame_okA ((F, 1, sp - 256 + 32) :: FF) fb) by exact (PMAUAR.frame_okA_push FF fb F 1 (sp - 256 + 32) FOK).
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 pre (PM.PS 9 tl tt ti) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMAPAR.oec_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 fb 0 cat HH1 FOK' EC1) as (_ & _ & _ & _ & EV & _).
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 9 tl tt ti])) sm1 e1 cr1 CTX G LM) as (_ & HD9 & _).
pose proof INV1 as (_ & ID1 & _ & SH1 & _). cbn [PM.p_done PM.p_stk] in ID1, HD9, SH1. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 9 tl tt ti) SH1) as (TOK & _).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & _). cbn [PM.ps_mode] in PT0.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
cfeed P (PMALPP5.alpK90_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 34%nat => T | _ => 0 end)) ltac:(first [assumption | unfold PMALPP5.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & _ & _ & WM).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
pose proof (PMALPK7.pstate_mode_upd MV M2v T 9 tl tt ti 10 PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZ2 WM) as PT2.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 9 tl tt ti) (PM.PS 10 tl tt ti) sm1 e1 cr1 0 4
fx1 fx2 R1 R2 0xac8a8 0xac3a0 M2v 0 cat CTX G LM MS2 MG2 FRZ2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PT2 EC1).
intros M1' model1' LM' FR' EC'.
apply (IHX fx2 R2 M1' model1'). split; [| split; [| split; [exact EC'| exact LM']]].
+ apply (PMALPK4.lregs_ks R R1 R2 sp op oec F PMALPP5.KS_alpK90 LR0 KS2). PMALPK4.ksinc.
+ apply (PMALPK7.inv_set_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre _ _ INV1); [apply (pstate_ok_mode 9 10 tl tt ti TOK); miff| cbn [PM.ps_mode]; miff].
Qed.
End WithHeap.
End PMALPK8.
