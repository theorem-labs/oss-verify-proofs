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
PmModelFactsA PmStepA PmStep PmParStep PmASrcKit PmAParKit PmAUarK PmAUar PmParKit2 PmParKit PmAParseD PmAParseK PmAParseK3 PmAParseK4 PmAParseK5 PmAParseK6 PmAParseK7 PmAParseK8 PmAParseK9 PmAParseP1 PmAParseP2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAParseA2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAParseD.PMALPD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit2.PMPK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw1"; "0Aw2"; "1app"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1prod"; "2eq"; "3Z"; "0F"; "0FF"; "0HI"; "0K"]; ["0L"; "0LBX"; "0LK"; "0LK1"; "0LK2"; "0LK2'"; "4Model"; "5bvmap"; "0M"; "0M1"; "0M2"; "0M2'"; "0R"; "0R1"; "0R2"; "6credit"]; ["7fframe"; "8SCFG"; "9aframe"; "9alinv"; "9apctx"; ":PS"; ":PST"; ":pst"; ":pstate"; ":srcst"; ":strm"; ":vstr"; ";lp_mu"; "<cfg"; "=end_array_spec"; "=end_object_spec"]; ["=read_key_spec"; ">FPState"; "?TSet"; "@srealizes"; "Aloaded_segments"; "0SCFG_P"; "Blt"; "0ar"; "0cat"; "0cr"; "0cr1"; "0cr2"; "0dn1"; "0dp1"; "0e"; "0e1"]; ["0e2"; "0fb"; "0fl"; "0fx1"; "0fx2"; "0mo1"; "0model"; "0model1"; "0model2"; "0model2'"; "0pre"; "0r"; "0s"; "0s2"; "0sm"; "0sm1"]; ["0sm2"; "0sp"; "0src1"; "Cbv"; "0str"; "0tb1"; "0tg1"; "0ti"; "0tl"; "0tt"; "0vb1"; "0vk1"]]).
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].
Module PMALPA2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Lemma arm_H5a : ltac2:(TCodec.tc2 tcn__PmAParseA2 "UO&QB&Gy5'RCyR0%211%5241'8y8%611%311p061'F'6'9';%2211%411&Q0%611&O'Q7'Q;'Q:'4'QA'Q9'Q8%?11&Q@vQEv@vQGv>%544321&Q4rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%BEGFEDA@?>=<;:987654321&Q2rKrJrIrH%5BLKJGFEDCBA@?;74321&Q3rQ=rGrFrErDrC(Q6rBrAr@r?r>r=r<r;&3r:(5(Q5+5r9r8r7%544321(7%11QK%93QL31%<3QM;1%F9EDCBA@?>1r6r5r4%Q1LQNQMQLQ0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321&QF%12=BrQIrQHrQGrQFrQErQDrQCrQBrQArQ?rQ>r3r2r1%QBLR?R>R=>=<;:987654QAR:R9R8R7MLKDCB321&Q<%12ED%Q24Q1QBQAQ@%Q43RG1L%Q73RHQE1%QA9R3R2R1R0QMQLQKQJ1%621QC%H261'QC&QD&Q1%11RL&Q=+e`m0%265QCQB1Q@Q<rQL%847521p0:1p0C1pSHS>1pT2S;1pU2S=1pTLS@1p6SE1pQ<SD1pTDSL1pQHSN1pQNT41pT:SB1%A6DRERD@RCRB%F4EC1Q5p031p0Q@1p0QC1p0RF1p0RM1p0SA1pSFT01pT0SM1pU0SO1pU@T81pUDT91pUBT:1pTFSN1pUHT<1pUFT=1pU>T>1pU<T81pU6T51pSLTA1pSJTB1pT<TC1p4TB1pQ8TA1pT@TI1pQDTK1pQLU11pT8T?1pTBTM1pQFTO1pQ:TH1pT6TM1pJTN1pSNTF1pTNTH1pU:TJ1pTJTL1pSBU31pT4U41pTHU51pU4U61pSDU21p2U61pQ6U51pLU61pQ4U91pT>U?1pQBUA1pQJUG1pQ0UN1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CALL CTX G LI HLT IH.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt ti])) sm1 e1 cr1 pre (PM.PS 5 tl tt ti) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt ti])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & _).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1, HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 5 tl tt ti) SH1) as (TOK & TPOS).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
assert (TL8' : L5.u64_at RSEGS MV (T + 8) (ti + (tl - ti))) by (replace (ti + (tl - ti)) with tl by (clear; lia); exact PT8).
assert (RD : 1 <= tl - ti <= 16777216) by (clear - TOK HLT; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
assert (RI : 0 <= ti <= 16777215) by (clear - TOK HLT; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
assert (RD' : 0 <= tl - ti < 2 ^ 64) by (clear - RD; lia). assert (RI' : 0 <= ti < 2 ^ 64) by (clear - RI; lia).
cfeed P (PMALPP1.alpH5a_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 39%nat => ti | 54%nat => tl - ti | _ => 0 end)) ltac:(first [assumption | unfold PMALPP1.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & _ & _ & EW).
pose proof (PMALPK7.pstate_idx_upd MV Mav T 5 tl tt ti (ti + 1) PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZa EW) as PTa.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 5 tl tt ti) (PM.PS 5 tl tt (ti + 1)) sm1 e1 cr1 24 8
fx1 fxa R1 Ra 0xac3a0 0xaec6c Mav 0 cat CTX G LM MSa MGa FRZa ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PTa EC1).
intros Ma modela LMa FRa ECa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP1.KS_alpH5a LR0 KSa); PMALPK4.ksinc).
assert (INVa : PM.inv (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 5 tl tt (ti + 1))]))).
{ apply (PMALPK7.inv_set_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre _ _ INV1); [clear - TOK HLT; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia| cbn [PM.ps_mode]; split; intros X; exact X]. }
pose proof LRa as (X2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X3 & X4).
unfold PMA.read_key_spec, PMSPA.read_key_spec, PMSPA.run_spec in CALL.
apply (PMALPK3.alp_call_run L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xaec6c 7 _ _ fxa Ra Ma modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 5 tl tt (ti + 1))])) sm1 e1 cr1 706372
CALL CTX G LMa ltac:(clear; lia) ERA ltac:(split; [clear; lia| reflexivity]) X2 X3 X4 ltac:(split; [exact E10| split; [exact E11| exact E12]]) INVa ECa).
intros fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 RP2 POST2 LM2.
pose proof (PMALPK4.lregs_pres R Ra R2 sp _ _ F LRa RP2) as LR2.
destruct POST2 as (RPR2 & STP2 & _ & [(v & Hv & ECv & _)|(EC2 & INV2 & PK & UK)]).
- exact (PMALPK8.after_keye_5 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 v _ CTX G LR2 LM2 Hv ECv).
- pose proof (PMALPK9.unread_nonneg _ _ _ _ _ _ RPR2) as U0.
destruct s2 as [mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 stk2]. cbn [PM.p_stk] in PK. subst stk2.
apply (PMALPK8.after_key0_5 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M2' model2' LK2' Aw2 mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 pre tl tt (ti + 1) sm2 e2 cr2 CTX G LR2 LM2 EC2 INV2).
intros fx3 R3 M3 model3 LI3. apply (IH fx3 R3 M3 model3 LK2' Aw2 _ sm2 e2 cr2 LI3).
pose proof LI3 as (_ & INV3 & _). pose proof INV3 as (_ & _ & _ & SH3 & _).
exact (PMALPK9.mu_strict (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt ti])) sm1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 5 tl tt (ti + 1))])) _ sm2 SH1 SH3 U0 eq_refl UK).
Qed.
Lemma arm_H7a : ltac2:(TCodec.tc2 tcn__PmAParseA2 "UO&QB&Gy5'RCyR0%211%5241'8y8%611%311p061'F'6'9';%2211%411&Q0%611&O'Q7'Q;'Q:'4'QA'Q9'Q8%?11&Q@vQEv@vQGv>%544321&Q4rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%BEGFEDA@?>=<;:987654321&Q2rKrJrIrH%5BLKJGFEDCBA@?;74321&Q3rQ=rGrFrErDrC(Q6rBrAr@r?r>r=r<r;&3r:(5(Q5+7r9r8r7%544321(7%11QK%93QL31%<3QM;1%F9EDCBA@?>1r6r5r4%Q1LQNQMQLQ0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321&QF%12=BrQIrQHrQGrQFrQErQDrQCrQBrQArQ?rQ>r3r2r1%QBLR?R>R=>=<;:987654QAR:R9R8R7MLKDCB321&Q<%12ED%Q24Q1QBQAQ@%Q43RG1L%Q73RHQE1%QA9R3R2R1R0QMQLQKQJ1%621QC%H261'QC&QD&Q1%11RL&Q=+e`m0%265QCQB1Q@Q<rQL%847521p0:1p0C1pSHS>1pT2S;1pU2S=1pTLS@1p6SE1pQ<SD1pTDSL1pQHSN1pQNT41pT:SB1%A6DRERD@RCRB%F4EC1Q5p031p0Q@1p0QC1p0RF1p0RM1p0SA1pSFT01pT0SM1pU0SO1pU@T81pUDT91pUBT:1pTFSN1pUHT<1pUFT=1pU>T>1pU<T81pU6T51pSLTA1pSJTB1pT<TC1p4TB1pQ8TA1pT@TI1pQDTK1pQLU11pT8T?1pTBTM1pQFTO1pQ:TH1pT6TM1pJTN1pSNTF1pTNTH1pU:TJ1pTJTL1pSBU31pT4U41pTHU51pU4U61pSDU21p2U61pQ6U51pLU61pQ4U91pT>U?1pQBUA1pQJUG1pQ0UN1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CALL CTX G LI HLT IH.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt ti])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt ti])) sm1 e1 cr1 pre (PM.PS 7 tl tt ti) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt ti])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & _).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1, HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 7 tl tt ti) SH1) as (TOK & TPOS).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
assert (TL8' : L5.u64_at RSEGS MV (T + 8) (ti + (tl - ti))) by (replace (ti + (tl - ti)) with tl by (clear; lia); exact PT8).
assert (RD : 1 <= tl - ti <= 16777216) by (clear - TOK HLT; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
assert (RI : 0 <= ti <= 16777215) by (clear - TOK HLT; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
assert (RD' : 0 <= tl - ti < 2 ^ 64) by (clear - RD; lia). assert (RI' : 0 <= ti < 2 ^ 64) by (clear - RI; lia).
cfeed P (PMALPP2.alpH7a_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 39%nat => ti | 54%nat => tl - ti | _ => 0 end)) ltac:(first [assumption | unfold PMALPP2.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & _ & _ & EW).
pose proof (PMALPK7.pstate_idx_upd MV Mav T 7 tl tt ti (ti + 1) PTv ltac:(clear - TR; lia) ltac:(clear - TR; lia) FRZa EW) as PTa.
apply (PMALPK4.top_run L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre (PM.PS 7 tl tt ti) (PM.PS 7 tl tt (ti + 1)) sm1 e1 cr1 24 8
fx1 fxa R1 Ra 0xac3a0 0xaec6c Mav 0 cat CTX G LM MSa MGa FRZa ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) PTa EC1).
intros Ma modela LMa FRa ECa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP2.KS_alpH7a LR0 KSa); PMALPK4.ksinc).
assert (INVa : PM.inv (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 7 tl tt (ti + 1))]))).
{ apply (PMALPK7.inv_set_top mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre _ _ INV1); [clear - TOK HLT; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in *; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in *; lia| cbn [PM.ps_mode]; split; intros X; exact X]. }
pose proof LRa as (X2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X3 & X4).
unfold PMA.read_key_spec, PMSPA.read_key_spec, PMSPA.run_spec in CALL.
apply (PMALPK3.alp_call_run L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xaec6c 7 _ _ fxa Ra Ma modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 7 tl tt (ti + 1))])) sm1 e1 cr1 706064
CALL CTX G LMa ltac:(clear; lia) ERA ltac:(split; [clear; lia| reflexivity]) X2 X3 X4 ltac:(split; [exact E10| split; [exact E11| exact E12]]) INVa ECa).
intros fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 RP2 POST2 LM2.
pose proof (PMALPK4.lregs_pres R Ra R2 sp _ _ F LRa RP2) as LR2.
destruct POST2 as (RPR2 & STP2 & _ & [(v & Hv & ECv & _)|(EC2 & INV2 & PK & UK)]).
- exact (PMALPK8.after_keye_7 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M2' model2' LK2' Aw2 s2 sm2 e2 cr2 v _ CTX G LR2 LM2 Hv ECv).
- pose proof (PMALPK9.unread_nonneg _ _ _ _ _ _ RPR2) as U0.
destruct s2 as [mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 stk2]. cbn [PM.p_stk] in PK. subst stk2.
apply (PMALPK8.after_key0_7 L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx2 R2 M2' model2' LK2' Aw2 mo2 dn2 dp2 src2 tb2 tg2 vb2 vk2 pre tl tt (ti + 1) sm2 e2 cr2 CTX G LR2 LM2 EC2 INV2).
intros fx3 R3 M3 model3 LI3. apply (IH fx3 R3 M3 model3 LK2' Aw2 _ sm2 e2 cr2 LI3).
pose proof LI3 as (_ & INV3 & _). pose proof INV3 as (_ & _ & _ & SH3 & _).
exact (PMALPK9.mu_strict (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt ti])) sm1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [(PM.PS 7 tl tt (ti + 1))])) _ sm2 SH1 SH3 U0 eq_refl UK).
Qed.
Lemma arm_H2b : ltac2:(TCodec.tc2 tcn__PmAParseA2 "V0&QB&Gy5'RCyR0%211%5241'8y8%611%311p061'F'6'9';%2211%411&Q0%611&O'Q7'Q;'Q:'4'QA'Q9'Q8%?11&Q>vQEv@vQGv>%544321&Q4rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%BEGFEDA@?>=<;:987654321&Q2rKrJrIrH%5BLKJGFEDCBA@?;74321&Q3rQ=rGrFrErDrC(Q6rBrAr@r?r>r=r<r;&3r:(5(Q5+2r9r8r7%544321(7%11QK%93QL31%<3QM;1%F9EDCBA@?>1r6r5r4%Q1LQNQMQLQ0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321':%13R@=BrQIrQHrQGrQFrQErQDrQCrQBrQArQ?rQ>r3r2r1%QBLR?R>R=>=<;:987654QAR:R9R8R7MLKDCB321&QF&Q<%12FE%Q34Q2QCQBQA%Q53RH1M%Q83RIQF1%QB9R4R3R2R1QNQMQLQK1%621QD%8261'QC&QD&Q1%11RM&Q=+e`m0%265QDQC1QAQ=rQL%847521p0:1p0D1pSHS?1pT2S<1pU2S>1pTLSA1p6SF1pQ<SE1pTDSM1pQHSO1pQNT51pT:SC1%A6DRFRE@RDRC%F4EC1Q6p031p0QA1p0QD1p0RG1p0RN1p0SB1pSFT11pT0SN1pU0T01pU@T91pUDT:1pUBT;1pTFSO1pUHT=1pUFT>1pU>T?1pU<T91pU6T61pSLTB1pSJTC1pT<TD1p4TC1pQ8TB1pT@TJ1pQDTL1pQLU21pT8T@1pTBTN1pQFU01pQ:TI1pT6TN1pJTO1pSNTG1pTNTI1pU:TK1pTJTM1pSBU41pT4U51pTHU61pU4U71pSDU31p2U71pQ6U61pLU71pQ4U:1pT>U@1pQBUB1pQJUH1pQ0UO1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CALL CTX G LI HEQ IH. subst ti.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 2 tl tt tl])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 2 tl tt tl])) sm1 e1 cr1 pre (PM.PS 2 tl tt tl) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 2 tl tt tl])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & _).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1, HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 2 tl tt tl) SH1) as (TOK & TPOS).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
assert (RI : 0 <= tl <= 16777216) by (clear - TOK; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
assert (RI' : 0 <= tl < 2 ^ 64) by (clear - RI; lia).
cfeed P (PMALPP1.alpH2b_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 39%nat => tl | _ => 0 end)) ltac:(first [assumption | unfold PMALPP1.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & _).
apply (PMALPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 2 tl tt tl])) sm1 e1 cr1 fx1 fxa R1 Ra 0xac3a0 0xad424 Mav K G LM MSa FRZa).
intros modela LMa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP1.KS_alpH2b LR0 KSa); PMALPK4.ksinc).
assert (NB : ~ PM.mode_bottom 2) by (unfold PM.mode_bottom; clear; lia).
assert (L2 : (2 <= length (pre ++ [PM.PS 2 tl tt tl]))%nat).
{ destruct TPOS as [(_ & X)|(X & _)]; [exfalso; exact (NB X)|]. destruct pre as [|p0 pre0]; [exfalso; apply X; reflexivity|]. cbn [length app]. rewrite length_app. cbn [length]. clear; lia. }
unfold PMA.end_array_spec, PMSPA.end_array_spec, PMSPA.run_spec in CALL.
apply (PMALPK9.vcall_e L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xad424 1 706140 _ _ fxa Ra M1 modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 2 tl tt tl])) sm1 e1 cr1
(fun s2 sm2 => PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 2 tl tt tl])) sm1) CALL CTX G LMa ltac:(clear; lia) LRa ERA ltac:(split; [clear; lia| reflexivity])).
- split; [split; [exact E10| split; [exact E11| exact E12]]| exact L2].
- exact INV1.
- exact EC1.
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LR3 LM3 JP3.
exact (PMALPK6.after_end_N L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 CTX G LR3 LM3 JP3).
- intros R2 s2 sm2 INV2 ((top0 & Etop) & UE) U0 STP. cbn [PM.p_stk] in Etop.
assert (T0 : top0 = PM.PS 2 tl tt tl) by (symmetry in Etop; apply app_inj_tail in Etop; destruct Etop as (_ & X); exact X). subst top0.
apply (PMPK2.lp_mu_pop (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 2 tl tt tl])) sm1 s2 sm2 (PM.PS 2 tl tt tl)); [exact Etop| unfold PMPK2.lp_w; cbn; clear; lia| rewrite UE; clear; lia].
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3. exact (IH fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3).
Qed.
Lemma arm_H4b : ltac2:(TCodec.tc2 tcn__PmAParseA2 "V0&QB&Gy5'RCyR0%211%5241'8y8%611%311p061'F'6'9';%2211%411&Q0%611&O'Q7'Q;'Q:'4'QA'Q9'Q8%?11&Q>vQEv@vQGv>%544321&Q4rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%BEGFEDA@?>=<;:987654321&Q2rKrJrIrH%5BLKJGFEDCBA@?;74321&Q3rQ=rGrFrErDrC(Q6rBrAr@r?r>r=r<r;&3r:(5(Q5+4r9r8r7%544321(7%11QK%93QL31%<3QM;1%F9EDCBA@?>1r6r5r4%Q1LQNQMQLQ0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321':%13R@=BrQIrQHrQGrQFrQErQDrQCrQBrQArQ?rQ>r3r2r1%QBLR?R>R=>=<;:987654QAR:R9R8R7MLKDCB321&QF&Q<%12FE%Q34Q2QCQBQA%Q53RH1M%Q83RIQF1%QB9R4R3R2R1QNQMQLQK1%621QD%8261'QC&QD&Q1%11RM&Q=+e`m0%265QDQC1QAQ=rQL%847521p0:1p0D1pSHS?1pT2S<1pU2S>1pTLSA1p6SF1pQ<SE1pTDSM1pQHSO1pQNT51pT:SC1%A6DRFRE@RDRC%F4EC1Q6p031p0QA1p0QD1p0RG1p0RN1p0SB1pSFT11pT0SN1pU0T01pU@T91pUDT:1pUBT;1pTFSO1pUHT=1pUFT>1pU>T?1pU<T91pU6T61pSLTB1pSJTC1pT<TD1p4TC1pQ8TB1pT@TJ1pQDTL1pQLU21pT8T@1pTBTN1pQFU01pQ:TI1pT6TN1pJTO1pSNTG1pTNTI1pU:TK1pTJTM1pSBU41pT4U51pTHU61pU4U71pSDU31p2U71pQ6U61pLU71pQ4U:1pT>U@1pQBUB1pQJUH1pQ0UO1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CALL CTX G LI HEQ IH. subst ti.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 4 tl tt tl])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 4 tl tt tl])) sm1 e1 cr1 pre (PM.PS 4 tl tt tl) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 4 tl tt tl])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & _).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1, HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 4 tl tt tl) SH1) as (TOK & TPOS).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
assert (RI : 0 <= tl <= 16777216) by (clear - TOK; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
assert (RI' : 0 <= tl < 2 ^ 64) by (clear - RI; lia).
cfeed P (PMALPP1.alpH4b_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 39%nat => tl | _ => 0 end)) ltac:(first [assumption | unfold PMALPP1.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & _).
apply (PMALPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 4 tl tt tl])) sm1 e1 cr1 fx1 fxa R1 Ra 0xac3a0 0xad424 Mav K G LM MSa FRZa).
intros modela LMa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP1.KS_alpH4b LR0 KSa); PMALPK4.ksinc).
assert (NB : ~ PM.mode_bottom 4) by (unfold PM.mode_bottom; clear; lia).
assert (L2 : (2 <= length (pre ++ [PM.PS 4 tl tt tl]))%nat).
{ destruct TPOS as [(_ & X)|(X & _)]; [exfalso; exact (NB X)|]. destruct pre as [|p0 pre0]; [exfalso; apply X; reflexivity|]. cbn [length app]. rewrite length_app. cbn [length]. clear; lia. }
unfold PMA.end_array_spec, PMSPA.end_array_spec, PMSPA.run_spec in CALL.
apply (PMALPK9.vcall_e L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xad424 1 706140 _ _ fxa Ra M1 modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 4 tl tt tl])) sm1 e1 cr1
(fun s2 sm2 => PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 4 tl tt tl])) sm1) CALL CTX G LMa ltac:(clear; lia) LRa ERA ltac:(split; [clear; lia| reflexivity])).
- split; [split; [exact E10| split; [exact E11| exact E12]]| exact L2].
- exact INV1.
- exact EC1.
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LR3 LM3 JP3.
exact (PMALPK6.after_end_N L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 CTX G LR3 LM3 JP3).
- intros R2 s2 sm2 INV2 ((top0 & Etop) & UE) U0 STP. cbn [PM.p_stk] in Etop.
assert (T0 : top0 = PM.PS 4 tl tt tl) by (symmetry in Etop; apply app_inj_tail in Etop; destruct Etop as (_ & X); exact X). subst top0.
apply (PMPK2.lp_mu_pop (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 4 tl tt tl])) sm1 s2 sm2 (PM.PS 4 tl tt tl)); [exact Etop| unfold PMPK2.lp_w; cbn; clear; lia| rewrite UE; clear; lia].
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3. exact (IH fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3).
Qed.
Lemma arm_H5b : ltac2:(TCodec.tc2 tcn__PmAParseA2 "V0&QB&Gy5'RCyR0%211%5241'8y8%611%311p061'F'6'9';%2211%411&Q0%611&O'Q7'Q;'Q:'4'QA'Q9'Q8%?11&Q?vQEv@vQGv>%544321&Q4rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%BEGFEDA@?>=<;:987654321&Q2rKrJrIrH%5BLKJGFEDCBA@?;74321&Q3rQ=rGrFrErDrC(Q6rBrAr@r?r>r=r<r;&3r:(5(Q5+5r9r8r7%544321(7%11QK%93QL31%<3QM;1%F9EDCBA@?>1r6r5r4%Q1LQNQMQLQ0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321':%13R@=BrQIrQHrQGrQFrQErQDrQCrQBrQArQ?rQ>r3r2r1%QBLR?R>R=>=<;:987654QAR:R9R8R7MLKDCB321&QF&Q<%12FE%Q34Q2QCQBQA%Q53RH1M%Q83RIQF1%QB9R4R3R2R1QNQMQLQK1%621QD%8261'QC&QD&Q1%11RM&Q=+e`m0%265QDQC1QAQ=rQL%847521p0:1p0D1pSHS?1pT2S<1pU2S>1pTLSA1p6SF1pQ<SE1pTDSM1pQHSO1pQNT51pT:SC1%A6DRFRE@RDRC%F4EC1Q6p031p0QA1p0QD1p0RG1p0RN1p0SB1pSFT11pT0SN1pU0T01pU@T91pUDT:1pUBT;1pTFSO1pUHT=1pUFT>1pU>T?1pU<T91pU6T61pSLTB1pSJTC1pT<TD1p4TC1pQ8TB1pT@TJ1pQDTL1pQLU21pT8T@1pTBTN1pQFU01pQ:TI1pT6TN1pJTO1pSNTG1pTNTI1pU:TK1pTJTM1pSBU41pT4U51pTHU61pU4U71pSDU31p2U71pQ6U61pLU71pQ4U:1pT>U@1pQBUB1pQJUH1pQ0UO1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CALL CTX G LI HEQ IH. subst ti.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt tl])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt tl])) sm1 e1 cr1 pre (PM.PS 5 tl tt tl) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt tl])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & _).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1, HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 5 tl tt tl) SH1) as (TOK & TPOS).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
assert (RI : 0 <= tl <= 16777216) by (clear - TOK; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
assert (RI' : 0 <= tl < 2 ^ 64) by (clear - RI; lia).
cfeed P (PMALPP1.alpH5b_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 39%nat => tl | _ => 0 end)) ltac:(first [assumption | unfold PMALPP1.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & _).
apply (PMALPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt tl])) sm1 e1 cr1 fx1 fxa R1 Ra 0xac3a0 0xaefb0 Mav K G LM MSa FRZa).
intros modela LMa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP1.KS_alpH5b LR0 KSa); PMALPK4.ksinc).
assert (NB : ~ PM.mode_bottom 5) by (unfold PM.mode_bottom; clear; lia).
assert (L2 : (2 <= length (pre ++ [PM.PS 5 tl tt tl]))%nat).
{ destruct TPOS as [(_ & X)|(X & _)]; [exfalso; exact (NB X)|]. destruct pre as [|p0 pre0]; [exfalso; apply X; reflexivity|]. cbn [length app]. rewrite length_app. cbn [length]. clear; lia. }
unfold PMA.end_object_spec, PMSPA.end_object_spec, PMSPA.run_spec in CALL.
apply (PMALPK9.vcall_e L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xaefb0 1 706640 _ _ fxa Ra M1 modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt tl])) sm1 e1 cr1
(fun s2 sm2 => PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt tl])) sm1) CALL CTX G LMa ltac:(clear; lia) LRa ERA ltac:(split; [clear; lia| reflexivity])).
- split; [split; [exact E10| split; [exact E11| exact E12]]| exact L2].
- exact INV1.
- exact EC1.
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LR3 LM3 JP3.
exact (PMALPK6.after_end_M L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 CTX G LR3 LM3 JP3).
- intros R2 s2 sm2 INV2 ((top0 & Etop) & UE) U0 STP. cbn [PM.p_stk] in Etop.
assert (T0 : top0 = PM.PS 5 tl tt tl) by (symmetry in Etop; apply app_inj_tail in Etop; destruct Etop as (_ & X); exact X). subst top0.
apply (PMPK2.lp_mu_pop (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 5 tl tt tl])) sm1 s2 sm2 (PM.PS 5 tl tt tl)); [exact Etop| unfold PMPK2.lp_w; cbn; clear; lia| rewrite UE; clear; lia].
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3. exact (IH fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3).
Qed.
Lemma arm_H7b : ltac2:(TCodec.tc2 tcn__PmAParseA2 "V0&QB&Gy5'RCyR0%211%5241'8y8%611%311p061'F'6'9';%2211%411&Q0%611&O'Q7'Q;'Q:'4'QA'Q9'Q8%?11&Q?vQEv@vQGv>%544321&Q4rQ<rQ;rQ:rQ9rQ8rQ7rQ6rQ5rQ4rQ3rQ2rQ1rQ0rOrNrMrL%BEGFEDA@?>=<;:987654321&Q2rKrJrIrH%5BLKJGFEDCBA@?;74321&Q3rQ=rGrFrErDrC(Q6rBrAr@r?r>r=r<r;&3r:(5(Q5+7r9r8r7%544321(7%11QK%93QL31%<3QM;1%F9EDCBA@?>1r6r5r4%Q1LQNQMQLQ0QIQHQGQFQEQDQCQBQ@Q?Q>Q=Q<Q;Q:ONMLK4321':%13R@=BrQIrQHrQGrQFrQErQDrQCrQBrQArQ?rQ>r3r2r1%QBLR?R>R=>=<;:987654QAR:R9R8R7MLKDCB321&QF&Q<%12FE%Q34Q2QCQBQA%Q53RH1M%Q83RIQF1%QB9R4R3R2R1QNQMQLQK1%621QD%8261'QC&QD&Q1%11RM&Q=+e`m0%265QDQC1QAQ=rQL%847521p0:1p0D1pSHS?1pT2S<1pU2S>1pTLSA1p6SF1pQ<SE1pTDSM1pQHSO1pQNT51pT:SC1%A6DRFRE@RDRC%F4EC1Q6p031p0QA1p0QD1p0RG1p0RN1p0SB1pSFT11pT0SN1pU0T01pU@T91pUDT:1pUBT;1pTFSO1pUHT=1pUFT>1pU>T?1pU<T91pU6T61pSLTB1pSJTC1pT<TD1p4TC1pQ8TB1pT@TJ1pQDTL1pQLU21pT8T@1pTBTN1pQFU01pQ:TI1pT6TN1pJTO1pSNTG1pTNTI1pU:TK1pTJTM1pSBU41pT4U51pTHU61pU4U71pSDU31p2U71pQ6U61pLU71pQ4U:1pT>U@1pQBUB1pQJUH1pQ0UO1").
Proof. intros K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx1 R1 M1 model1 LK1 Aw1 mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 pre tl tt ti sm1 e1 cr1.
intros CALL CTX G LI HEQ IH. subst ti.
destruct LI as (LR & INV1 & EC1 & LM).
pose proof LR as LR0.
pose proof (PMALPK.lfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt tl])) sm1 e1 cr1 0 cat CTX G LM EC1) as LF.
pose proof (PMALPK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt tl])) sm1 e1 cr1 pre (PM.PS 7 tl tt tl) CTX G LM eq_refl) as (TF & PTv & PT1).
cbn [PM.p_b] in TF, PTv, PT1.
pose proof (PMALPK4.hfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt tl])) sm1 e1 cr1 CTX G LM) as (HM8 & HD9 & _).
pose proof INV1 as (IM1 & ID1 & _ & SH1 & _). cbn [PM.p_more PM.p_done PM.p_stk] in IM1, ID1, SH1, HM8, HD9. rewrite IM1 in HM8. rewrite ID1 in HD9.
destruct (PMPK2.top_of_shape pre (PM.PS 7 tl tt tl) SH1) as (TOK & TPOS).
set (T := vb1 + 32 * Z.of_nat (length pre)) in *.
set (op := PMSPA.o_p PMA.AD fb) in *. set (ov := PMSPA.o_v PMA.AD fb) in *. set (oec := PMSPA.o_ec PMA.AD fb) in *.
set (MV := mrestrict (ahid Aw1 model1) M1) in *.
pose proof PTv as (PT0 & PT8 & PT16 & PT24). cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx] in PT0, PT8, PT16, PT24.
PMALPK5.lf_open LF. PMALPK5.lr_open LR.
unfold PMALPK.tfacts in TF. destruct TF as (TLO & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & T64).
assert (TR : 0 <= T /\ T + 32 <= 2 ^ 64) by (clear - T64 TLO; lia).
assert (RI : 0 <= tl <= 16777216) by (clear - TOK; unfold PM.pstate_ok, PM.mode_counted, PM.mode_indef, PM.mode_bottom, PM.MAX_ITEMS in TOK; cbn [PM.ps_mode PM.ps_len PM.ps_idx PM.ps_type] in TOK; lia).
assert (RI' : 0 <= tl < 2 ^ 64) by (clear - RI; lia).
cfeed P (PMALPP2.alpH7b_conc fx1 R1 MV (fun j => match j with 2%nat => sp | 34%nat => T | 36%nat => op | 37%nat => ov | 38%nat => oec | 47%nat => F | 48%nat => fl | 39%nat => tl | _ => 0 end)) ltac:(first [assumption | unfold PMALPP2.aligned; assumption]).
destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & ERA & E10 & E11 & E12 & _).
apply (PMALPK4.ro_run L ar C HI LY HIok R M model LBX FF LK Aw cr sp fb s str sm e F fl LK2 M2 model2 M1 model1 LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt tl])) sm1 e1 cr1 fx1 fxa R1 Ra 0xac3a0 0xaefb0 Mav K G LM MSa FRZa).
intros modela LMa.
assert (LRa : PMALPD.lregs R Ra sp op oec F) by (apply (PMALPK4.lregs_ks R R1 Ra sp op oec F PMALPP2.KS_alpH7b LR0 KSa); PMALPK4.ksinc).
assert (NB : ~ PM.mode_bottom 7) by (unfold PM.mode_bottom; clear; lia).
assert (L2 : (2 <= length (pre ++ [PM.PS 7 tl tt tl]))%nat).
{ destruct TPOS as [(_ & X)|(X & _)]; [exfalso; exact (NB X)|]. destruct pre as [|p0 pre0]; [exfalso; apply X; reflexivity|]. cbn [length app]. rewrite length_app. cbn [length]. clear; lia. }
unfold PMA.end_object_spec, PMSPA.end_object_spec, PMSPA.run_spec in CALL.
apply (PMALPK9.vcall_e L ar C HI HIok K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 0xaefb0 1 706640 _ _ fxa Ra M1 modela LK1 Aw1 (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt tl])) sm1 e1 cr1
(fun s2 sm2 => PMPK2.lp_mu s2 sm2 < PMPK2.lp_mu (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt tl])) sm1) CALL CTX G LMa ltac:(clear; lia) LRa ERA ltac:(split; [clear; lia| reflexivity])).
- split; [split; [exact E10| split; [exact E11| exact E12]]| exact L2].
- exact INV1.
- exact EC1.
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LR3 LM3 JP3.
exact (PMALPK6.after_end_M L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat s str sm e F fl LK2 M2 model2 fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 CTX G LR3 LM3 JP3).
- intros R2 s2 sm2 INV2 ((top0 & Etop) & UE) U0 STP. cbn [PM.p_stk] in Etop.
assert (T0 : top0 = PM.PS 7 tl tt tl) by (symmetry in Etop; apply app_inj_tail in Etop; destruct Etop as (_ & X); exact X). subst top0.
apply (PMPK2.lp_mu_pop (PM.PST mo1 dn1 dp1 src1 tb1 tg1 vb1 vk1 (pre ++ [PM.PS 7 tl tt tl])) sm1 s2 sm2 (PM.PS 7 tl tt tl)); [exact Etop| unfold PMPK2.lp_w; cbn; clear; lia| rewrite UE; clear; lia].
- intros fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3. exact (IH fx3 R3 M3 model3 LK3 Aw3 s3 sm3 e3 cr3 LI3 Q3).
Qed.
End WithHeap.
End PMALPA2.
