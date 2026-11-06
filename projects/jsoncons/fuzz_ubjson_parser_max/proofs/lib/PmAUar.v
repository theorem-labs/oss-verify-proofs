(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmLayout PmLayoutA PmModel PmSpecsA PmSpecsAa PmAUarK.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAUar () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAUar.PMAUAR.SCFG_1.WithIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAUarK.PMAUK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepAR.L5SAR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["0A"; "0A6"; "0BX0"; "1app"; "1cons"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2not"; "2or"; "3map"]; ["4Z"; "0E"; "0F"; "0FF"; "0HI"; "0K"; "0L"; "0LB"; "0LB6"; "0LK"; "0LK2"; "0LK6"; "5Model"; "5event"; "6bvmap"; "0M"]; ["0M'"; "0M1"; "0M1'"; "0M2"; "0Mf"; "0Mx"; "0R1"; "0R2"; "7mrestrict"; "8credit"; "8regs_preserved"; "9SB"; "9aclient"; "9ahid"; "9ar_sptop"; "9ff_addr"]; ["9ff_bytes"; "9ff_room"; "9ff_rs"; "9fframe"; "9hl_tp"; "9model_rt"; "9ri_inv"; "9vml"; "9vml_of"; ";defined"; ";frame_but"; ";outside"; ";range"; ";u64_at"; ";writable"; ":SCFG"]; ["<avis"; "<cfg"; "=zeros_at"; ">Wfr"; "?WretX"; "?gctx"; "@aobjA"; "@ffroomA"; "@ffrsA"; "@frame_okA"; "ASM_PC"; "BFPState"; "Bgetr"; "CTSet"; "Dsrealizes"; "Emem_grows"]; ["Fahpres"; "Famodel_ok"; "Fastk"; "Gdk"; "Gek"; "Hloaded_segments"; "0SCFG_P"; "0SCR"; "IIn"; "Iincl"; "Jadd"; "Jdiv"; "Jle"; "Jlt"; "Jmodulo"; "Jpow"]; ["Jsub"; "0V"; "0V6"; "0W"; "0Wx"; "0a"; "0ar"; "0cr"; "0cr2"; "0cr6"; "0f"; "0fb"; "0fl"; "0fx"; "0h"; "0h'"]; ["0i"; "0k"; "0model"; "0model1"; "0model2"; "0n"; "0o"; "0ocell"; "0ohi"; "0olo"; "0own"; "0rr"; "0rs"; "0scr"; "0scr0"; "0sp"]; ["0sp'"; "0sp0"; "0spc"; "KNoDup"; "LBV"; "LZ_to_bv"; "Lbv"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Module PMAUAR.
Import L5A. Import L5CA. Import L5SAR.
Abbreviation RSEGS := Asan.M.loaded_segments.
Lemma ffroomA_push : ltac2:(TCodec.tc2 tcn__PmAUar "Q8'@'5&QC%211&R7r6r4r3%43321&RI%13834'T3&?&Q?&3(4%13>9;%33?1;%64@B51%82C1&RL&RJr8+1%3221r9%6221r5%=3J16%I341Hp041p0<1p0F1p0I1pVFQ01pQFQ01pQDQ11pQ8Q21pW0Q61pVNQ71").
Proof. intros h h' FF LK LK2 f.
intros FR INC ND Hh k Hk. specialize (FR k Hk). rewrite ff_count_app in FR. rewrite ff_count_app.
pose proof (ff_count_cons k f FF) as C1.
pose proof (ff_count_incl k LK2 LK INC (nodup_of_map_app_r (f :: FF) LK2 ND)) as C2. lia.
Qed.
Lemma ffrsA_push : ltac2:(TCodec.tc2 tcn__PmAUar "Q4'5&QC%211'@&R8r6r5%3221&RL&RJ+Q0%2251r2%5221r7%72:1(4'9%12??%221@(8%14BB@?r4%345D21r9%93621%F21<p0<1p0?1p0F1pWJK1pW4L1pQ6M1pX2N1pX0O1pQ8Q11").
Proof. intros FF sp sp' F k rs. intros H1 H2 H3 f [<-|Hf]; [cbn; lia| specialize (H1 f Hf); lia]. Qed.
Lemma frame_okA_push : ltac2:(TCodec.tc2 tcn__PmAUar "J'5&QC%211'@&R9r5r4%3221(4'9%1277%2218(8r3%24;;81r2%446=21r6%:3721%?21>p0=1pWJB1pW4C1pQ6D1pVHE1pQ8G1").
Proof. intros FF fb F k rs. intros ((r0 & Hf) & Hm). split; [exists r0; right; exact Hf| exact Hm]. Qed.
Lemma aobjA_push : ltac2:(TCodec.tc2 tcn__PmAUar "B'5&QC%211'@&R6r4r3r2%43321(4r5%23:41%83176p051pVF=1pW<<1pW>=1pQ8?1").
Proof. intros FF o n f. intros (g & Hg & X). exists g. split; [right; exact Hg| exact X]. Qed.
Lemma ff_room_of : ltac2:(TCodec.tc2 tcn__PmAUar "Q5'@'5&QC%211&R7r4r3r2%43321&RLzr5%3221&RH(4+1+2+3+4(6%11D%73E31%83F51%93G71%:3H91%;3I?1%=3JD1&QAr6%23H1Bp041p0C1p0H1pW4Q11pQDO1pQ8Q01pVNQ41").
Proof. intros h FF LK k. intros FR Hh Hk. specialize (FR k Hk). unfold ff_room. lia. Qed.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Lemma uar_sm : ltac2:(TCodec.tc2 tcn__PmAUar "\G'@'5'9%1233%311&QC%511&Q9!p091'T6yR0%211'7y8%511%311p051p01:'R;&Ny5%221:'L&R=&RHrF(4z+1+2+3+4(6%11Q2%83Q331%93Q451%:3Q571%;3Q691%<3Q7;1%?3Q8>1&QFvD&3rE%23Q:1CrDrCrBrAr7&QHr5%211%=8<9876541rG%=3QEN1%@8?1=;:974&RAr6%22=1'M%M11%411&RBvS6r;%3421ED&R?r<%2214&RDvFrLrJ&QL%Q;11r=%796=54QDQ2219&RCrMrKr>%48;B32LQI16'<&R<r@(T4(:%23R4QK1%5241&T5%12RAR2%93RA31%73R9QN6%:2Q>1&QD%11I%72RG1%?3RG41%=3R?R7<%@2QE1%;2RKQ1%C3RK21&RN%12LR;%F3S:1R>';&RL%12RAK&RM&RO+R0%22RC1%42Q01%8261+@%=2Q41%Q23SF1RJ&RJ&S0rN%221Q:+`0%5221%A21QD%B2Q>QErQ1%D2Q@1r1%911r2%H251rQ0%H231%L231p061pV<T91pX@SNSJrO%119rQ2%11=r4%QE2T5=%211%RN12%QO3T321p061pV<TE1r3%H11p031p0=1pR6@1pR4T:1&QArQ;rQ8rQ7%43321rQ:%T93TMQ11+Q0%Q=251&QB%11Q3%QK231p061pVFU41'R5rQBrQ@rQ?rQ=rQ<rQ9rQ6rQCrQ>rQA%;FS=SDT;:9876HD5GF4OQB3QDT1Q621+:%S03U21RO%S32T61%RN2U>Q:%S63U>21&Q:r8%22<1%T42BT<&QErQ4%2215r:%T34T21?GrQHrQF%SO9SNT521KBSJFT4rQIrQG%SJ8T1T821GNQ8T4rQJ%U03V841rQD%T69T5T<291KT1Q<T0rQK%U43V<51rQE%T28T9T@2:15QDSO%S622RA%S52RB;%S9221%U41R5%Q31R6%T33V721p041pV<VI1&QN&RE&Q8&Q=r?%22K1%421T:&Q@rQN%211%:494TB1%82NT?%:21UE&RK+8%22;1&Q;%SD221rQO%<11%7216%E4D941&R2%D2Q7V0%F21V2%<2TM;%SM21:rR0%E11%@21?%83641&QM%M2Q<V:%O21V<rR1%L11%T72V=1%T721G%74Q551U:rQL%Q521VC%Q721VE%Q:4Q91VCW7&QIrQM%Q:21VI%Q<21VLrR3%Q911%633VL1&R0%Q@2Q;W1rR4%Q>11%433W21%QD2Q5WG%Q;2W6Q:%TL21Q9rR5%QD11%Q?21Q>%;3641%QK2Q3W1%=31W=WL%U>2WNTI%U=2TJT<%UA221&Q<rR;rR<%WE3XM21rR:%U;2W7TO%67VKW232TDT=1p081pW2Y51%UH2X:TG'>%UA2W=WD%UM21VIrR=%R:11%UE2VL1%V121WB%7251%R82VOR7%UI21R6%V5291%R;27R:%UL231%V821WI%>241%V:2>W=%V02W>XJ%V<21WM%B231%V?251%V@2=1p0F1p0H1pWNYN1pX4YO1pW<Z01pV<Z11'R>&QOvRF%211&R1rI%25SNWGTFWN1%74S>41SMp091p0QB1p0QE1p0QM1p0R31p0R;1p0R@1p0RI1p0S31p0S?1p0SK1p0T41p0T91p0T>1p0TB1p0TF1p0TI1p0TM1p0TO1p0U31p0U91pQFZI1pVJ[01pQ6[11pW:Z;1pR8ZB1pR@Z>1&R:%11UC%Q15W2VL1XGXF%Q64T=Q31XNp051p0V11p0V;1p0VA1p0W41p0W>1p0WA1p0WB1p0WD1p0WL1p0X01p0X:1p0X>1p0XC1p0XJ1p0Y51p0Y;1p0YD1p0YH1p0YM1p0Z11p0Z51p0Z91p0ZH1pWH\11pQ<[:1pW8[<1pW6[=1pR4[D1pR0[E1pR>[A1pVL[E1pWF[G1pW@\11pWB\;1pWD\<1pX6\=1pU@\>1pQ4\?1p2\<1pV@\:1pQD\<1pQ8\=1p6\@1pQ@\A1pW4\F1").
Proof. intros k LB BX0 FF LK cr A E SCR spc olo ohi ocell own fx R1 M M1 model model1 K rr.
intros Hk HH HH1 AM1 K0 ASTK MG01 EK01 DK01 G2 G4 G1 RR0 RR1 SP16 SPSC SPO1 SPO2 SPO3 OCR OWNAG FFRk FFRS KONT.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (HAJ.aior_stack_malloc _ _ _ _ _ HIok k Hk) as SM. unfold astack_malloc_spec in SM.
rewrite (aly_segs L C LYa), (PMA.ly_sm L C LY k Hk), (aly_scr_sm L C LYa) in SM.
assert (U2 : bv_unsigned (getr R1 2%bv) = spc) by (rewrite G2; apply L5.unsigned_lit; clear - SPSC SPO1 SPO2 SPO3 SHI SPT SLO; lia).
eapply (SM fx R1 M1 model1 (BX0 ++ LB) FF LK cr A K HH1 (proj1 AM1) (proj2 AM1)); clear SM.
- exact G4.
- rewrite G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by exact RR1. exact RR0.
- rewrite U2. replace spc with (E - (E - spc)) by (clear; lia).
apply (astack_ok_of_astk L ar C LYa M M1 E SCR (E - spc) 512 ASTK MG01); [clear - SPO1 SPO2 SPO3; lia| clear; lia| clear - SPSC; lia|].
replace (E - (E - spc)) with spc by (clear; lia). exact SP16.
- exact FFRk.
- intros f Hf. rewrite U2. specialize (FFRS f Hf). clear - FFRS SPO1 SPO2 SPO3. lia.
- exact K0.
- intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI2 FDEF FLC FLP FLNC FLA FLW FSH PRES2 RT2 MI2 HH2.
rewrite U2 in FLNC, PRES2, HH2. rewrite G1.
pose proof (sm_facts L ar C HI LYa HIok (BX0 ++ LB) FF LK2 cr A M2 model2 F k (spc + 32) fl HH2 Hk FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH)
as (FR & FFL & F32 & F8 & B64 & FDEFv & FWv & FBIG & FSHW & FSHZ & FLCv & FLR & FLWv & FLBIG & VF & VSH & VFL).
assert (Hh2 : m_halted model2 = None) by (rewrite (L5LZ.model_rt_halted _ _ RT2); exact (proj1 AM1)).
assert (ASTK2 : astk ar M2 E SCR).
{ apply (astk_after_rt L ar C HI HIok (BX0 ++ LB) FF LK cr A M M1 M2 _ E SCR spc 512 HH ASTK MG01 PRES2); clear - SPSC SPO1 SPO2 SPO3 SLO; lia. }
assert (NCS : forall a, spc <= a < E -> ~ aclient L ar LB FF E SCR a).
{ intros a Xa Hc. destruct (aclient_cases L ar C HI LYa HIok (BX0 ++ LB) FF LK cr A M _ E SCR a HH SPT (aclient_appb L ar LB BX0 FF E SCR a Hc)) as [Y|Y].
- clear - Xa Y SPSC SPO1 SPO2 SPO3; lia.
- clear - Xa Y SLO SPSC SPO1 SPO2 SPO3; lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (BQ : ff_bytes k mod 8 = 0 /\ (F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1 /\ ff_bytes k / 8 * 8 = ff_bytes k) by (clear - F8 B64 FR; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
assert (NCF : forall a, (F <= a < F + ff_bytes k \/ S F <= a <= S (F + ff_bytes k - 1)) -> ~ aclient L ar LB FF E SCR a).
{ intros a Ha Hc. apply (fresh_frame_not_client L ar C HI LYa HIok (BX0 ++ LB) FF LK cr A M _ E SCR F (ff_bytes k) a HH SPT).
- clear - FR; lia.
- exact FCEIL.
- exact FAPP.
- clear - F8; lia.
- clear - FR; lia.
- exact (proj1 BQ).
- eapply fframes_apart_incl. exact FAPART. intros g0 Hg; apply in_or_app; left; exact Hg.
- exact FBLK.
- exact Ha.
- exact (aclient_appb L ar LB BX0 FF E SCR a Hc). }
assert (AGF : forall a, spc <= a < E -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha. apply (proj1 PRES2 a); [clear - Ha SPSC SPO1 SPO2 SPO3 SLO SHI SPT; lia|]. apply stack_client; clear - Ha SPSC SPO1 SPO2 SPO3 SLO SHI SPT; lia. }
assert (FLNCl : ~ aclient L ar LB ((F, k, spc + 32) :: FF) 0 0 fl) by (intros X; apply FLNC; exact (aclient_appb L ar LB BX0 _ 0 0 fl X)).
assert (G : PMAUK.gctx L ar HI LB FF LK A E SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr BX0).
{ refine (PMAUK.GCTX L ar HI LB FF LK A E SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr BX0
Hk SPT SLO SHI _ OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNCl HH2 FLC _ _ FBIG F32 FLA FLR FLBIG NCF NCS).
- clear - SLO SHI SPT SPSC SPO1 SPO2 SPO3; lia.
- clear - FR; lia.
- split; [exact F8| exact (proj2 BQ)]. }
apply (KONT R2 M2 model2 F fl LK2 G B10 RP2 (conj Hh2 MI2) RT2 ASTK2).
+ eapply ek_trans. exact EK01. intros a (Ha & Hc & _). apply (proj1 PRES2 a Ha).
apply (aclient_mono L ar (BX0 ++ LB) FF E SCR spc 512 a (aclient_appb L ar LB BX0 FF E SCR a Hc)). intros x Hx. clear - Hx SPSC SPO1 SPO2 SPO3; lia.
+ eapply dk_trans. exact DK01. intros a Ha Hc Hn. rewrite (proj1 PRES2 a Ha). exact Hn.
apply (aclient_mono L ar (BX0 ++ LB) FF E SCR spc 512 a (aclient_appb L ar LB BX0 FF E SCR a Hc)). intros x Hx. clear - Hx SPSC SPO1 SPO2 SPO3; lia.
+ intros a (Ha & Hc & _). apply (proj1 PRES2 a Ha).
apply (aclient_mono L ar (BX0 ++ LB) FF E SCR spc 512 a Hc). intros x Hx. clear - Hx SPSC SPO1 SPO2 SPO3; lia.
+ intros a Ha Hc Hn. rewrite (proj1 PRES2 a Ha). exact Hn.
apply (aclient_mono L ar (BX0 ++ LB) FF E SCR spc 512 a Hc). intros x Hx. clear - Hx SPSC SPO1 SPO2 SPO3; lia.
+ exact AGF.
+ exact FWv.
+ exact FSHW.
+ exact FSHZ.
+ exact FLCv.
+ exact FLWv.
+ exact FDEFv.
+ exact VF.
+ exact VSH.
+ exact VFL.
+ intros a n sp0 scr0 Hc Hn.
exact (sm_apart L ar C HI LYa HIok (BX0 ++ LB) FF LK2 cr A M2 _ F k (spc + 32) fl sp0 scr0 a n HH2 SPT Hk ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC Hc Hn).
Qed.
Lemma wret_ek : ltac2:(TCodec.tc2 tcn__PmAUar "T3'5'9'@%2211%411&QC%611!p061'T6yR0%211'7y8%511%311p051p01:'L&Q9&QG&QL%F11'R5vFvS6vDrLrKrJrIrHrGrFrErDrCrBrAr@r?r>r=r<r;r:%GFFEDCBA@?>=<;:987654321&QF(4%Q@2Q>Q?(8%14QAQA><&RJ+Q0%22F1%54QDQE41%8371Mr9r8r7r6r4%?8Q4A654321r1%311&=&QKr2%2281%411p061pV<R51';&RLz%221<&RM&RO+2+R0%3221%52B1%:271&R4%15QCQBQAHA%D11'<&T5r3%22R?1%Q=11%Q?12%63R=21p081p0<1pV<RM1&RDrO%29R:R9QH1HHQ6Q9Q8p041p0M1p0Q71p0QH1pV:RO1pV8RB1pV6RE1pR:RJ1pR<RK1p4S81pVDRJ1pQHS81pQBS;1p6S<1pVBRN1pW:S01pR8S31pQFS>1pW4SC1pVJSD1pQ6SE1pWFS71pW@SA1pWBSH1pWDSI1pX6SJ1pU@SK1pX0SL1p2SK1pQDSJ1pQ8SK1pQ@SN1").
Proof. intros LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0 LB6 LK6 cr6 A6 Mx Mf V6 W Wx.
intros G HH6 WXin FZ. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (WB & WF & FSAPP & FSCEIL & _).
unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL.
assert (FB8 : (F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1 /\ ff_bytes k / 8 * 8 = ff_bytes k) by (split; [exact (proj1 (proj2 F8)) | exact (proj2 (proj2 F8))]).
apply (ek_piece L ar LB6 FF 0 0 W Mx Mf (PMAUK.WretX F fl k Wx) FZ).
intros a Ha Hc Ho [Wa|Wa]; [| exact (WXin a Wa Ho)].
assert (IND : forall BS ST, aclient_g BS ST L ar LB6 FF 0 0 a -> in_block LB6 a \/ (hl_img_lo L <= a < hl_img_hi L) \/ (exists b, In b LB6 /\ BS (fst b) (snd b) a)
\/ aclient L ar LB FF sp SCR a).
{ intros BS ST X. destruct X as [X|[X|[X|[X|[X|[X|X]]]]]].
- left; exact X.
- right; right; right. unfold aclient, aclient_g. right; left. split; [exact (proj1 X)|]. intros Y. destruct Wa as [[Y1|Y1]|Y1].
+ clear - Y1 FCEIL X FR. lia.
+ clear - Y1 FR F8 X SPT. unfold SB in *. pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D. lia.
+ subst a. clear - FLR X. lia.
- right; left. exact (proj1 X).
- right; right; right. unfold aclient, aclient_g. do 3 right; left. exact X.
- right; right; right. unfold aclient, aclient_g. do 4 right; left. exact X.
- right; right; right. unfold aclient, aclient_g. do 5 right; left. exact X.
- right; right; left. exact X. }
destruct (IND _ _ Hc) as [X|[X|[X|X]]].
-
destruct X as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5. destruct Wa as [[Y|Y]|Y].
+ destruct (FA (F, k, spc + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z; clear - Y Z Xb FR; lia.
+ destruct B5 as (_ & B5 & _). clear - Y Xb B5 FR F8. unfold SB in *.
pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
+ subst a. unfold FS_BYTES in BFS, FLP. clear - Xb BFS FLP. lia.
- rewrite (aly_img_lo L C LYa), (aly_img_hi L C LYa) in X. destruct Wa as [[Y|Y]|Y].
+ clear - X Y FR; lia.
+ clear - X Y FR. unfold SB in *. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
+ subst a. clear - X FLR; lia.
-
destruct X as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
unfold in_shadow_of, S in Xb. destruct Wa as [[Y|Y]|Y].
+ destruct FBIG as [Z|Z]; unfold SB in Xb.
* pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Y Z Xb D; lia.
* pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Y Z Xb D FR; lia.
+ destruct (FA (F, k, spc + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z.
* assert (E1 : (F - 1) / 8 = F / 8 - 1).
{ rewrite <- (proj1 F8) at 1. replace (F / 8 * 8 - 1) with (7 + (F / 8 - 1) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
pose proof (Z.div_le_mono (fst b + snd b - 1) (F - 1) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
clear - Y Xb D. unfold SB in *. lia.
* assert (E1 : (F + ff_bytes k) / 8 = F / 8 + ff_bytes k / 8).
{ rewrite <- (proj1 F8) at 1. rewrite <- (proj2 FB8) at 1. replace (F / 8 * 8 + ff_bytes k / 8 * 8) with ((F / 8 + ff_bytes k / 8) * 8) by lia.
rewrite Z.div_mul by lia. reflexivity. }
pose proof (Z.div_le_mono (F + ff_bytes k) (fst b) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
clear - Y Xb D FB8. unfold SB in *. lia.
+ subst a. destruct FLBIG as [Z|Z]; unfold SB in Xb.
* pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Z Xb D; lia.
* pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Z Xb D; lia.
- destruct Wa as [[Y|Y]|Y].
+ apply (NCF a); [left; clear - Y FR; lia| exact X].
+ apply (NCF a); [right; unfold S; rewrite (proj1 FB8); unfold SB in *; clear - Y; lia| exact X].
+ subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact X.
Qed.
Definition Wfr (F fl k : Z) (Wx : Z -> Prop) (a : Z) : Prop := ((F <= a < F + ff_bytes k \/ F / 8 + SB <= a < F / 8 + SB + ff_bytes k / 8) \/ a = fl) \/ Wx a.
Lemma wfr_ek : ltac2:(TCodec.tc2 tcn__PmAUar "T3'5'9'@%2211%411&QC%611!p061'T6yR0%211'7y8%511%311p051p01:'L&Q9&QG&QL%F11'R5vFvS6vDrLrKrJrIrHrGrFrErDrCrBrAr@r?r>r=r<r;r:%GFFEDCBA@?>=<;:987654321&QF(4%Q@2Q>Q?(8%14QAQA><&RJ+Q0%22F1%54QDQE41%8371Mr9r8r7r6r4%?8Q4A654321r1%311&=&QKr2%2281%411p061pV<R51';&RLz%221<&RM&RO+2+R0%3221%52B1%:271&R3%15QCQBQAHA%D11'<&T5r3%22R?1%Q=11%Q?12%63R=21p081p0<1pV<RM1&RDrO%29R:R9QH1HHQ6Q9Q8p041p0M1p0Q71p0QH1pV:RO1pV8RB1pV6RE1pR:RJ1pR<RK1p4S81pVDRJ1pQHS81pQBS;1p6S<1pVBRN1pW:S01pR8S31pQFS>1pW4SC1pVJSD1pQ6SE1pWFS71pW@SA1pWBSH1pWDSI1pX6SJ1pU@SK1pX0SL1p2SK1pQDSJ1pQ8SK1pQ@SN1").
Proof. intros LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0 LB6 LK6 cr6 A6 Mx Mf V6 W Wx.
intros G HH6 WXin FZ. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (WB & WF & FSAPP & FSCEIL & _).
unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL.
assert (FB8 : (F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1 /\ ff_bytes k / 8 * 8 = ff_bytes k) by (split; [exact (proj1 (proj2 F8)) | exact (proj2 (proj2 F8))]).
apply (ek_piece L ar LB6 FF 0 0 W Mx Mf (Wfr F fl k Wx) FZ).
intros a Ha Hc Ho [Wa|Wa]; [| exact (WXin a Wa Ho)].
assert (IND : forall BS ST, aclient_g BS ST L ar LB6 FF 0 0 a -> in_block LB6 a \/ (hl_img_lo L <= a < hl_img_hi L) \/ (exists b, In b LB6 /\ BS (fst b) (snd b) a)
\/ aclient L ar LB FF sp SCR a).
{ intros BS ST X. destruct X as [X|[X|[X|[X|[X|[X|X]]]]]].
- left; exact X.
- right; right; right. unfold aclient, aclient_g. right; left. split; [exact (proj1 X)|]. intros Y. destruct Wa as [[Y1|Y1]|Y1].
+ clear - Y1 FCEIL X FR. lia.
+ clear - Y1 FR F8 X SPT. unfold SB in *. pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D. lia.
+ subst a. clear - FLR X. lia.
- right; left. exact (proj1 X).
- right; right; right. unfold aclient, aclient_g. do 3 right; left. exact X.
- right; right; right. unfold aclient, aclient_g. do 4 right; left. exact X.
- right; right; right. unfold aclient, aclient_g. do 5 right; left. exact X.
- right; right; left. exact X. }
destruct (IND _ _ Hc) as [X|[X|[X|X]]].
-
destruct X as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5. destruct Wa as [[Y|Y]|Y].
+ destruct (FA (F, k, spc + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z; clear - Y Z Xb FR; lia.
+ destruct B5 as (_ & B5 & _). clear - Y Xb B5 FR F8. unfold SB in *.
pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
+ subst a. unfold FS_BYTES in BFS, FLP. clear - Xb BFS FLP. lia.
- rewrite (aly_img_lo L C LYa), (aly_img_hi L C LYa) in X. destruct Wa as [[Y|Y]|Y].
+ clear - X Y FR; lia.
+ clear - X Y FR. unfold SB in *. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
+ subst a. clear - X FLR; lia.
-
destruct X as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
unfold in_shadow_of, S in Xb. destruct Wa as [[Y|Y]|Y].
+ destruct FBIG as [Z|Z]; unfold SB in Xb.
* pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Y Z Xb D; lia.
* pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Y Z Xb D FR; lia.
+ destruct (FA (F, k, spc + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z.
* assert (E1 : (F - 1) / 8 = F / 8 - 1).
{ rewrite <- (proj1 F8) at 1. replace (F / 8 * 8 - 1) with (7 + (F / 8 - 1) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
pose proof (Z.div_le_mono (fst b + snd b - 1) (F - 1) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
clear - Y Xb D. unfold SB in *. lia.
* assert (E1 : (F + ff_bytes k) / 8 = F / 8 + ff_bytes k / 8).
{ rewrite <- (proj1 F8) at 1. rewrite <- (proj2 FB8) at 1. replace (F / 8 * 8 + ff_bytes k / 8 * 8) with ((F / 8 + ff_bytes k / 8) * 8) by lia.
rewrite Z.div_mul by lia. reflexivity. }
pose proof (Z.div_le_mono (F + ff_bytes k) (fst b) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
clear - Y Xb D FB8. unfold SB in *. lia.
+ subst a. destruct FLBIG as [Z|Z]; unfold SB in Xb.
* pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Z Xb D; lia.
* pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Z Xb D; lia.
- destruct Wa as [[Y|Y]|Y].
+ apply (NCF a); [left; clear - Y FR; lia| exact X].
+ apply (NCF a); [right; unfold S; rewrite (proj1 FB8); unfold SB in *; clear - Y; lia| exact X].
+ subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact X.
Qed.
Lemma ahpres_of_frame_but : ltac2:(TCodec.tc2 tcn__PmAUar "RH'5'9'@%2211%411&QC%611&Q9'T6yR0%211'7y8%511%311p051&QG&QFvDr:r9r8r7r6r5r3%9887654321';&RL+SoonPPPPP0&Q>vS6%211%5241&RO+2+Q?%3221%:261%<261&S0+XPPP0%22:1r4%421C%A231z%C214&QJ(4(8%;2LK%24QBQB1L(6%11QC%63QD31%831Q4Q3&R?%12Q7Q6&QIr;%E2Q8Q7%3321Q8&R@vFrAr@&QL%?11r<%796Q754QBQA21:p091p0>1p0A1p0K1p0N1p0Q51p0QC1pWLR<1pX0R=1pV4R01pR2R21pR0R31p2R?1pV@R=1pQDR?1pQ8R@1pQ@RC1").
Proof. intros LB FF LK cr A M M' V sp scr.
intros HH SPT HC HS FB MG D. split; [|split].
- intros a (Ha & Hc & _). apply FB. rewrite L5.unsigned_lit by lia.
destruct (aclient_cases L ar C HI LYa HIok LB FF LK cr A M V sp scr a HH SPT Hc) as [(Y1 & Y2)|Y].
+ intros r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply Y2. lia.
+ intros r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
- apply (L5.defined_grows M M' _ _ MG D).
- intros a Ha Hc Hn. exact (MG _ Hn).
Qed.
End WithIface.
End SCFG_1.
End PMAUAR.
