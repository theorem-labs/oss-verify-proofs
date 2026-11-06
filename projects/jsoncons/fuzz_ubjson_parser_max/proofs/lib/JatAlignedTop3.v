(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatRzLog JatPoison JatAllocA JatAllocB JatAllocG JatAllocV JatInitCache JatPopulate1 ArtRuns ArtRunsMem
JatCls JatFp JatClsRep JatClsGfa2 JatCellEx JatByteCell JatCARSpec JatAlloc3Pure JatDepotA JatDepot JatUnwind JatUnwindG JatMalloc JatAllocate3 JatMallocTop3 JatAllocA16 JatAllocB16 JatAllocate3A16 JatAligned16.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatAlignedTop3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocate3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCARSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatDepot."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRzLog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatUnwind."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1S"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2not"; "3Z"; "0EVOK"]; ["0GR"; "0HI"; "4machine_state"; "5bvmap"; "0M'"; "0M0"; "0Q"; "6apart"; "6cell"; "6wr"; "7aev"; "7aruns"; "8class_id"; "8class_size"; "8rz_log"; "9ret_ok"]; [":art_alloc_rodata"; ";art_alloc3_fp"; "<art_ca_cptr"; "<art_ca_events"; "<art_ca_pre"; "<art_cls_pop"; "=art_cls"; "=art_cls_mfa'"; "=art_cls_needs_populate"; "=art_cls_new"; "=art_cls_ok"; "=art_cls_rep"; "=art_cptr_ok"; "=art_evok_list"; "=art_geo"; "=art_pc_hdr"]; ["=art_prim_consts"; "=cl_au"; "=cl_cache"; "=cl_free"; "=cl_mu"; ">DInvD"; ">DRoD"; "?art_tsd"; "@art_layout"; "Aart_rz_rodata"; "Breadable8"; "Cgetr"; "Cmkst"; "Dmem_grows"; "Eloaded_segments"; "0S"]; ["FIn"; "Gadd"; "Gle"; "Glt"; "Gmodulo"; "Gmul"; "Gof_nat"; "Gpow"; "Gsub"; "0ab"; "0b1"; "0blk"; "0bot"; "0c"; "0cl"; "0ctx"]; ["0fx"; "0inited"; "0j"; "0kb"; "0key"; "0km"; "0l2"; "0loff"; "0log"; "0m8"; "0n"; "0q16"; "0qn"; "0qr"; "0qs"; "0qz"]; ["0r"; "0raw0"; "0regs"; "0regs'"; "0ris"; "0rl"; "0rom"; "0rs"; "0rz"; "0shb"; "0spb"; "HBV"; "HZ_to_bv"; "Hbv"; "Hbv_unsigned"; "0t"]; ["0top"; "0tp"; "0tsd"; "0v"; "0w"; "0x"; "0y"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_aligned16_3 := (ltac2:(TCodec.tc2 tcn__JatAlignedTop3 "h?'5'J%211'B!p021p041&Cy5'S=yR0%211%5241'8y8%611%311p061'>'6'2'Q6&L&R1r8+@%3221r:%5221%711&Q2r1r2%3221rE&R5&R7+2+Q0%3221%5281%B271%72;A%D221+QoooPP0+XP0rD%<221%I241r3+M%?2>1%A231%N251'<&QKrQ4(S;+1(:%33QD21%6251rQ1%93QD21&OrQ2%211rQ6%;3QLO9%>221&S<%12QM6%B3QM31rQ7+4%B3R31@%E231rQ0%82R41%I3R431rQ8+:%I3R:1G%L231%>2R:QK%O3R:21rQ9+;%O3R@1M%Q2231rQ3%E2RA1%Q63RA31&R2+8%221Q7&R4rQ5%221R9z%Q>3RB21rG&N%11Q4%QB3RF31rH%R62R51%R82RB1%QF3RJ71%R:2RD8%QH3RL51';%C2QF7+T0%E291%4231rQ:rF%RC2H1%S021RE%R23S641%L2F4+7%N261%=231rJrI%RL2Q11%R:3S>31rK%R<3S@1ErQ>rL%Q8221%S?23<%Q:231%I231rM%SC21SArO%SE221+RPP0%QA221&Q>rQArQ;rQ<rQ?rQ=%6854321QOR5R<rQB+TP0%T1221&R8rQC%2214%QO241rQD+Q?%SK2SJ1%R3231rQE%R221T9%S=3TA1R0%R72R1S1&R3%12RMRF%R:2@RA+QO%T52T41%52QF1%R>2R8ErQH%TF21C%RA2Q11rQI%TI21C%TJ21S7+VbTP0%RF221+V[bo8rQJ+RH%N221%RK241%RL25:+D%TG2TF1%U52Q61rQN%S1221+G%TL2TK1%U:2Q;1rQO%S6221&G%14Q8:@Q>rQL%34Q6<1Q@rQF+Q5%U62U51%UD21QD%844AG1rQG+QoonlP0+`PQoooPP0%QG212%=44F31%>45BEQKrR0%@4Q8D1QM%A4Q6EH:%B4Q1F86&I&QNrR<rR9%R221R4%54431R5&QJrR=rR:rQK%43321rR>rR4%=4<21R=rR?rR1%V42UJ1%VA2UL1+Q2%V62V51%D4C631&Q0rR@%211&HrRA+RQTHu1%45K321U9&QIrRB%211&QHrRC%211&QGrRDrR;%362KOQ41N&Q@rR8rRE%33Q721rRF+QW^^H%E5Q<21BV:rRG+Qgck2%H5Q?21EU4rRH+QVmdH+Sa0%WD221u8+Q8%W:2W91%Q05QG7431rRI+Sa8%WK291u2%Q55QL421WKrRJ+Sa:%X02>1+RP0%Q:5R14261rRK+Qian0%Q=5R421@UIrRL+QWQWH+Q<%X9221u4%QC5R:521T;rRM+QD%X>271+UN%QH5R?4261rRN+RE%XC2<1%QL5RC31QIWArRO+QV\dH%QO5RF21Q2QCrS0%XI2KQ@%R25RI21@V>rS1%R45RK1Q>Q7Q;rS2%XN2Q5VG%R75RN21EVCrS3+QW^_L+N%R;5S232I1rS4+QibQ8%Y621RD%R?5S631R<X4rS5+SS0%Y:2Q71%RC5S:31R@VOrS6%Y=2Q7QG%RF5S=21RCW2rS7%Y@2Q4W9%RI5S@21QLR8rS8%YC2Q2YA%RL5SC21QOR;&Q?+V@%YG2Q21rS9%432SG1&Q;%YK2Q35rS:%362Q<QARHSK1&Q:%12SMSH&=%ZH1Z6&QB%11SH(7%11Z:%Y73531%711(9%Y:3Z<SC1p031&QD%11SN+XPP0%Z221QM%Y@3ZD31%>1SJ%YB3@1<&Q8%12SMSJ%YE3ZG1<%:1SG%ZF219+S`PPPP0%XB221&Q7&R6&4&QC%11SO%32[31%511&Q9%12T8T3%[2231%:2T51+`PPPP0%XO221%X>2>1p0C1p0G1&Q=v?rSA&Q3%13R=TGTD%53431&QA%11T?%[52Y:[9%Y<221%Q81TB%W6231%XM231rSB%[G2U1[>+WJ%U15UH32TN1p051pW>\01&R0&1%QL1TJ%Q31TK%33\521%53\6[I1rSC%[G2[E[J%\42U;1%U=5V431U:=p051pW8\<1&QE(0%11TO%34S>S@1E&QF%11;%[>2[DZC%\?2U4SB%[12\M1%[B3\M31r4%[C21[6rSE%[62]21%[G3]231r5%[H21[CrSG%[K3]621%]91]:(3+3%[L3]=1[J%[M3]>ZH[K+9%[O3]@1[M+B%\13]B1[O+C%\33]D1\1%\43]EX3\2+E%\63]G1\4+F%\83]I1\6%\93]JX3\7+H%\;3]L1\9+I%\=3]N1\;+J%\?3^01\=+K%\A3^21\?%S@1I%I3J21%J3K51%K3L81%L3M;1%M3N>1%N3O@1%O3Q0C1%Q03Q1F1%Q13Q2H1%Q23Q3K1%Q33Q4N1%Q43Q5Q11%Q53Q6\=1%Q63Q7Q41%R73Q8]K1%]42^3]KrSM%]621]M%]83^C31p051pV2Q>1&QMrSKr6%3221rSJ%Z=21Z?&S>%12^N^9%\<231%Z5225%[L221%TE11&Q1+RS0%ZF2=1rSDrS@rS?rSIrS>rS=%?2_<^F%:>87S:SE6V;5VDU84UA321%U111%^N1^8rSO%11^:%^63_<31p051p0B1pW<_D1rS<%S24<1V?_9%_;2BUEr9%UH32U51%_>2RJUH&Q5&Q4%12VIVF%311%UI65SASMVK1_?%42VIVG%611%UH2VK1&Q<&M%11VL%:2VMVJ%T<11%5331W1r<%]H2]B1+X0%[B231%]9231r=%]J21^@%_53`91_1r?%`62W6Q;%\521`5%Y@5Z731Y=_Jr@%`:2W6Q@+?%\:221%YE5Z<41YB8rA%`?2W7U4+>%\?221%YJ5ZA41XF^6rB%`D2W8TN+<%\D221rT2%Z05ZG52X>1rC%`>2`<W8%`K2W?1%Z45ZK31Z1U4%^G2^A`E%\@2`FUC%^7221rS;%`E2`C1%a22W:1%`G2`ET?%a4221%a521`L%Z>5[5^81Z;^Jp081pU6a=1%`:3a>R?^M%W:11%a;27UE%ZD5[;^>1ZAV1p031%W<1R@%`@3W>1W:%VN2RBRC%`B3aD1W9+QPP0%]52a;1%^L2G1%a92a7RJ%a:2a8RJ%aG221rT0%a=271%aJ21aA%_E241%aL25U3%]?231%_6231%WO11rT1%aE2?1%b22S51%b321a9%[<5\3^J1[9V<p061p0B1pU6b<1p0G1p0J1%a;3b?UAb8%X;11+\hkdfgWVVmUeI%[E5\<_KS4ZH1%b>2S5`7rSH%b@2S71%^?21b?%[J5\A`04ZM1%_K261p091rT@rT?%W;3GSJSL%VK3c>21&QLvR@rT;rT<%453_F2`;1%9261p0;1p0G1p0QD1p0QJ1p0R71p0R<1p0RC1p0RI1p0RO1p0S41p0S81p0S>1p0SE1p0SI1p0T01p0T41p0T71p0U31p0U81p0VH1p0VM1p0W31pTFcJ1pQ:cL1pV8d21'Kv@rSF+_U`8%bJ3d91bH/01d9%Q55Q441W:U5%77]NXE6Q5Q@W61p091p0WD1p0WG1p0WL1p0X91p0XG1p0XN1p0YH1p0YN1p0Z:1p0Z=1p0ZB1p0ZH1p0ZL1p0[01p0[41p0[91p0[>1p0[C1p0[G1p0[J1p0[N1p0\21p0\71p0\=1p0\D1p0\H1p0\N1p0]41p0]=1p0]A1p0]E1p0]J1p0]O1p0^31p0^71p0^=1p0^A1p0^I1p0^M1p0_31p0_:1p0_<1p0_>1p0_A1p0_C1p0_I1p0_O1p0`21p0`51p0`;1p0`A1p0`C1p0`I1p0`O1p0a31p0a51p0a91p0a;1p0a>1p0a@1p0aD1p0aI1p0b11p0b91p0b@1p0bG1p0bJ1p0bO1p0c41p0c:1p0c@1p0cC1p0cH1p0cM1p0d31p0d71p0d?1p0dF1p0dN1p0e51p0e91tVDfGeD1tTDfHeO1tW:fIf:1tTLfJf?1pTNfH1pU4fJ1pU8fL1pUHfN1pUDfO1pUJg01pULg11pV@g21pV0g31pVBg41pV<g51pTJg61pW2g71pTHg81pU>g91pU<g:1pUNg;1pV:g<1pVFg=1pU@g>1pW0g?1pU0g@1pW6gA1pU:gB1pW4gC1pUFgD1pQ4gE1pT0gF1pV4gN1pV>gI1pQ<gJ1pV6h01pUBh;1pQ>h81")) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 0%nat 0%nat).
Variable log : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 2%nat 0%nat).
Variable M0 : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 3%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 4%nat 0%nat).
Variable raw0 : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 5%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 6%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 7%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 8%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 9%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 10%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 11%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 12%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 13%nat 0%nat).
Variable loff : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 14%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_aligned16_3) 15%nat 0%nat).
Theorem art_aligned16_3 : ltac:(sec_stmt2 constr:(SEC_T_art_aligned16_3) 16%nat 0%nat).
Proof using Type Q log regs M0 rom raw0 S HI n tp key tsd ctx t loff spb.
intros ris qs km l2 blk top bot rl rz qz rs qr qn m8 q16 kb inited cl c w ab shb
H1 Hret H2 H4 H10 H11
Hn Hn16 Erl Erz Erz16 Hqz En Hm8 Ers Ers16 Hrs Hprim
GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Hloff Hloff' Hloff'' Htpd Htsdd
Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs
W RD0 Wt Wsh RO C1046 RZRO L TSD PC Ci Cr Cmax Cmin16 Cmax2048 Chook Cmfs Cfb Cpp Cg Clsan Ctctx Ctid Cctx30 Cfast Cunw C40 Ctop Cbot
PH RC OK Hin Emu Room EV PZ1 PZ2 DI DR K.
assert (Eab : ab = spb + c * 2 ^ 32 + w * 16) by reflexivity.
assert (Eshb : shb = 2147450880 + 8192 * qs + c * 2 ^ 29) by reflexivity.
clearbody ab shb.
pose proof (AsanTab.class_id_ok (rs + 16 + rz) ltac:(lia)) as (Hc & Hfit & _). fold c in Hc, Hfit.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
assert (At_i : apart t 4096 0x10000 (0x691000 - 0x10000)) by (unfold apart; clear - G9; lia).
assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
assert (Ac_i : apart ctx 4096 0x10000 (0x691000 - 0x10000)) by (unfold apart; clear - G15; lia).
assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G16; lia).
change (hid (t + 4096 <= 0x10000 \/ 0x691000 <= t)) in G9. change (hid (ctx + 4096 <= 0x10000 \/ 0x691000 <= ctx)) in G15.
clear G10 G16.
pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _).
assert (Hkm : 0 <= km) by lia. assert (Hkm' : 262144 * km <= 3758096384) by lia.
pose proof DI as (dN & dTF & dST & DG1 & DG2 & DG3 & DG4 & DG5 & DG6 & DG7 & _).
pose proof TSD as (_ & _ & _ & _ & _ & TR).
pose proof PC as (_ & _ & _ & _ & _ & Cpg1 & Cpg2 & _).
destruct (art_icu1_16 regs M0 rom raw0 S n tp key tsd ctx t top bot H1 H2 H4 H10 H11 ltac:(lia) HS47 ltac:(lia) G7 ltac:(lia) G9 ltac:(unfold apart; lia)
ltac:(unfold apart; lia) G15 G18 G19 G20 G21 G22 ltac:(lia) Htop W Wt TSD Ci Cctx30 ltac:(pose proof L as L'; unfold art_layout in L'; tauto) Cfast Cunw C40 Ctop Cbot)
as (r1 & M1 & RUN1 & Q1_1 & Q1_2 & Q1_10 & Q1_11 & Q1_12 & Q1_13 & Q1_14 & Q1_15 & Q1_24 & Q1_4 & K1 & G01 & A1
& F8 & F16 & F24 & F32 & F40 & F48 & F56 & F64 & E36 & E44 & E52 & E60 & E68 & E76 & E84 & E92 & E00 & E08 & E28 & E20 & E16' & W1).
eapply ar_steps; [exact RUN1|].
assert (T1 : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= S - 2288 \/ S <= a) -> (a + Z.of_nat k <= t + 3168 \/ t + 3169 <= a) ->
cellA M0 a k v -> cellA M1 a k v).
{ intros a k v Ha Hak O1 O2 C. apply (cell_agree M0 M1); [|lia|lia|exact C]. intros x Hx. apply A1; lia. }
assert (HS8 : S mod 8 = 0). { clear - HS16. rewrite <- (Z.div_exact S 16) in HS16 by lia. rewrite HS16. replace (16 * (S / 16)) with ((2 * (S / 16)) * 8) by lia. apply Z_mod_mult. }
assert (RD1 : readable8 M1 (S - 16) top).
{ intros a Ha1 Ha2 Ha8. destruct (Z.lt_ge_cases a S) as [Lo|Hi].
- assert (a = S - 16 \/ a = S - 8) as [->| ->].
{ clear - Ha1 Lo Ha8 HS8. rewrite <- (Z.div_exact a 8) in Ha8 by lia. rewrite <- (Z.div_exact S 8) in HS8 by lia. lia. }
+ eexists. exact F16.
+ eexists. exact F8.
- destruct (RD0 a ltac:(lia) ltac:(lia) Ha8) as [w' Cw]. exists w'. apply T1; [lia|cbn; lia|cbn; lia| clear - Hi G8 HHI; cbn; lia | exact Cw]. }
destruct (art_unwind_fast_any r1 M1 rom (0x81640 : bv 64)%bv (S - 2224) (S - 2136) 0x796a0 S top bot
Q1_1 ltac:(unfold ret_ok; bveq) Q1_2 Q1_10 Q1_11 Q1_12 Q1_13 Q1_14 Q1_15
ltac:(lia) ltac:(lia) ltac:(lia) Hbot Hbt Htop4 Htop ltac:(lia) HS8 ltac:(lia) ltac:(lia)
ltac:(eapply wr_sub; [exact W1|lia|lia]) ltac:(eapply wr_sub; [exact W1|lia|lia]) (fun _ _ => RD1)
ltac:(apply T1; [lia|cbn; lia|cbn; lia|clear - At_i; unfold apart in At_i; cbn; lia|exact Cpg1]) ltac:(apply T1; [lia|cbn; lia|cbn; lia|clear - At_i; unfold apart in At_i; cbn; lia|exact Cpg2]))
as (r2 & M2 & RUN2 & Q2_2 & Q2_1 & K2 & G12 & A2 & (sz & Hsz & Csz & TRC)).
eapply ar_steps; [exact RUN2|].
assert (T2 : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= S - 2288 \/ S - 2224 <= a) -> (a + Z.of_nat k <= S - 2128 \/ S - 2124 <= a) ->
(a + Z.of_nat k <= S - 2120 \/ S - 1880 <= a) -> cellA M1 a k v -> cellA M2 a k v).
{ intros a k v Ha Hak O1 O2 O3 C. apply (cell_agree M1 M2); [|lia|lia|exact C]. intros x Hx. apply A2; lia. }
pose proof (art_icu2_16_fn r2 M2 rom S n t (U (getr regs 23)) (U (getr regs 24)) Q2_2 ltac:(rewrite K2 by inl; exact Q1_24)
ltac:(lia) HS47 ltac:(lia) Hn16 G7 ltac:(lia) ltac:(unfold apart; lia) (u64_range _) (u64_range _)
ltac:(eapply wr_grows; [exact G12|exact W1]) ltac:(eapply wr_grows; [exact G12|]; eapply wr_grows; [exact G01|exact Wt])
ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E36]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E44])
ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E52]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E60])
ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E68]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E76])
ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E84]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E92])
ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E00]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E08])) as RUN3.
match type of RUN3 with msteps _ _ (mkst ?R _ ?X _) => set (r3 := R) in RUN3; set (M3 := X) in RUN3 end.
eapply ar_steps; [exact RUN3|].
assert (A03 : art_agree [(S - 2288, 2288); (t + 3168, 1)] M0 M3).
{ intros x Hx. cbn [art_out fst snd] in Hx. unfold M3. rewrite 5 Wn_outside by (cbn; clear - Hx G7 G8 G2 HHI G1 HS47; lia). rewrite A2 by (clear - Hx; lia). apply A1; clear - Hx; lia. }
assert (G03 : mem_grows M0 M3). { eapply mem_grows_trans; [exact G01|]. eapply mem_grows_trans; [exact G12|]. unfold M3. zgrows. }
assert (T_img3 : forall a (k : nat) v, 0x10000 <= a -> a + Z.of_nat k <= 0x691000 -> cellA M0 a k v -> cellA M3 a k v).
{ intros a k v Ha Hk C. apply (art_cell_tr1 _ M0 M3 a k v A03); [|exact C]. revert Ha Hk. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris. intros Ha Hk. zarith_f. }
assert (RO3 : art_alloc_rodata M3).
{ unfold art_alloc_rodata in *. destruct RO as (a1 & a2 & a3). repeat split; apply T_img3; first [exact a1|exact a2|exact a3|clear; lia|clear; cbn; lia]. }
assert (RZRO3 : art_rz_rodata M3).
{ unfold art_rz_rodata in *. destruct RZRO as (a1 & a2 & a3). repeat split; apply T_img3; first [exact a1|exact a2|exact a3|clear; lia|clear; cbn; lia]. }
assert (L3 : art_layout M3).
{ eapply art_layout_fp; [exact A03| |exact L]. intros z Hz. apply (art_gap_out _ 0x10000 (0x20cbc8 - 0x10000)); [|clear - Hz; lia]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
assert (T3 : art_tsd M3 tp key tsd ctx t). { apply (art_tsd_tr _ M0 M3 tp key tsd ctx t A03); [| | | |exact TSD]; clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
assert (PC3 : art_prim_consts spb ris M3).
{ eapply art_prim_consts_fp; [exact A03| |exact PC]. intros z Hz. apply (art_gap_out _ 0x10000 (0x691000 - 0x10000)); [|clear - Hz; lia]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
assert (W3 : wrA M3 (S - 2176 - 1920) 1920) by (eapply wr_grows; [exact G03|]; eapply wr_sub; [exact W|lia|lia]).
assert (Wt3 : wrA M3 t 4096) by (eapply wr_grows; [exact G03|exact Wt]).
assert (Wsh3 : wrA M3 (2147450880 + 8192 * qs) (2 ^ 34)) by (eapply wr_grows; [exact G03|exact Wsh]).
assert (Clsan3 : cellA M3 (tp + loff) 4 0) by (apply T_img3; [clear - Hloff'; lia|clear - Hloff''; cbn; lia|exact Clsan]).
assert (Ctctx3 : cellA M3 t 8 ctx). { apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|exact Ctctx]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
assert (Ctid3 : cellA M3 (ctx + 8) 4 0). { apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|exact Ctid]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
assert (PH3 : art_pc_hdr (t + 208) inited M3).
{ apply (art_pc_hdr_tr _ (t + 208) inited M0 M3 ltac:(clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; lia) ltac:(clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; lia) A03); [|exact PH]. intros c' Hc'. revert Hc'. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris. intros Hc'. zarith_f. }
assert (RC3 : art_cls_rep (t + 208) spb ris c cl M3).
{ apply (art_cls_rep_tr [(S - 2288, 2288); (t + 3168, 1)] (t + 208) spb ris c cl M0 M3); first [ exact RC | exact G03 | exact A03 | exact Hl16 | idtac ];
first [ clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; lia | clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f ]. }
assert (PZ1_3 : forall y, cl_au cl <= 8 * y < cl_mu cl -> cellA M3 (shb + y) 1 250).
{ intros y Hy. apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|apply PZ1; exact Hy]. revert Hy. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris. intros Hy. zarith_f. }
pose proof (art_class_size_facts c Hc) as (Hcsz & _).
assert (PZ2_3 : forall v, In v (cl_cache cl ++ cl_free cl) -> cellA M3 (shb + 2 * v) 1 250).
{ intros v Hv. apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|apply PZ2; exact Hv].
pose proof (proj1 (Forall_forall _ _) Hfor v Hv) as (Hv0 & Hv1 & _). revert Hv0 Hv1 Hcsz. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris. intros Hv0 Hv1 Hcsz. zarith_f. }
assert (DI3 : DInvD l2 blk (Datatypes.S kb) M3).
{ apply (DInvD_frame l2 blk (Datatypes.S kb) M0 M3 DI). intros x Dx. apply A03. revert Dx. apply art_dpriv_out; clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
assert (DR3 : DRoD M3).
{ apply (DRoD_frame M0 M3 DR). intros x Hx. apply A03. apply (art_gap_out _ 0x10000 (0x20cbc8 - 0x10000)); [|clear - Hx; lia]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
assert (Cstk3 : cellA M3 (S - 2136) 8 (S - 2120)).
{ unfold M3. do 5 (apply cell_Wn_other; [clear - G7 HHI G1; lia|clear - G8 G2 HS47; cbn; lia|clear - HHI G1; lia|clear - HS47; cbn; lia|unfold apart; clear - G8 HHI; cbn; lia|]).
apply T2; [clear - HHI G1; lia|clear - HS47; cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E28]. }
assert (Cszt3 : cellA M3 (S - 2136 + 8) 8 sz).
{ replace (S - 2136 + 8) with (S - 2128) by lia. unfold M3.
do 5 (apply cell_Wn_other; [clear - G7 HHI G1; lia|clear - G8 G2 HS47; cbn; lia|clear - HHI G1; lia|clear - HS47; cbn; lia|unfold apart; clear - G8 HHI; cbn; lia|]).
replace sz with (sz + 0 * 2 ^ 32) by lia. replace (S - 2136 + 8) with (S - 2128) in Csz by lia.
apply cell8_of_cells4; [clear - HHI G1; lia|clear - HS47; lia|clear - Hsz; lia|lia|exact Csz|].
replace (S - 2128 + 4) with (S - 2124) by lia. apply T2; [clear - HHI G1; lia|clear - HS47; cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E16']. }
assert (DP3 : DPreD blk M3 (S - 2120) sz).
{ unfold DPreD. split; [exact Hsz|]. split.
{ clear - HS8. rewrite <- (Z.div_exact S 8) in HS8 by lia. rewrite HS8. replace (8 * (S / 8) - 2120) with ((S / 8 - 265) * 8) by lia. apply Z_mod_mult. }
split; [clear - HHI G1; lia|]. split; [clear - HS47 Hsz; lia|]. split; [unfold apart; clear - Dblk HHI Hsz; lia|].
intros i Hi. destruct (TRC i Hi) as [w' Cw]. unfold rcell. eexists.
assert (C3' : cellA M3 (S - 2120 + 8 * i) 8 (U w')).
{ unfold M3. do 5 (apply cell_Wn_other; [clear - G7 HHI G1 Hi; lia|clear - G8 G2 HS47 Hi Hsz; cbn; lia|clear - HHI G1 Hi; lia|clear - HS47 Hi Hsz; cbn; lia|unfold apart; clear - G8 HHI Hi Hsz; cbn; lia|]).
replace (S - 2120 + 8 * i) with (S - 2136 + 16 + 8 * i) by lia. exact Cw. }
exact C3'. }
rewrite Eshb in PZ1_3, PZ2_3.
apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
assert (C1046_3 : cellA M3 0x10498 1 4) by (apply T_img3; [clear; lia|clear; cbn; lia|exact C1046]).
apply (art_allocate3_16 EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) log r3 M3 rom (0x527c4 : bv 64)%bv (S - 2176) HI n (S - 2136) tp key tsd ctx t loff spb ris qs km l2 blk
(S - 2120) sz rl rz qz rs qr qn m8 q16 kb inited cl
ltac:(unfold r3; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; rewrite K2 by inl; exact Q1_4)
ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity)
ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity)
Hn Erl Erz Erz16 Hqz En Hm8 Ers Ers16 Hrs Hprim
GEO ltac:(clear - HHI; lia) ltac:(clear - HHI; lia) ltac:(clear - HS47; lia) ltac:(clear; lia) ltac:(clear; lia)
ltac:(clear - HHI G1 HS47; lia) ltac:(clear - Hsz; lia) ltac:(clear; lia) ltac:(clear - Hsz; lia)
Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs
W3 Wt3 Wsh3 RO3 C1046_3 RZRO3 L3 T3 PC3
ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Ci]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cr])
ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cmax]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cmin16])
ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cmax2048]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Chook])
ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cmfs]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cfb])
ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cpp]) ltac:(apply T_img3; [clear; lia|clear; cbn; lia|exact Cg])
Clsan3 Ctctx3 Ctid3 Cstk3 Cszt3
PH3 RC3 OK Hin Emu Room EV PZ1_3 PZ2_3 DI3 DP3 DR3).
intros r4 M4 b1 P4_10 P4_2 P4_1 K4 G34 AG34 DI4 PH4 RC4 OK4 CP4 Hb1 Hty CL1 CL3 CL4 CL2 SAB4 SHZ SHP PSH LCH.
fold c in P4_10, AG34, RC4, OK4, CP4, CL1, CL2, CL3, CL4, SAB4, SHZ, SHP, PSH, LCH. fold w in P4_10, AG34, CP4, CL1, CL2, CL3, CL4, SAB4, SHZ, SHP, PSH, LCH.
rewrite <- ?Eab in P4_10, AG34, CL1, CL2, CL3, CL4, LCH. rewrite <- ?Eshb in SAB4, SHZ, SHP, PSH.
pose proof CP4 as (Hw0 & Hwsz & _).
pose proof OK4 as OK'. unfold art_cls_ok in OK'. cbn [art_cls_pop cl_cache cl_free cl_au cl_mu cl_mfa] in OK'.
destruct OK' as (_ & (_ & Haumu') & _ & _ & _ & Hmu3' & _).
assert (Hub8 : (ab + rz) / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz).
{ rewrite Eab, Espb, Erz16. replace (65536 * qs + c * 2 ^ 32 + w * 16 + 16 * qz) with ((8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz) * 8) by lia. apply Z.div_mul. lia. }
assert (Hqr8 : rs / 8 = qr). { rewrite Ers, Z.mul_comm. apply Z.div_mul. lia. }
assert (ABOVE : forall x, S - 2176 <= x -> ~ art_alloc3_fp16 (S - 2176) t spb ris qs c km ab rz n rs l2 blk x).
{ intros x Hx FX. apply art_alloc3_fp16_sub in FX. revert FX. apply (art_alloc3_fp_above (S - 2176) HI t spb ris qs c km ab rz n rs l2 blk _ _ x Hc Hkm Hkm' ltac:(clear - HHI; lia) G1 Espb G4 Eris G6 G8 Dl2 Dblk
ltac:(clear - Eab Hc Hw0 Hwsz Haumu' Hmu3' Hfit Hrs; lia) Hub8 Hqr8 ltac:(clear - Hc Hw0 Hwsz Haumu' Hmu3' Hfit Hrs Hqz Ers Erz16 Espb Eris G6 G2 Hcsz; lia) Hx). }
assert (T34 : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> S - 2176 <= a -> cellA M3 a k v -> cellA M4 a k v).
{ intros a k v Ha Hak O1 C. apply (art_cell_agree _ M3 M4); [|exact Ha|exact Hak|exact C]. intros x Hx. apply AG34. apply ABOVE. clear - Hx O1. lia. }
assert (TF : forall a v, S - 64 <= a -> a + 8 <= S -> cellA M1 a 8 v -> cellA M4 a 8 v).
{ intros a v Ha Ha' C. apply T34; [clear - Ha HHI G1; lia|clear - Ha' HS47; cbn; lia|clear - Ha; lia|]. unfold M3.
do 5 (apply cell_Wn_other; [clear - G7 HHI G1 Ha; lia|clear - G8 G2 HS47 Ha'; cbn; lia|clear - HHI G1 Ha; lia|clear - HS47 Ha'; cbn; lia|unfold apart; clear - G8 HHI Ha Ha'; cbn; lia|]).
apply T2; [clear - HHI G1 Ha; lia|clear - HS47 Ha'; cbn; lia|clear - Ha; cbn; lia|clear - Ha; cbn; lia|clear - Ha; cbn; lia|exact C]. }
pose proof (art_ic3_16_fn r4 M4 rom raw0 S n (ab + rz) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21)) (U (getr regs 22))
P4_2 P4_10 ltac:(clear - Eab Espb G4 Hc Hw0 Hwsz Haumu' Hmu3' Hqz Erz16 Eris G6 G2 Hcsz; lia) ltac:(clear - HHI G1; lia) HS47 Hret ltac:(clear - Hn Hrs Hprim Hqz Erz16; lia)
(u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
ltac:(apply T34; [clear - HHI G1; lia|clear - HS47; cbn; lia|clear; lia| unfold M3; clear - HHI G1 HS47 G7 G8 G2; zcell])
ltac:(apply T34; [clear - HHI G1; lia|clear - HS47; cbn; lia|clear; lia| unfold M3; clear - HHI G1 HS47 G7 G8 G2; zcell])
ltac:(apply T34; [clear - HHI G1; lia|clear - HS47; cbn; lia|clear; lia| unfold M3; clear - HHI G1 HS47 G7 G8 G2; zcell])
ltac:(apply T34; [clear - HHI G1; lia|clear - HS47; cbn; lia|clear; lia| unfold M3; clear - HHI G1 HS47 G7 G8 G2; zcell])
ltac:(apply TF; [clear; lia|clear; lia|exact F8]) ltac:(apply TF; [clear; lia|clear; lia|exact F16]) ltac:(apply TF; [clear; lia|clear; lia|exact F24])
ltac:(apply TF; [clear; lia|clear; lia|exact F32]) ltac:(apply TF; [clear; lia|clear; lia|exact F40]) ltac:(apply TF; [clear; lia|clear; lia|exact F48])
ltac:(apply TF; [clear; lia|clear; lia|exact F56]) ltac:(apply TF; [clear; lia|clear; lia|exact F64])) as RUN5.
eapply ar_steps; [exact RUN5|]. apply ar_done.
apply (K _ M4 b1).
- gres. exact P4_10.
- gres. reflexivity.
- gres. reflexivity.
- intros r Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; try apply Z_to_bv_bv_unsigned;
rewrite K4 by inl; unfold r3; gres; try apply Z_to_bv_bv_unsigned; rewrite K2 by inl; first [ rewrite K1 by inl; reflexivity | rewrite Q1_4; symmetry; exact H4 ].
- eapply mem_grows_trans; [exact G03|exact G34].
- intros x N1 N2.
rewrite (AG34 x ltac:(intros FX; apply art_alloc3_fp16_window in FX; destruct FX as [FX|FX]; [exact (N1 FX)|exact (N2 FX)])).
destruct (Z.eq_dec (U x) (t + 3168)) as [e|ne].
+ assert (Ex : x = Z_to_bv 64 (t + 3168)) by (rewrite <- e; symmetry; apply Z_to_bv_bv_unsigned). rewrite Ex.
rewrite (art_byte_of_cell1 M0 (t + 3168) 0 ltac:(clear - At_i; unfold apart in At_i; lia) ltac:(clear - G7 G8 G2; lia) ltac:(clear; lia) Cunw).
apply art_byte_of_cell1; [clear - At_i; unfold apart in At_i; lia|clear - G7 G8 G2; lia|clear; lia|]. unfold M3. clear - G7 G8 G2 HHI G1 HS47. zcell.
+ apply A03. cbn [art_out fst snd]. clear - N1 ne. repeat split; lia.
- exact DI4.
- exact PH4.
- exact RC4.
- exact OK4.
- exact CP4.
- exact Hb1.
- exact Hty.
- exact CL1.
- exact CL3.
- exact CL4.
- exact CL2.
- exact SAB4.
- exact SHZ.
- exact SHP.
- exact PSH.
- exact LCH.
Qed.
End SE.
End Spec.
