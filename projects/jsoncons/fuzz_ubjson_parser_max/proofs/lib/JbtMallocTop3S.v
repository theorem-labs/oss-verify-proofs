(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtRzLog JbtPoison JbtAllocA JbtAllocB JbtAllocG JbtAllocV JbtInitCache JbtPopulate1 ArtRuns ArtRunsMem
JbtCls JbtFp JbtClsRep JbtClsGfa2 JbtCellEx JbtByteCell JbtCARSpec JbtAlloc3Pure JbtDepotA JbtDepot JbtUnwind JbtUnwindG JbtMalloc JbtAllocate3 JbtAllocate3S JbtMallocTop3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtMallocTop3S () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocate3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCARSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtDepot."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRzLog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtUnwind."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1S"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2not"; "3Z"; "0EVOK"]; ["0GR"; "0HI"; "4machine_state"; "5bvmap"; "0M'"; "0M0"; "0Q"; "6apart"; "6cell"; "6wr"; "7aev"; "7aruns"; "8class_id"; "8class_size"; "8rz_log"; "9ret_ok"]; [":art_alloc_rodata"; ";art_alloc3_fp"; "<art_ca_cptr"; "<art_ca_events"; "<art_ca_pre"; "<art_cls_pop"; "=art_cls"; "=art_cls_mfa'"; "=art_cls_needs_populate"; "=art_cls_new"; "=art_cls_ok"; "=art_cls_rep"; "=art_cptr_ok"; "=art_evok_list"; "=art_geo"; "=art_pc_hdr"]; ["=art_prim_consts"; "=cl_au"; "=cl_cache"; "=cl_free"; "=cl_mu"; ">DInvD"; ">DRoD"; "?art_tsd"; "@art_layout"; "Aart_rz_rodata"; "Breadable8"; "Cgetr"; "Cmkst"; "Dmem_grows"; "Eloaded_segments"; "0S"]; ["FIn"; "Gadd"; "Gle"; "Glt"; "Gmodulo"; "Gmul"; "Gof_nat"; "Gpow"; "Gsub"; "0ab"; "0b1"; "0blk"; "0bot"; "0c"; "0cl"; "0ctx"]; ["0fx"; "0inited"; "0j"; "0kb"; "0key"; "0km"; "0l2"; "0loff"; "0log"; "0m8"; "0n"; "0qn"; "0qr"; "0qs"; "0qz"; "0r"]; ["0raw0"; "0regs"; "0regs'"; "0ris"; "0rl"; "0rom"; "0rs"; "0rz"; "0shb"; "0spb"; "HBV"; "HZ_to_bv"; "Hbv"; "Hbv_unsigned"; "0t"; "0top"]; ["0tp"; "0tsd"; "0v"; "0w"; "0x"; "0y"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_malloc3_small := (ltac2:(TCodec.tc2 tcn__JbtMallocTop3S "gH'5'J%211'B!p021p041&Cy5'S<yR0%211%5241'8y8%611%311p061'>'6'2'Q6&L&R1r7r9%3221%511&Q2r1r2%3221rD&R5&R7+2+Q0%3221%5281%@271+@%82<1%C231+QoooPP0+XP0rC%=221%H241r3+M%@2?1%B231%M251'<&QKrQ3(S:+1(:%33QC21%6251rQ0%93QC21&OrQ1%211rQ5%;3QKQ09%>221&S;%12QL6%B3QL31rQ6+4%B3R21@%E231rO%82R31%I3R331rQ7+:%I3R91G%L231%N3R81=';&R2rQ2%22N1&R3+8%2241%7241&N%11Q6%Q93R<QN1rE%QN2QM1%R02QI1%Q=3R@R21%R22QKR3%Q?3RB51%@2Q<6+T0%B281%D231%R82@QLrB%RD221%QG3RJM1z%I21R1+7%K2R31%M231rGrF%RC2K1%R03S331rQ:rH%Q3221%S223:%Q5231%Q7231rIrK%S7221+RPP0%Q;221&Q>rQ=rQ8rQ;rQ9rQ4%685QH432R51R@rQ>+TP0%SC221&R8rQ?%2214%QI241rQ@+Q?%S?2S>1%QM231&R4rQA%221S=%S13T41Q9%R22Q:R1%R02S1B%R42@RG+QO%SI2SH1%R42RD1%R82Q@ErQD%T821C%R;2Q11rQE%T;21C%T<21RJ+Vb\P0%R@221+V[jY8rQF+RH%N221%RE241%RF25:+D%T;2T:1%TG2Q61rQJ%RK221+G%T@2T?1%TL2Q;1rQK%S0221&G%14Q8:@Q>rQH%34Q5<1Q@rQB+Q5%TJ2TI1%U621QD%844AG1rQC+QoonlP0+`PQoooPP0%QG212%=44F31%>45BEQKrQL%@4Q8D1QM%A4Q6EH:%B4Q1F86&I&QNrR8rR5%R221R4%54431R5&QJrR9rR6rQG%43321rR:rR0%=4<21R=rR;rQM%UH2U=1%V32U?1+Q2%UJ2UI1%D4C631&Q0rR<%211&QIrR=%211&QHrR>%211&QGrR?rR7%362JO1IN&Q@rR4rR3rR@%43321&HrRA+QWehHu1%45Q:321UKrRB+QgkU2%75Q=214T:rRC+QWTnH+Sa0%W4221u8+Q8%VL2VK1%?5QE7431rRD+Sa8%W;291u2%D5QJ421VLrRE+Sa:%W@2>1+RP0%I5QO4261rRF+QiiX0%L5R221@TOrRG+QWXaH+Q<%WI221u4%Q25R8521T9rRH+QD%WN271+UN%Q75R=4261rRI+RE%X32<1%Q;5RA31Q8W2rRJ+QVdP0%Q>5RD21Q2QFrRK%X92KQB%QA5RG21@UDrRL%QC5RI1Q>Q7Q;rRM%X>2Q5V<%QF5RL21EUIrRN+QWeiL+N%QJ5S032I1rRO+Qii[8%XF21RB%QN5S431QKWErS0+SS0%XJ2Q71%R25S831QOV5rS1%XM2Q7QG%R55S;21R2V8rS2%Y02Q4VN%R85S>21QLR:rS3%Y32Q2XB%R;5SA21QOR=&Q?+V@%Y72Q21rS4%432SE1&Q;%Y;2Q35rS5%362Q<QARKSI1&Q:%12SKSF&=%Z81YF&QB%11SF(7%11YJ%XH3531%711(9%XK3YLSA1p031&QD%11SL+XPP0%YD21QM%Y13Z431%>1SH%Y33@1<&Q8%12SKSH%Y63Z71<%:1SG%Z6219+S`PPPP0%X:221&Q7&R6&4&QC%11SO%32ZC1%511&Q9%12T6T3%ZB231%:2T51+`PPPP0%XG221%XI2>1p0C1p0G1&Q=v?rS<&Q3%13R=TETB%53431&QA%11T?%ZG2XOZK%Y4221%Q81TB%Y3231%Y8231rS=%[72TO[0+WJ%T@5UF32T=1p051pW<[@1&R0&1%QL1TG%Q31TH%33[E21%53[F[;1rS>%[92[7[<%[D2U91%TL5V231TI=p051pW6[L1&QE(0%11TL%34S>S@1E&QF%11;%ZO2[5Z4%[O2U1SB%ZB2\=1%[33\=31r4%[421ZGrS@%ZG2\B1%[83\B31r5%[921[4rSB%[<3\F21%\I1\J(3+3%[=3\M1[;%[>3\NZ=[<+9%[@3]01[>+B%[B3]21[@+C%[D3]41[B%[E3]5X1[C+E%[G3]71[E+F%[I3]91[G%[J3]:X1[H+H%[L3]<1[J+I%[N3]>1[L+J%\03]@1[N+K%\23]B1\0%S@1I%I3J21%J3K51%K3L81%L3M;1%M3N>1%N3O@1%O3Q0C1%Q03Q1F1%Q13Q2H1%Q23Q3K1%Q33Q4N1%Q43Q5Q11%Q53Q6[N1%Q63Q7Q41%R73Q8]=1r8%\F21]>rSH%\H21]@%\J3^431p061pV0Q?1&QMrSFr6%3221rSE%Z<21Z>&S=%12^?]L%\5231%\3225%\8221%TF11&Q1+RS0%ZE2=1rS?rS;rS:rSDrS9rS8%?2^M^9%:>87S;SF6V95V@U94UB321%U211r:%11]KrSJ%11]M%]I3^N31p061p0C1pW:_61rS7%S44=1V?Q8%^M2CUG%UI31U6^L%^O2RKUI&Q5&Q4%12VGVE%311%UJ65SBSNVI1A%42VHVE%611%UI2VJ1&Q<&M%11VJ%:2VKVG%T=11%5331W0r<%]A2\I1+X0%]@231%]E231r=%[H21^2%^G3_J1^Cr?%_G2W3Q;%\421_7%Y05Z631XM_=r@%_K2W3Q@+?%\9221%Y55Z;41Y28rA%`02W4U5+>%\>221%Y:5Z@41XG]=%`42W5TN+<%\B221rSM%Y?5ZE]E2X>1%_O2_MW1%`:2W;1%YB5ZH_E1Y?U3%^>2]F`6%^<2`7UB%^A221%`52`3QD%`@2W41%`72`5T=%`B221%`C21`<%YK5[1]H1YH]Np071pU6`K1%_I3`LR<^1%W811%`I27UC%Z15[7]N1YNUOp031%W:1R>%_O3W<1W8%VL2R@RB%`13a21W7+QPP0%_02`K1%_52F1%`I2`GRH%`J2`HRG%a5221rSK%`M271%a821a1%_;241%a:25U1%_:231%_?231%WM11rSL%a52?1%a@2S41%aA21`H%ZI5[O^<1ZFV:p061p0B1pU6aJ1p0G1p0J1%`J3aMU?a7%X911+\hkdfgWVVmUeI%[25\8^KS<ZF1%aL2S=_JrSC%aN2S?1%^;21a>%[75\=_04ZK1%`4261p091rT;rT:%W93GSISJ%VI3bL21&QLvR@rT6rT7%453_62_;1%9261p0;1p0G1p0QD1p0QJ1p0R61p0R:1p0R@1p0RF1p0RL1p0S11p0S51p0S;1p0SB1p0SF1p0SM1p0T01p0T31p0U01p0U51p0VF1p0VK1p0W11pTFc81pQ:c:1pV6c@1'Kv@rSA+_Tk<%b93cG1b7/01cG%Q55Q441W8U2%77]JXC6Q5Q@W41p091p0WB1p0WE1p0WJ1p0X71p0XE1p0XL1p0YF1p0YL1p0Z81p0Z;1p0Z@1p0ZF1p0ZJ1p0ZN1p0[21p0[71p0[<1p0[A1p0[E1p0[H1p0[L1p0\01p0\51p0\;1p0\B1p0\F1p0\L1p0]21p0];1p0]?1p0]E1p0]K1p0^01p0^41p0^81p0^<1p0^D1p0^H1p0^N1p0_51p0_71p0_91p0_<1p0_>1p0_D1p0_J1p0_M1p0`01p0`61p0`<1p0`>1p0`D1p0`J1p0`N1p0a01p0a41p0a61p0a81p0a:1p0a?1p0aD1p0aL1p0b41p0b:1p0bA1p0bF1p0bL1p0c11p0c61p0c91p0c>1p0cB1p0cK1p0d11p0d91p0d@1p0dD1tVBf1dO1tTDf2e:1tW8f3eF1tTLf4eK1pTNf21pU4f41pU8f61pUDf81pUHf91pUJf:1pV>f;1pUNf<1pV@f=1pV:f>1pTJf?1pW0f@1pTHfA1pU>fB1pU<fC1pULfD1pV8fE1pVDfF1pU@fG1pVNfH1pU0fI1pW4fJ1pU:fK1pW2fL1pUFfM1pQ4fN1pT0fO1pV2g71pV<g21pQ<g31pV4g91pUBgD1pQ>gA1")) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 0%nat 0%nat).
Variable log : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 2%nat 0%nat).
Variable M0 : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 3%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 4%nat 0%nat).
Variable raw0 : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 5%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 6%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 7%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 8%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 9%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 10%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 11%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 12%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 13%nat 0%nat).
Variable loff : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 14%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_malloc3_small) 15%nat 0%nat).
Theorem art_malloc3_small : ltac:(sec_stmt2 constr:(SEC_T_art_malloc3_small) 16%nat 0%nat).
Proof using Type Q log regs M0 rom raw0 S HI n tp key tsd ctx t loff spb.
intros ris qs km l2 blk top bot rl rz qz rs qr qn m8 kb inited cl c w ab shb
H1 Hret H2 H4 H10
Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hprim
GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Hloff Hloff' Hloff'' Htpd Htsdd
Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs
W RD0 Wt Wsh RO RZRO L TSD PC Ci Cr Cmax Cmin16 Cmax2048 Chook Cmfs Cfb Cpp Cg Clsan Ctctx Ctid Cctx30 Cfast Cunw C40 Ctop Cbot
PH RC OK Hin Emu Room EV PZ1 PZ2 DI DR K.
assert (Eab : ab = spb + c * 2 ^ 32 + w * 16) by reflexivity.
assert (Eshb : shb = 2147450880 + 8192 * qs + c * 2 ^ 29) by reflexivity.
clearbody ab shb.
pose proof (AsanTab.class_id_ok (rs + rz) ltac:(lia)) as (Hc & Hfit & _). fold c in Hc, Hfit.
pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
assert (At_i : apart t 4096 0x10000 (0x693000 - 0x10000)) by (unfold apart; clear - G9; lia).
assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
assert (Ac_i : apart ctx 4096 0x10000 (0x693000 - 0x10000)) by (unfold apart; clear - G15; lia).
assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G16; lia).
change (hid (t + 4096 <= 0x10000 \/ 0x693000 <= t)) in G9. change (hid (ctx + 4096 <= 0x10000 \/ 0x693000 <= ctx)) in G15.
clear G10 G16.
pose proof OK as (Hl16 & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & _).
assert (Hkm : 0 <= km) by lia. assert (Hkm' : 262144 * km <= 3758096384) by lia.
pose proof DI as (dN & dTF & dST & DG1 & DG2 & DG3 & DG4 & DG5 & DG6 & DG7 & _).
pose proof TSD as (_ & _ & _ & _ & _ & TR).
pose proof PC as (_ & _ & _ & _ & _ & Cpg1 & Cpg2 & _).
destruct (art_icu1 regs M0 rom raw0 S n tp key tsd ctx t top bot H1 H2 H4 H10 ltac:(lia) HS47 ltac:(lia) G7 ltac:(lia) G9 ltac:(unfold apart; lia)
ltac:(unfold apart; lia) G15 G18 G19 G20 G21 G22 ltac:(lia) Htop W Wt TSD Ci Cctx30 ltac:(pose proof L as L'; unfold art_layout in L'; tauto) Cfast Cunw C40 Ctop Cbot)
as (r1 & M1 & RUN1 & Q1_1 & Q1_2 & Q1_10 & Q1_11 & Q1_12 & Q1_13 & Q1_14 & Q1_15 & Q1_24 & Q1_4 & K1 & G01 & A1
& F8 & F16 & F24 & F32 & F40 & F48 & F56 & E36 & E44 & E52 & E60 & E68 & E76 & E84 & E92 & E00 & E08 & E28 & E20 & E16' & W1).
eapply ar_steps; [exact RUN1|].
assert (T1 : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= S - 2272 \/ S <= a) -> (a + Z.of_nat k <= t + 3168 \/ t + 3169 <= a) ->
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
destruct (art_unwind_fast_any r1 M1 rom (0x81910 : bv 64)%bv (S - 2208) (S - 2128) 0x79434 S top bot
Q1_1 ltac:(unfold ret_ok; bveq) Q1_2 Q1_10 Q1_11 Q1_12 Q1_13 Q1_14 Q1_15
ltac:(lia) ltac:(lia) ltac:(lia) Hbot Hbt Htop4 Htop ltac:(lia) HS8 ltac:(lia) ltac:(lia)
ltac:(eapply wr_sub; [exact W1|lia|lia]) ltac:(eapply wr_sub; [exact W1|lia|lia]) (fun _ _ => RD1)
ltac:(apply T1; [lia|cbn; lia|cbn; lia|clear - At_i; unfold apart in At_i; cbn; lia|exact Cpg1]) ltac:(apply T1; [lia|cbn; lia|cbn; lia|clear - At_i; unfold apart in At_i; cbn; lia|exact Cpg2]))
as (r2 & M2 & RUN2 & Q2_2 & Q2_1 & K2 & G12 & A2 & (sz & Hsz & Csz & TRC)).
eapply ar_steps; [exact RUN2|].
assert (T2 : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= S - 2272 \/ S - 2208 <= a) -> (a + Z.of_nat k <= S - 2120 \/ S - 2116 <= a) ->
(a + Z.of_nat k <= S - 2112 \/ S - 1872 <= a) -> cellA M1 a k v -> cellA M2 a k v).
{ intros a k v Ha Hak O1 O2 O3 C. apply (cell_agree M1 M2); [|lia|lia|exact C]. intros x Hx. apply A2; lia. }
pose proof (art_icu2_fn r2 M2 rom S n t (U (getr regs 22)) (U (getr regs 23)) (U (getr regs 24)) Q2_2 ltac:(rewrite K2 by inl; exact Q1_24)
ltac:(lia) HS47 ltac:(lia) G7 ltac:(lia) ltac:(unfold apart; lia) (u64_range _) (u64_range _) (u64_range _)
ltac:(eapply wr_grows; [exact G12|exact W1]) ltac:(eapply wr_grows; [exact G12|]; eapply wr_grows; [exact G01|exact Wt])
ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E36]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E44])
ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E52]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E60])
ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E68]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E76])
ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E84]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E92])
ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E00]) ltac:(apply T2; [lia|cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E08])) as RUN3.
match type of RUN3 with msteps _ _ (mkst ?R _ ?X _) => set (r3 := R) in RUN3; set (M3 := X) in RUN3 end.
eapply ar_steps; [exact RUN3|].
assert (A03 : art_agree [(S - 2272, 2272); (t + 3168, 1)] M0 M3).
{ intros x Hx. cbn [art_out fst snd] in Hx. unfold M3. rewrite 3 Wn_outside by (cbn; clear - Hx G7 G8 G2 HHI G1 HS47; lia). rewrite A2 by (clear - Hx; lia). apply A1; clear - Hx; lia. }
assert (G03 : mem_grows M0 M3). { eapply mem_grows_trans; [exact G01|]. eapply mem_grows_trans; [exact G12|]. unfold M3. zgrows. }
assert (T_img3 : forall a (k : nat) v, 0x10000 <= a -> a + Z.of_nat k <= 0x693000 -> cellA M0 a k v -> cellA M3 a k v).
{ intros a k v Ha Hk C. apply (art_cell_tr1 _ M0 M3 a k v A03); [|exact C]. revert Ha Hk. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris. intros Ha Hk. zarith_f. }
assert (RO3 : art_alloc_rodata M3).
{ unfold art_alloc_rodata in *. destruct RO as (a1 & a2 & a3). repeat split; apply T_img3; first [exact a1|exact a2|exact a3|clear; lia|clear; cbn; lia]. }
assert (RZRO3 : art_rz_rodata M3).
{ unfold art_rz_rodata in *. destruct RZRO as (a1 & a2 & a3). repeat split; apply T_img3; first [exact a1|exact a2|exact a3|clear; lia|clear; cbn; lia]. }
assert (L3 : art_layout M3).
{ eapply art_layout_fp; [exact A03| |exact L]. intros z Hz. apply (art_gap_out _ 0x10000 (0x20e908 - 0x10000)); [|clear - Hz; lia]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
assert (T3 : art_tsd M3 tp key tsd ctx t). { apply (art_tsd_tr _ M0 M3 tp key tsd ctx t A03); [| | | |exact TSD]; clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
assert (PC3 : art_prim_consts spb ris M3).
{ eapply art_prim_consts_fp; [exact A03| |exact PC]. intros z Hz. apply (art_gap_out _ 0x10000 (0x693000 - 0x10000)); [|clear - Hz; lia]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
assert (W3 : wrA M3 (S - 2144 - 1952) 1952) by (eapply wr_grows; [exact G03|]; eapply wr_sub; [exact W|lia|lia]).
assert (Wt3 : wrA M3 t 4096) by (eapply wr_grows; [exact G03|exact Wt]).
assert (Wsh3 : wrA M3 (2147450880 + 8192 * qs) (2 ^ 34)) by (eapply wr_grows; [exact G03|exact Wsh]).
assert (Clsan3 : cellA M3 (tp + loff) 4 0) by (apply T_img3; [clear - Hloff'; lia|clear - Hloff''; cbn; lia|exact Clsan]).
assert (Ctctx3 : cellA M3 t 8 ctx). { apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|exact Ctctx]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
assert (Ctid3 : cellA M3 (ctx + 8) 4 0). { apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|exact Ctid]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
assert (PH3 : art_pc_hdr (t + 208) inited M3).
{ apply (art_pc_hdr_tr _ (t + 208) inited M0 M3 ltac:(clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; lia) ltac:(clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; lia) A03); [|exact PH]. intros c' Hc'. revert Hc'. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris. intros Hc'. zarith_f. }
assert (RC3 : art_cls_rep (t + 208) spb ris c cl M3).
{ apply (art_cls_rep_tr [(S - 2272, 2272); (t + 3168, 1)] (t + 208) spb ris c cl M0 M3); first [ exact RC | exact G03 | exact A03 | exact Hl16 | idtac ];
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
{ apply (DRoD_frame M0 M3 DR). intros x Hx. apply A03. apply (art_gap_out _ 0x10000 (0x20e908 - 0x10000)); [|clear - Hx; lia]. clear - HHI HS47 HS16 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eshb Hau0 Haumu Hmu3 Emu Hmfa1 Hnf4 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hbot Hbt Htop4 Htop; subst shb ris; zarith_f. }
assert (Cstk3 : cellA M3 (S - 2128) 8 (S - 2112)).
{ unfold M3. do 3 (apply cell_Wn_other; [clear - G7 HHI G1; lia|clear - G8 G2 HS47; cbn; lia|clear - HHI G1; lia|clear - HS47; cbn; lia|unfold apart; clear - G8 HHI; cbn; lia|]).
apply T2; [clear - HHI G1; lia|clear - HS47; cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E28]. }
assert (Cszt3 : cellA M3 (S - 2128 + 8) 8 sz).
{ replace (S - 2128 + 8) with (S - 2120) by lia. unfold M3.
do 3 (apply cell_Wn_other; [clear - G7 HHI G1; lia|clear - G8 G2 HS47; cbn; lia|clear - HHI G1; lia|clear - HS47; cbn; lia|unfold apart; clear - G8 HHI; cbn; lia|]).
replace sz with (sz + 0 * 2 ^ 32) by lia. replace (S - 2128 + 8) with (S - 2120) in Csz by lia.
apply cell8_of_cells4; [clear - HHI G1; lia|clear - HS47; lia|clear - Hsz; lia|lia|exact Csz|].
replace (S - 2120 + 4) with (S - 2116) by lia. apply T2; [clear - HHI G1; lia|clear - HS47; cbn; lia|cbn; lia|cbn; lia|cbn; lia|exact E16']. }
assert (DP3 : DPreD blk M3 (S - 2112) sz).
{ unfold DPreD. split; [exact Hsz|]. split.
{ clear - HS8. rewrite <- (Z.div_exact S 8) in HS8 by lia. rewrite HS8. replace (8 * (S / 8) - 2112) with ((S / 8 - 264) * 8) by lia. apply Z_mod_mult. }
split; [clear - HHI G1; lia|]. split; [clear - HS47 Hsz; lia|]. split; [unfold apart; clear - Dblk HHI Hsz; lia|].
intros i Hi. destruct (TRC i Hi) as [w' Cw]. unfold rcell. eexists.
assert (C3' : cellA M3 (S - 2112 + 8 * i) 8 (U w')).
{ unfold M3. do 3 (apply cell_Wn_other; [clear - G7 HHI G1 Hi; lia|clear - G8 G2 HS47 Hi Hsz; cbn; lia|clear - HHI G1 Hi; lia|clear - HS47 Hi Hsz; cbn; lia|unfold apart; clear - G8 HHI Hi Hsz; cbn; lia|]).
replace (S - 2112 + 8 * i) with (S - 2128 + 16 + 8 * i) by lia. exact Cw. }
exact C3'. }
rewrite Eshb in PZ1_3, PZ2_3.
apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
apply (art_allocate3_small EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) log r3 M3 rom (0x51e84 : bv 64)%bv (S - 2144) HI n (S - 2128) tp key tsd ctx t loff spb ris qs km l2 blk
(S - 2112) sz rl rz qz rs qr qn m8 kb inited cl
ltac:(unfold r3; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; rewrite K2 by inl; exact Q1_4)
ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity)
ltac:(unfold r3; gres; reflexivity) ltac:(unfold r3; gres; reflexivity)
Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hprim
GEO ltac:(clear - HHI; lia) ltac:(clear - HHI; lia) ltac:(clear - HS47; lia) ltac:(clear; lia) ltac:(clear; lia)
ltac:(clear - HHI G1 HS47; lia) ltac:(clear - Hsz; lia) ltac:(clear; lia) ltac:(clear - Hsz; lia)
Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs
W3 Wt3 Wsh3 RO3 RZRO3 L3 T3 PC3
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
assert (ABOVE : forall x, S - 2144 <= x -> ~ art_alloc3_fp (S - 2144) t spb ris qs c km ab rz n rs l2 blk x).
{ intros x Hx. apply (art_alloc3_fp_above (S - 2144) HI t spb ris qs c km ab rz n rs l2 blk _ _ x Hc Hkm Hkm' ltac:(clear - HHI; lia) G1 Espb G4 Eris G6 G8 Dl2 Dblk
ltac:(clear - Eab Hc Hw0 Hwsz Haumu' Hmu3' Hfit Hrs; lia) Hub8 Hqr8 ltac:(clear - Hc Hw0 Hwsz Haumu' Hmu3' Hfit Hrs Hqz Ers Erz16 Espb Eris G6 G2 Hcsz; lia) Hx). }
assert (T34 : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> S - 2144 <= a -> cellA M3 a k v -> cellA M4 a k v).
{ intros a k v Ha Hak O1 C. apply (art_cell_agree _ M3 M4); [|exact Ha|exact Hak|exact C]. intros x Hx. apply AG34. apply ABOVE. clear - Hx O1. lia. }
assert (TF : forall a v, S - 56 <= a -> a + 8 <= S -> cellA M1 a 8 v -> cellA M4 a 8 v).
{ intros a v Ha Ha' C. apply T34; [clear - Ha HHI G1; lia|clear - Ha' HS47; cbn; lia|clear - Ha; lia|]. unfold M3.
do 3 (apply cell_Wn_other; [clear - G7 HHI G1 Ha; lia|clear - G8 G2 HS47 Ha'; cbn; lia|clear - HHI G1 Ha; lia|clear - HS47 Ha'; cbn; lia|unfold apart; clear - G8 HHI Ha Ha'; cbn; lia|]).
apply T2; [clear - HHI G1 Ha; lia|clear - HS47 Ha'; cbn; lia|clear - Ha; cbn; lia|clear - Ha; cbn; lia|clear - Ha; cbn; lia|exact C]. }
pose proof (art_ic3_fn r4 M4 rom raw0 S (ab + rz) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))
P4_2 P4_10 ltac:(clear - Eab Espb G4 Hc Hw0 Hwsz Haumu' Hmu3' Hqz Erz16 Eris G6 G2 Hcsz; lia) ltac:(clear - HHI G1; lia) HS47 Hret
(u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
ltac:(apply T34; [clear - HHI G1; lia|clear - HS47; cbn; lia|clear; lia| unfold M3; clear - HHI G1 HS47 G7 G8 G2; zcell])
ltac:(apply T34; [clear - HHI G1; lia|clear - HS47; cbn; lia|clear; lia| unfold M3; clear - HHI G1 HS47 G7 G8 G2; zcell])
ltac:(apply TF; [clear; lia|clear; lia|exact F8]) ltac:(apply TF; [clear; lia|clear; lia|exact F16]) ltac:(apply TF; [clear; lia|clear; lia|exact F24])
ltac:(apply TF; [clear; lia|clear; lia|exact F32]) ltac:(apply TF; [clear; lia|clear; lia|exact F40]) ltac:(apply TF; [clear; lia|clear; lia|exact F48])
ltac:(apply TF; [clear; lia|clear; lia|exact F56])) as RUN5.
eapply ar_steps; [exact RUN5|]. apply ar_done.
apply (K _ M4 b1).
- gres. exact P4_10.
- gres. reflexivity.
- gres. reflexivity.
- intros r Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; try apply Z_to_bv_bv_unsigned;
rewrite K4 by inl; unfold r3; gres; try apply Z_to_bv_bv_unsigned; rewrite K2 by inl; first [ rewrite K1 by inl; reflexivity | rewrite Q1_4; symmetry; exact H4 ].
- eapply mem_grows_trans; [exact G03|exact G34].
- intros x N1 N2. rewrite (AG34 x N2).
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
