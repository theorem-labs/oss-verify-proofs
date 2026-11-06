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
JbtCls JbtFp JbtClsPop3 JbtClsRep JbtClsGfa2 JbtClsRefill JbtCellEx JbtCARSpec JbtAlloc3Pure JbtDepotA JbtDepot JbtAllocPre3 JbtAllocPost JbtAllocPostS JbtAllocate3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtAllocate3S () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocate3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCARSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtDepot."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRzLog."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1S"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2not"; "3Z"; "0EVOK"]; ["0GR"; "0HI"; "4machine_state"; "5bvmap"; "0M'"; "0M0"; "0Q"; "6apart"; "6cell"; "6wr"; "7aev"; "7aruns"; "8class_id"; "8class_size"; "8rz_log"; "9ret_ok"]; [":art_alloc_rodata"; ";art_alloc3_fp"; "<art_ca_cptr"; "<art_ca_events"; "<art_ca_pre"; "<art_cls_pop"; "=art_cls"; "=art_cls_mfa'"; "=art_cls_needs_populate"; "=art_cls_new"; "=art_cls_ok"; "=art_cls_rep"; "=art_cptr_ok"; "=art_evok_list"; "=art_geo"; "=art_pc_hdr"]; ["=art_prim_consts"; "=cl_au"; "=cl_cache"; "=cl_free"; "=cl_mu"; ">DInvD"; ">DPreD"; ">DRoD"; "?art_tsd"; "@art_layout"; "Aart_rz_rodata"; "Bgetr"; "Bmkst"; "Cmem_grows"; "Dloaded_segments"; "EIn"]; ["Fadd"; "Fle"; "Flt"; "Fmodulo"; "Fmul"; "Fof_nat"; "Fpow"; "Fsub"; "0ab"; "0b1"; "0blk"; "0c"; "0cl"; "0ctx"; "0fx"; "0inited"]; ["0j"; "0kb"; "0key"; "0km"; "0l2"; "0loff"; "0log"; "0m8"; "0n"; "0qn"; "0qr"; "0qs"; "0qz"; "0r"; "0raw"; "0regs"]; ["0regs'"; "0ris"; "0rl"; "0rom"; "0rs"; "0rz"; "0shb"; "0sp"; "0spb"; "GBV"; "GZ_to_bv"; "Gbv"; "Gbv_unsigned"; "0stk"; "0szt"; "0t"]; ["0tp"; "0trp"; "0tsd"; "0v"; "0w"; "0x"; "0y"]]).
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
Local Abbreviation SEC_T_art_allocate3_small := (ltac2:(TCodec.tc2 tcn__JbtAllocate3S "h9'5'J%211'B!p021p041&Cy5'S;yR0%211%5241'8y8%611%311p061'>'6'2'Q6&L&R0r7r9%3221%511&Q2r1r2%3221rD&R4&R6+2+Q0%3221%5281%@271+@%82<1%C231+QoooPP0+XP0rC%=221%H241r3+M%@2?1%B231%M251'<&QKrQ4(S9+1(:%33QC21%6251rQ1%93QC21&OrQ2%211rQ6%;3QKQ09%>221&S:%12QL6%B3QL31rQ7+4%B3R21@%E231rO%82R31%I3R331rQ8+:%I3R91G%L231+QWTnH%?2R:1%Q03R:31rQ9+;%Q03R@1N%Q3231rQ3%F2RA1%Q73RA31rQ:+<%Q73RG1Q5%Q:231+8%M2RH1%Q>3RH31rQ;+=%Q>3RN1Q<%QA231%Q32RNQA%QD3RN21rQ<+>%QD3S41QB%QG231%Q92S4QE%QJ3S421rQ=+?%QJ3S:1QH%QM231%QO3S916';&R1%12QNQ8&R2%12Q:H%5231rI&N%11Q7%R93S<31rJ%RN2RM1%S02RI1%R=3S@71%S22RK8%R?3SB51%?2R<6+T0%A281%C231rH%S92Q91rG%SE221%RH3SKM1z%I216+7%K281%M231rLrK%SD2QD1%S13T431rQ@rM%Q3221%T323:%Q5231%Q7231rNrQ0%T8221+RPP0%Q;221&Q>rQCrQ>%382QKQE>1R8R?RFrQD&R7rQE+Qm0%3221%QE251+TP0%TF251rQF%QI221rQG+RS0%TK221+Q?%TB2TA1%QO231rQH%R121?%U12:T@rQI%U321>%R5231%R62Q>RO+R0%TL2TK1%R72S21%R;241rQL%R<21RH%U22S2RI%U=2RD1rQM%U?21J%RA231%RB2QJQ0rQK%UC21L%RE2Q;1%UE2;L%UF21T4+Vb\P0%RI221+V[jY8+RH%Q;2=1%RM231%RN24C+D%UD2UC1%V02Q?1rR2%S3221+G%UI2UH1%V52QD1rR3%S8221&G%14Q@:KQDrQO%34Q<<1QF+Q5%V22V11%V>21QI%74Q=@Q11rQJ+QoonlP0+`PQoooPP0%R3212%<44E31rR1%>46B1R1%?4Q5CAR2%@4Q>D3:%A4Q;E86&I&QNrR@rR=%R>21R<%54431R=rRArR6%84721R=rRB%VJ2V?N%W52VA1+Q2%VL2VK1%>4=531&Q0rRC%211&QJrRD%211&QIrRE%211&QHrRFrR?rR>rR<rR;%66543K21&Q@rR:rR9rRG%43321&HrRH+QWehHu1%45Q7321W0rRI+QgkU2%75Q:214T>rRJ+Sa0%X82V<1u8+Q8%X02WO1%>5QA6431rRK+Sa8%X?2VC1u2%C5QF421X0rRL+Sa:%XD2VH1+RP0%H5QK4261rRM+QiiX0%K5QN21@U2rRN+QWXaH+Q<%XM221u4%Q15R4521T:rRO+QD%Y2271+UN%Q65R94261rS0+RE%Y72<1%Q:5R=31Q7X6rS1+QVdP0%Q=5R@21Q2QKrS2%Y=2Q0QJ%Q@5RC21@UGrS3%QB5RE1QAQ7Q=rS4%YB2Q<W8%QE5RH21EULrS5%QG5RJ1EQ<RBrS6%YG2BW=%QJ5RM21Q?RE&Q?+V@%YK2Q91rS7%432R31&Q;%YO2Q85rS8%362QDQKR6R71&Q:%12R9R<&=%ZL1Z:&QB%11RA(7%11Z>%Y<3531%711(9%Y?3Z@RH1p031&QD%11SC+XPP0%Z821R5%YE3ZH31%>1RO%YG3@1<&Q8%12S2S3%YJ3ZK1<%:1SM%ZJ219+S`PPPP0%WM221&Q7&R5&4&QC%11T5%32[71%511&Q9%12SAT9%[6231%:2T;1+`PPPP0%X:221%X<2>1p0C1p0G1&Q=v?rS?&Q3%13R<SLSM%53431&QA%11TD%[;2Y;[?%XG221%Q81TG%XG231%XK231rS@%[K2T6[D+WJ%SO5U232SL1p051pW>\41&QO&1%QL1TO%Q31U0%33\921%53\:[O1rSA%[M2[K\0%\82TD1%T;5U>31T8=p051pW8\@1&QE(0%11U1%34S?SE1E&QF%14SA;SGSJ&QGrSB%211%[F2[LZK%\F2U6SA%[92]41%[J3]431r4%[K21[>rSD%[>2]91%[O3]931r5%\021[KrSF%\33]=21%]@1]A(3+3%\43]D1\2%\53]EZL\3+9%\73]G1\5+B%\93]I1\7+C%\;3]K1\9%\<3]LW?\:+E%\>3]N1\<+F%\@3^01\>%\A3^1W?\?+H%\C3^31\A+I%\E3^51\C+J%\G3^71\E+K%\I3^91\G%SC1I%I3J21%J3K51%K3L81%L3M;1%M3N>1%N3O@1%O3Q0C1%Q03Q1F1%Q13Q2H1%Q23Q3K1%Q33Q4N1%Q43Q5Q11%Q53Q6\E1%Q63Q7Q41%R:3Q8^41r8%]=21^5rSL%]?21^7%]A3^K31p061pULQ?1&QMrSJr6%3221&Q1rSIrS>rS=rS<rSGrS;rS:&S<%12_<^I%:>9RJSA87V96VCU:5U?431%TM11%_01^KrSM%11^M%^73_<31p051pW<_C1%RL4<;V3M%_92RFU?%UA31TN_8rSC%_<21UB&Q5&Q4%12V?V:%311r:%UD66S<SHVB21%52V>V:%711%UC2V@1&Q<&M%11V?%;2V@V=%T711%5331VFr<%\N2\61+X0%\N231%]2231&R3r=%221^A%_63`91_2r?%`62VJQ=%[G21_F%X:5Y=31X7_Lr@%`:2VKQB%[K21]A%X>5YA31X;7rA%`>2VMTO%[O21]K%XB5YE31X0\IrB%`B2VNTH%\321^<rT1%XG5YJ42WG1%`<2`:VJ%`G2W31%XJ5YM`21XGTL%]J2]2`C%]I2`DU;%]M221rF%`C2`AR0%`N2VN1%`E2`CQD%a0221%a121`J%Y45Z761Y1];p081pU2a91%`73a:R=]>%W211%a727U=%Y:5Z=<1Y7UIp031%W41R@%`=3W61W2%VF2RBRC%`?3a@1W1+QPP0%^>2a91%^B2G1%a72a5RI%a82a6RG%aC221rSN%a;271%aF21a?%^H241rSE%aI261%^I241%^M241%WH11rSO%aD2@1%aO2S61%b021a7%Z35[6^41Z0V5p061p0C1pU2b91p0H1p0K1%a93b<?aF%X411+\hkdfgWVVmUeI%Z<5[?^HS>Z11%b;2S?`1%b<2S@U<%]M21aL%Z@5[C^L3Z51%_A251p081rT?rT>%W33FSJSK%VC3c:21&QLvR>rT:rT;%453_E2_71%9261p0;1p0F1p0QD1p0QJ1p0R71p0R;1p0RA1p0RF1p0RK1p0S01p0S51p0S;1p0SB1p0SF1p0SO1p0T21p0T41p0TG1p0TL1p0V=1p0VB1p0VH1pTDcF1pQ:cH1pV2cN1'Kv@+ZWeD%bF3d41bD/01d4%Q45Q3R11VNT>%67\OX<5Q4TOVJ1p081p0W81p0W<1p0W?1p0WD1p0X11p0X?1p0XF1p0Y@1p0YF1p0Z21p0Z51p0Z:1p0Z@1p0ZD1p0ZG1p0ZK1p0ZN1p0[21p0[61p0[;1p0[A1p0[H1p0[L1p0\21p0\81p0\@1p0\D1p0\J1p0]01p0]81p0]<1p0]@1p0]D1p0]K1p0]O1p0^61p0^81p0^:1p0^<1p0^?1p0^E1p0^J1p0^M1p0_01p0_61p0_<1p0_>1p0_C1p0_H1p0_L1p0_N1p0`41p0`71p0`81p0`>1p0`C1p0`F1p0`M1p0a21p0a91p0a>1p0aD1p0aK1p0b01p0b61p0b<1p0bA1p0bD1p0bI1p0bN1p0c51p0c;1p0cB1p0cI1p0d11p0d91p0dA1p0dI1p0e01p0e41tV>fAe?1tTBfBeJ1tW:fCf61tTHfDf;1pTJfB1pU0fD1pU4fF1pU@fH1pUDfI1pUFfJ1pV:fK1pUJfL1pV<fM1pV6fN1pVNfO1pW4g01pTFg11pU:g21pU8g31pUHg41pV4g51pVBg61pU<g71pW0g81pTLg91pW6g:1pU6g;1pW2g<1pVLg=1pUBg>1pQ4g?1pV@g@1pUNgH1pV8gC1pQ<gD1pV0gJ1pU>h51pQ>h21")) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 0%nat 0%nat).
Variable log : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 1%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 2%nat 0%nat).
Variable M0 : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 3%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 4%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 5%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 6%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 7%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 8%nat 0%nat).
Variable stk : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 9%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 10%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 11%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 12%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 13%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 14%nat 0%nat).
Variable loff : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 15%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_allocate3_small) 16%nat 0%nat).
Theorem art_allocate3_small : ltac:(sec_stmt2 constr:(SEC_T_art_allocate3_small) 17%nat 0%nat).
Proof using Type Q log regs M0 rom raw sp HI n stk tp key tsd ctx t loff spb.
intros ris qs km l2 blk trp szt rl rz qz rs qr qn m8 kb inited cl c w ab shb
H1 Hret H2 H4 H10 H11 H12 H13 H14 H15
Hn Erl Erz Erz16 Hqz En Hm8 Ers Hrs Hprim
GEO HHI HHI' Hsp' Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd
Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs
W Wt Wsh RO RZRO L TSD PC Ci Cr Cmax Cmin16 Cmax2048 Chook Cmfs Cfb Cpp Cg Clsan Ctctx Ctid Ctrp Cszt
PH RC OK Hin Emu Room EV PZ1 PZ2 DI DP DR K.
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
assert (Hkm : 0 <= km) by lia.
assert (Hkm' : 262144 * km <= 3758096384) by lia.
pose proof DI as (dN & dTF & dST & DG1 & DG2 & DG3 & DG4 & DG5 & DG6 & DG7 & _).
pose proof TSD as (_ & _ & _ & _ & _ & TR).
assert (Ers8 : rs = 8) by lia.
assert (Ers_max : rs = (Z.max n 8 + 7) / 8 * 8) by (rewrite Z.max_r by lia; rewrite Ers8; reflexivity).
destruct (art_allocate_pre3a regs M0 rom raw sp 1283032 n stk tp key tsd ctx t rl rs qr rz qz
H1 H2 H4 H10 H11 H12 H13 H14 H15 ltac:(lia) Erl Erz Erz16 Hqz
Ers_max Ers ltac:(rewrite Z.max_r by lia; lia) Hprim
ltac:(lia) Hsp' Hstk Hstk' ltac:(lia) ltac:(lia)
G7 ltac:(lia) G9 ltac:(unfold apart; lia) ltac:(unfold apart; lia) G15 G18 G19 G20 G21 G22
W RO RZRO TSD Ci Cr Cmax Cmin16 Cmax2048)
as (r5 & M5 & RUN5 & P5_1 & P5_2 & P5_4 & P5_8 & P5_9 & P5_10 & P5_11 & P5_12 & P5_13 & P5_19 & P5_20 & P5_21 & P5_22 & P5_23 & P5_25 & P5_26 & P5_27 & P5_3
& G05 & AG05 & F120 & F112 & F104 & F96 & F88 & F80 & F72 & F64 & F56 & F48 & F40 & F32 & F24 & F8 & F16).
eapply ar_steps; [exact RUN5|].
assert (A05 : art_agree [(sp - 144, 144)] M0 M5). { intros x Hx. apply AG05. cbn in Hx. lia. }
assert (W5 : wrA M5 (sp - 128 - 720) 720) by (eapply wr_grows; [exact G05|]; eapply wr_sub; [exact W|lia|lia]).
assert (Wt5 : wrA M5 t 4096) by (eapply wr_grows; [exact G05|exact Wt]).
assert (Wsh5 : wrA M5 (2147450880 + 8192 * qs) (2 ^ 34)) by (eapply wr_grows; [exact G05|exact Wsh]).
assert (PC5 : art_prim_consts spb ris M5). { eapply art_prim_consts_fp; [exact A05| |exact PC]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
assert (L5 : art_layout M5). { eapply art_layout_fp; [exact A05| |exact L]. intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia. }
assert (T5 : art_tsd M5 tp key tsd ctx t).
{ eapply art_tsd_fp; [exact A05| | |exact G19|exact G20|exact G21|exact G22|exact TSD].
- intros z Hz. cbn. clear - Hz HHI G1. repeat split; lia.
- intros z Hz. cbn. clear - Hz HHI G1 G13 G14. repeat split; lia. }
assert (PH5 : art_pc_hdr (t + 208) inited M5).
{ apply (art_pc_hdr_tr _ (t + 208) inited M0 M5 ltac:(lia) ltac:(lia) A05); [|exact PH]. intros c' Hc'. clear - Hc' HHI G7 G8. zarith_f. }
assert (RC5 : art_cls_rep (t + 208) spb ris c cl M5).
{ apply (art_cls_rep_tr [(sp - 144, 144)] (t + 208) spb ris c cl M0 M5); first [ exact RC | exact G05 | exact A05 | exact Hl16 | lia | idtac ];
clear - Hc HHI Hsp' G1 G2 G6 Eris G4 Espb G7 G8 Hnf4 Hmfa1; zarith_f. }
assert (Hs8 : (rs + rz) mod 8 = 0). { rewrite Ers, Erz16. replace (8 * qr + 16 * qz) with ((qr + 2 * qz) * 8) by lia. apply Z_mod_mult. }
apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg st H; exact H].
apply (art_ca_rspec_holds EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) log r5 M5 rom (0x52154 : bv 64)%bv (sp - 128) HI t ctx tp key tsd spb ris qs (rs + rz) km inited cl
P5_1 ltac:(unfold ret_ok; bveq) P5_2 P5_4 P5_10 P5_11 P5_12 P5_13 ltac:(lia) Hs8 ltac:(lia) ltac:(lia) GEO W5 Wt5 PC5 L5 T5 PH5 RC5 OK Hin Emu).
{ intros E1 E2. destruct (Room E1 E2) as (R1 & R2). split; [exact R1|]. split; [exact R2|].
split; (eapply wr_sub; [exact Wsh5| |]); clear - Hc Hkm R1 Emu; lia. }
{ exact EV. }
intros r6 M6 R10 R2 R1 RK G56 RA RPH RCR ROK RCP RSH.
fold c in R10, RA, RCR, ROK, RCP, RSH. fold w in R10, RCP.
set (clp := art_ca_pre c cl) in *.
assert (R6_10 : getr r6 10 = Z_to_bv 64 ab) by (rewrite Eab; exact R10).
pose proof (art_class_size_facts c Hc) as (Hsz & Hsz16). set (sz := AsanTab.class_size c) in *.
pose proof RCP as (Hw0 & Hwsz & _).
pose proof ROK as OK'. unfold art_cls_ok in OK'. cbn [art_cls_pop cl_cache cl_free cl_au cl_mu cl_mfa] in OK'.
destruct OK' as (Hl16' & (Hau0' & Haumu') & _ & _ & _ & Hmu3' & _ & (_ & Hmfa1') & Hnf4' & _).
set (au' := cl_au clp) in *. set (mu' := cl_mu clp) in *.
destruct RCR as [CR6 RR6]. pose proof RR6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wu6).
cbn [art_cls_pop cl_mu] in Wu6. fold mu' in Wu6.
assert (A56 : art_agree (art_ca_W (sp - 128) t spb ris qs c km) M5 M6) by (apply art_ca_fp_agree; [exact Hc|exact RA]).
unfold art_ca_W in A56.
assert (G06 : mem_grows M0 M6) by (eapply mem_grows_trans; [exact G05|exact G56]).
assert (Hab16 : ab mod 16 = 0). { rewrite Eab, Espb. replace (65536 * qs + c * 2 ^ 32 + w * 16) with ((4096 * qs + c * 2 ^ 28 + w) * 16) by lia. apply Z_mod_mult. }
assert (Hrz16 : rz mod 16 = 0). { rewrite Erz16, Z.mul_comm. apply Z_mod_mult. }
assert (Hab8 : ab / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w). { rewrite Eab, Espb. replace (65536 * qs + c * 2 ^ 32 + w * 16) with ((8192 * qs + c * 2 ^ 29 + 2 * w) * 8) by lia. apply Z.div_mul. lia. }
assert (Hub8 : (ab + rz) / 8 = 8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz). { rewrite Eab, Espb, Erz16. replace (65536 * qs + c * 2 ^ 32 + w * 16 + 16 * qz) with ((8192 * qs + c * 2 ^ 29 + 2 * w + 2 * qz) * 8) by lia. apply Z.div_mul. lia. }
assert (Hqr8 : rs / 8 = qr). { rewrite Ers, Z.mul_comm. apply Z.div_mul. lia. }
assert (SAB6 : cellA M6 (shb + 2 * w) 1 250).
{ assert (OLD : 16 * w < cl_mu cl -> cellA M0 (shb + 2 * w) 1 250 -> cellA M6 (shb + 2 * w) 1 250).
{ intros Hold C0. apply (art_cell_tr1 _ M5 M6 _ _ _ A56); [|apply (art_cell_tr1 _ M0 M5 _ _ _ A05); [|exact C0]].
- clear - Hold Emu HHI G1 G2 G4 G6 Espb Eris At_s Eshb Hc Hkm Hw0 Hmu3. zarith_f.
- clear - HHI G1 G2 G4 G6 Espb Eris Eshb Hc Hw0 Hold Hmu3. zarith_f. }
pose proof (art_ca_cptr_origin c cl Hc OK) as ORG. fold w in ORG. destruct ORG as [Hold|(Ecache & NP & Hauw)].
- apply OLD; [|apply PZ2; exact Hold].
pose proof (proj1 (Forall_forall _ _) Hfor w Hold) as (_ & Ho & _). fold sz in Ho. clear - Ho Haumu Hsz. lia.
- destruct (Z_lt_ge_dec (16 * w) (cl_mu cl)) as [Hlo|Hhi].
+ apply OLD; [exact Hlo|]. apply PZ1. clear - Hauw Hlo. lia.
+ pose proof (art_ca_pre_mu_pop c cl Ecache NP) as Emu'. fold clp in Emu'. fold mu' in Emu'.
pose proof (RSH Ecache NP (2 * w - 32768 * km) ltac:(clear - Hhi Emu Hwsz Haumu' Emu' Hsz; lia)) as C6.
replace (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + (2 * w - 32768 * km)) with (shb + 2 * w) in C6 by (clear - Eshb; lia). exact C6. }
assert (Wc6 : wrA M6 ab (rs + rz)). { eapply wr_sub; [exact Wu6| |]; clear - Eab Hw0 Hwsz Haumu' Hfit; lia. }
destruct (art_cell_exists_b M6 (ab + rz - 15) 1 ltac:(lia) ltac:(right; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia)
ltac:(eapply wr_sub; [exact Wc6| |]; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia)) as (ob & Hob & Cob).
change (2 ^ (8 * Z.of_nat 1)) with 256 in Hob.
assert (R6_9 : getr r6 9 = Z_to_bv 64 n) by (rewrite RK by inl; exact P5_9).
assert (R6_19 : getr r6 19 = Z_to_bv 64 (rs + rz)) by (rewrite RK by inl; exact P5_19).
assert (R6_20 : getr r6 20 = Z_to_bv 64 rz) by (rewrite RK by inl; exact P5_20).
assert (R6_21 : getr r6 21 = Z_to_bv 64 n) by (rewrite RK by inl; exact P5_21).
assert (R6_23 : getr r6 23 = Z_to_bv 64 stk) by (rewrite RK by inl; exact P5_23).
assert (R6_25 : getr r6 25 = Z_to_bv 64 7) by (rewrite RK by inl; exact P5_25).
assert (R6_26 : getr r6 26 = Z_to_bv 64 t) by (rewrite RK by inl; exact P5_26).
assert (R6_27 : getr r6 27 = Z_to_bv 64 1) by (rewrite RK by inl; exact P5_27).
assert (R6_4 : getr r6 4 = Z_to_bv 64 tp) by (rewrite RK by inl; exact P5_4).
assert (R6_8 : getr r6 8 = Z_to_bv 64 1) by (rewrite RK by inl; exact P5_8).
assert (R6_3 : getr r6 3 = getr regs 3) by (rewrite RK by inl; exact P5_3).
assert (F16_6 : cellA M6 (sp - 128 + 16) 8 16) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
assert (Ctctx6 : cellA M6 t 8 ctx) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
assert (Ctid6 : cellA M6 (ctx + 8) 4 0) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
assert (Ctrp6 : cellA M6 stk 8 trp) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
assert (Cszt6 : cellA M6 (stk + 8) 8 szt) by (ztr_c ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris)).
pose proof (art_alloc_b_fn r6 M6 rom (sp - 128) ab n rs rz stk t ctx ob trp szt R2 R6_10 R6_9 R6_19 R6_20 R6_21 R6_23 R6_25 R6_26 R6_27
ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Hab16 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Ers_max ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Hrz16 Hprim
ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) G13 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Hob Htrp Hszt
ltac:(eapply wr_sub; [exact Wc6| |]; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia)
Cob F16_6 Ctctx6 Ctid6 Ctrp6 Cszt6
ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f)) as RUN7.
match type of RUN7 with msteps _ _ (mkst ?R _ ?MM _) => set (R7 := R) in RUN7; set (M7 := MM) in RUN7 end.
eapply ar_steps; [exact RUN7|].
assert (A67 : art_agree [(ab + rz - 16, 16)] M6 M7).
{ unfold M7, art_alloc_memB. clear - Eab Espb G4 G2 G6 Eris Hc Hw0 Hwsz Haumu' Hmu3' Hsz Hqz Erz16. eapply art_agree_sub; [zagree|]. zsub_c ltac:(clear). }
assert (G67 : mem_grows M6 M7) by (unfold M7, art_alloc_memB; zgrows).
assert (Hn32 : n / 2 ^ 32 = 0) by (apply Z.div_small; clear - Hn Hrs Hprim Hqz Erz16; lia).
pose proof (art_hdr_b1a_range ob Hob) as Hb1a. pose proof (art_hdr_b1_range ob Hob) as Hb1.
assert (B7 : cellA M7 (ab + rz - 15) 1 (art_hdr_b1 ob) /\ cellA M7 (ab + rz - 12) 4 n /\ cellA M7 (ab + rz - 14) 2 0).
{ unfold M7, art_alloc_memB. rewrite Hn32. clear - Hb1a Hb1 Eab Espb G4 G2 G6 Eris Hc Hw0 Hwsz Haumu' Hmu3' Hsz Hqz Erz16 Hn Hprim Hrs. repeat split; zcell. }
destruct B7 as (B7a & B7b & B7c).
assert (G07 : mem_grows M0 M7) by (eapply mem_grows_trans; [exact G06|exact G67]).
pose proof (art_agree_trans _ _ _ _ _ A05 (art_agree_trans _ _ _ _ _ A56 A67)) as A07.
assert (DO7 : forall z, dprivD l2 blk z -> art_out ([(sp - 144, 144)] ++ [(sp - 128 - 720, 720); (t + 208, 2592); (t + 2872, 16); (ris + 128 * c, 128); (spb + c * 2 ^ 32 + 262144 * km, 262144);
(spb + c * 2 ^ 32 + 3758096384, 536870912); (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km, 32768);
(2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048, 67108864)] ++ [(ab + rz - 16, 16)]) z).
{ apply art_dpriv_out; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (DI7 : DInvD l2 blk (S kb) M7). { apply (DInvD_frame l2 blk (S kb) M0 M7 DI). intros x Dx. apply A07. apply DO7. exact Dx. }
assert (DP7 : DPreD blk M7 trp szt).
{ apply (DPreD_frame blk M0 M7 trp szt DP). intros x Hx. apply A07. apply (art_gap_out _ trp (8 * szt)); [|exact Hx]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (DR7 : DRoD M7).
{ apply (DRoD_frame M0 M7 DR). intros x Hx. apply A07. apply (art_gap_out _ 0x10000 (0x20e908 - 0x10000)); [|clear - Hx; lia]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (W7 : wrA M7 (sp - 128 - 224) 224) by (eapply wr_grows; [exact G07|]; eapply wr_sub; [exact W|lia|lia]).
assert (ND7 : nodp (dprivD l2 blk) (sp - 128 - 224) 224). { intros i Hi D. unfold dprivD in D. clear - Hi D HHI G1 Dl2 Dblk. lia. }
pose proof (art_depot_spec_holds l2 blk) as DEPOT. unfold art_depot_spec in DEPOT.
destruct (DEPOT kb R7 M7 rom (0x52260 : bv 64)%bv (sp - 128) trp szt ltac:(unfold R7; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold R7; gres; exact R2)
ltac:(unfold R7; gres; reflexivity) ltac:(unfold R7; gres; reflexivity) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) W7 ND7 DI7 DP7 DR7)
as (r8 & M8 & id & RUN8 & P8_10 & Hid & K8 & G78 & AGd & DI8).
clear DEPOT A07 DO7.
eapply ar_steps; [exact RUN8|].
assert (A78 : art_agree [(0x20e908, 0x65e928 - 0x20e908); (l2, 2 ^ 20); (blk, 2 ^ 23); (sp - 128 - 224, 224)] M7 M8).
{ intros x Hx. cbn [art_out fst snd] in Hx. apply AGd; [unfold dprivD; clear - Hx; lia | clear - Hx; lia]. }
pose proof (art_agree_trans _ _ _ _ _ A67 A78) as A68.
pose proof (art_agree_trans _ _ _ _ _ A56 A68) as A58.
pose proof (art_agree_trans _ _ _ _ _ A05 A58) as A08.
assert (G08 : mem_grows M0 M8) by (eapply mem_grows_trans; [exact G07|exact G78]).
assert (T_img : forall a (k : nat) v, 0x10000 <= a -> a + Z.of_nat k <= 0x20e908 -> cellA M0 a k v -> cellA M8 a k v).
{ intros a k v Ha Hk C. apply (art_cell_tr1 _ M0 M8 a k v A08); [|exact C]. revert Ha Hk. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris. intros Ha Hk. zarith_f. }
assert (T_frm : forall a (k : nat) v, sp - 128 <= a -> a + Z.of_nat k <= sp -> cellA M5 a k v -> cellA M8 a k v).
{ intros a k v Ha Hk C. apply (art_cell_tr1 _ M5 M8 a k v A58); [|exact C]. revert Ha Hk. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris. intros Ha Hk. zarith_f. }
assert (W8 : wrA M8 (sp - 1952) 1952) by (eapply wr_grows; [exact G08|exact W]).
assert (Wc8 : wrA M8 ab (rs + rz)) by (eapply wr_grows; [exact G78|]; eapply wr_grows; [exact G67|exact Wc6]).
assert (Wsh8 : wrA M8 (0x7fff8000 + ab / 8) 8192). { eapply wr_grows; [exact G08|]. eapply wr_sub; [exact Wsh| |]; rewrite Hab8; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia. }
assert (Wt8 : wrA M8 t 4096) by (eapply wr_grows; [exact G08|exact Wt]).
assert (L8 : art_layout M8).
{ eapply art_layout_fp; [exact A08| |exact L]. intros z Hz. apply (art_gap_out _ 0x10000 (0x20e908 - 0x10000)); [|clear - Hz; lia]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (T8 : art_tsd M8 tp key tsd ctx t). { apply (art_tsd_tr _ M0 M8 tp key tsd ctx t A08); [| | | |exact TSD]; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (SAB8 : cellA M8 (0x7fff8000 + ab / 8) 1 250).
{ rewrite Hab8. replace (0x7fff8000 + (8192 * qs + c * 2 ^ 29 + 2 * w)) with (shb + 2 * w) by (clear - Eshb; lia).
apply (art_cell_tr1 _ M6 M8 _ _ _ A68); [|exact SAB6]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (Clsan8 : cellA M8 (tp + loff) 4 0). { apply (art_cell_tr1 _ M0 M8 _ _ _ A08); [|exact Clsan]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (RO3 : cellA M0 0x10358 8 0xcc6e96b9cc6e96b9) by (unfold art_alloc_rodata in RO; tauto).
destruct (art_tcell_exists M8 t 2800 At_i G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(lia) ltac:(lia) Wt8) as (mc & Hmc & Cmc).
destruct (art_tcell_exists M8 t 2808 At_i G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(lia) ltac:(lia) Wt8) as (mb & Hmb & Cmb).
destruct (art_tcell_exists M8 t 2816 At_i G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(lia) ltac:(lia) Wt8) as (mr & Hmr & Cmr).
destruct (art_tcell_exists M8 t (2912 + 8 * c) At_i G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - Hc; lia) ltac:(clear - Hc; lia) Wt8) as (mbs & Hmbs & Cmbs).
replace (t + 2808) with (t + 2800 + 8) in Cmb by (clear; lia). replace (t + 2816) with (t + 2800 + 16) in Cmr by (clear; lia).
replace (t + (2912 + 8 * c)) with (t + 2800 + 112 + 8 * c) in Cmbs by (clear; lia).
assert (B8a : cellA M8 (ab + rz - 15) 1 (art_hdr_b1 ob)). { apply (art_cell_tr1 _ M7 M8 _ _ _ A78); [|exact B7a]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (B8b : cellA M8 (ab + rz - 12) 4 n). { apply (art_cell_tr1 _ M7 M8 _ _ _ A78); [|exact B7b]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (B8c : cellA M8 (ab + rz - 14) 2 0). { apply (art_cell_tr1 _ M7 M8 _ _ _ A78); [|exact B7c]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f. }
assert (R8_2 : getr r8 2 = Z_to_bv 64 (sp - 128)) by (rewrite K8 by dk8; unfold R7; gres; exact R2).
assert (R8_3 : getr r8 3 = getr regs 3) by (rewrite K8 by dk8; unfold R7; gres; exact R6_3).
assert (R8_4 : getr r8 4 = Z_to_bv 64 tp) by (rewrite K8 by dk8; unfold R7; gres; exact R6_4).
assert (R8_8 : getr r8 8 = Z_to_bv 64 1) by (rewrite K8 by dk8; unfold R7; gres; exact R6_8).
assert (R8_9 : getr r8 9 = Z_to_bv 64 n) by (rewrite K8 by dk8; unfold R7; gres; exact R6_9).
assert (R8_18 : getr r8 18 = Z_to_bv 64 ab) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
assert (R8_19 : getr r8 19 = Z_to_bv 64 (rs + rz)) by (rewrite K8 by dk8; unfold R7; gres; exact R6_19).
assert (R8_20 : getr r8 20 = Z_to_bv 64 (ab + rz)) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
assert (R8_21 : getr r8 21 = Z_to_bv 64 (ab + rz - 16)) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
assert (R8_24 : getr r8 24 = Z_to_bv 64 0) by (rewrite K8 by dk8; unfold R7; gres; reflexivity).
destruct (art_allocate_post_small r8 M8 rom raw sp n qn m8 rs qr rz qz c (4096 * qs) w ab t tp loff key tsd ctx id 250 (art_hdr_b1 ob) mc mb mr mbs
(U raw) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))
(U (getr regs 22)) (U (getr regs 23)) (U (getr regs 24)) (U (getr regs 25)) (U (getr regs 26)) (U (getr regs 27))
eq_refl Hret R8_2 R8_4 R8_8 R8_9 P8_10 R8_18 R8_19 R8_20 R8_21 R8_24
Hn En Hm8 Ers Hrs Erz16 ltac:(clear - Hqz Erz16; lia) Hprim eq_refl ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia)
ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) Hsp'
G7 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) G9 ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - At_s; unfold apart in *; lia)
ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) G15 G18 ltac:(clear - Ac_s; unfold apart in *; lia)
Hloff G19 Hloff' Hloff'' G21 G22
ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zapart_f)
Hid ltac:(lia) Hb1 Hmc Hmb Hmr Hmbs
(u64_range raw) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
W8 Wc8 Wsh8 Wt8 L8 T8 SAB8
ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Cpp]) ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Cmfs]) ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Cfb])
ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Cg]) Clsan8 ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact Chook]) ltac:(apply T_img; [clear; lia|clear; cbn; lia|exact RO3])
Cmc Cmb Cmr Cmbs B8a B8b B8c
ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F8])
ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F120]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F112]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F104])
ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F96]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F88]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F80])
ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F72]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F64]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F56])
ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F48]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F40]) ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F32])
ltac:(apply T_frm; [clear; lia|clear; cbn; lia|exact F24]))
as (rF & MF & RUNF & PF10 & PF2 & PF1 & PF8 & PF9 & PF18 & PF19 & PF20 & PF21 & PF22 & PF23 & PF24 & PF25 & PF26 & PF27 & GF & AGF & CL1 & CL2 & CL3 & CL4 & SHZ & SHP & PF3 & PF4 & LCH).
eapply ar_steps; [exact RUNF|]. apply ar_done.
assert (A8F : art_agree [(sp - 1952, 1952); (ab, rz + n); (2147450880 + (ab + rz) / 8, rs / 8); (t + 2800, 24); (t + 2912 + 8 * c, 8)] M8 MF).
{ intros x Hx. cbn [art_out fst snd] in Hx. apply AGF. unfold art_post_writtenG. clear - Hx. lia. }
rewrite Hub8, Hqr8 in A8F.
pose proof (art_agree_trans _ _ _ _ _ A68 A8F) as A6F.
assert (G6F : mem_grows M6 MF) by (eapply mem_grows_trans; [exact G67|]; eapply mem_grows_trans; [exact G78|exact GF]).
pose proof (art_hdr_b1_type ob Hob) as (Hty & Hb1').
apply (K rF MF (Z.land (art_hdr_b1 ob) 243)).
- exact PF10.
- exact PF2.
- exact PF1.
- intros r Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
[ rewrite PF3; exact R8_3 | rewrite PF4, R8_4; symmetry; exact H4
| rewrite PF8 | rewrite PF9 | rewrite PF18 | rewrite PF19 | rewrite PF20 | rewrite PF21 | rewrite PF22 | rewrite PF23 | rewrite PF24 | rewrite PF25 | rewrite PF26 | rewrite PF27 ];
apply Z_to_bv_bv_unsigned.
- eapply mem_grows_trans; [exact G08|exact GF].
- intros x N.
assert (N1 : ~ art_post_writtenG sp t c ab rz n rs (U x)).
{ intros F; apply N; unfold art_alloc3_fp; unfold art_post_writtenG in F.
destruct F as [F|[F|[F|[F|F]]]]; [left | do 2 right; left | do 3 right; left | do 4 right; left | do 5 right; left]; exact F. }
rewrite (AGF x N1).
rewrite (AGd x) by (intros F; apply N; unfold art_alloc3_fp; first [ do 6 right; exact F | left; clear - F; lia ]).
rewrite (A67 x) by (cbn [art_out fst snd]; split; [|exact I]; intros F; apply N; unfold art_alloc3_fp; right; right; left; clear - F Hqz Erz16 Hn; lia).
rewrite (RA x) by (intros F; apply N; unfold art_alloc3_fp; right; left; exact F).
apply AG05. intros F. apply N. unfold art_alloc3_fp. left. clear - F. lia.
- apply (DInvD_frame l2 blk kb M8 MF DI8). intros x Dx. apply A8F. revert Dx. apply art_dpriv_out; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f.
- apply (art_pc_hdr_tr _ (t + 208) true M6 MF ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) ltac:(clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia) A6F); [|exact RPH]. intros c' Hc'. revert Hc'. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris. intros Hc'. zarith_f.
- match type of A6F with art_agree ?WW _ _ => apply (art_cls_rep_tr WW (t + 208) spb ris c (art_cls_pop clp) M6 MF) end; first [ exact (conj CR6 RR6) | exact G6F | exact A6F | exact Hl16' | idtac ];
cbn [art_cls_pop cl_free]; first [ clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; lia | clear - Hnf4' Hmfa1'; lia | idtac ].
all: revert Hnf4' Hmfa1'; clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; intros Hnf4' Hmfa1'; zarith_f.
- exact ROK.
- exact RCP.
- exact Hb1'.
- exact Hty.
- exact CL1.
- exact CL3.
- exact CL4.
- exact CL2.
- apply (art_cell_tr1 _ M6 MF _ _ _ A6F); [|exact SAB6]. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris; zarith_f.
- intros j Hj. replace (shb + 2 * w + 2 * qz + j) with (2147450880 + ab / 8 + 2 * qz + j) by (rewrite Hab8; clear - Eshb; lia). apply SHZ. exact Hj.
- intros NE. replace (shb + 2 * w + 2 * qz + qn) with (2147450880 + ab / 8 + 2 * qz + qn) by (rewrite Hab8; clear - Eshb; lia). apply SHP. exact NE.
- intros E1 E2 j Hj Hex. pose proof (RSH E1 E2 j Hj) as C6.
replace (2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km + j) with (shb + 32768 * km + j) in C6 by (clear - Eshb; lia).
apply (art_cell_tr1 _ M6 MF _ _ _ A6F); [|exact C6]. revert Hj Hex. clear - HHI HHI' Hsp' G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Hc Hkm Hkm' Eab Eshb Hw0 Hwsz Haumu' Hmu3' Hsz Hfit Hqz Erz16 Ers Hrs Hn En Hm8 Hprim Hstk Hstk' Htrp Hszt Htrp1 Htrp2 Hloff Hloff' Hloff'' Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs DG1 DG2 DG4 DG5 TR Hab8 Hub8 Hqr8; subst ab shb ris. intros Hj Hex. zarith_f.
- exact LCH.
Qed.
End SE.
End Spec.
