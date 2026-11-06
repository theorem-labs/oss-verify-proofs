(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JbtLeaf JbtAllocG JbtPoison ArtRuns ArtRunsMem JbtFp JbtRefill1 JbtCellEx .
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JbtRecycle3 JbtRecycle3R.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtRecycle3D () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle3D.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3lt"; "4nth"; "5Z"]; ["0HI"; "6bvmap"; "0M"; "0M'"; "7apart"; "7cell"; "7wr"; "8msteps"; "9ret_ok"; ":art_agree"; ";art_f32"; ";art_lcdrain_a_mem"; "<getr"; "<mkst"; "<regupd"; "=mem_grows"]; [">loaded_segments"; "?In"; "@add"; "@le"; "@lt"; "@mul"; "@of_nat"; "@pow"; "@sub"; "0c"; "0ca"; "0cnt"; "0fx"; "0h"; "0ia"; "0j"]; ["0mfa"; "0nf"; "0nfr"; "0qris"; "0raw"; "0regs"; "0regs'"; "0ris"; "0rom"; "0sp"; "0spb"; "ABV"; "AZ_to_bv"; "Abv"; "0ws"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section FPX. Context {fx : PropExec.FPState}.
Definition art_lcdrain_a_mem (M : word -> option byte) (sp : Z) (raw : word) (ca ia c cnt h : Z) : word -> option byte :=
Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 24) 0) (sp - 16) 0) (sp - 56) ia) (sp - 48) 0) (sp - 40) 0) (sp - 32) 0) (ca + 80 * c) (cnt - h).
Section SE.
Local Abbreviation SEC_T_art_lcdrain_a_fn := (ltac2:(TCodec.tc2 tcn__JbtRecycle3D "UO&Ay5'QMyR0%211%5241'5y8%611%311p061'?':&Lr:(QK+1(8%33A21%6251r7%93A21r;+2%93G17%<231&QL%12H7%@3H31r<+:%@3N1>%C231%E3M16r=+;%E3Q31C%H231&Q2r8&Q5+R@r6%3221%6251%C2Q:1%Q23Q:91r>+<%Q23Q@1Q0%Q5231%I2Q@<%Q83Q@21r?+=%Q83QF1Q6%Q;231%Q=3QE16&Q3+Vb\P0+R0%G221%421Q1&Q4&Q7%12Q:5%32Q01&F&Q0rA&Q8%12H;%54431<+TP0%@21K+Ra0%Q62G1r@%821B%E231'9%G2R1Q2+O%I2Q41%4231z%L219%H2:F%8221%O2Q4<+@%Q12F1rIrE%K4J21C&ErJrFrD%QK2QJ1%QN231u4rC%85Q37321rKrG%R22R1=%R5221+4%R7221%R62RG8%@5Q;72:1'G&MvQ<rM+ZbZL%S63SB1S4/01SBrL%756521@&N+Zb^0%S12SH1%339S:1%QG2Q1R1%S42SK1%633S71%S62SMG%832S21+QH%QM2Q71%S:2T11%<34S11rH+R`0%S2221%S?2T61%A35RI1+>%SM3T;1SK%S52S4Q<%S8281%S921QE%R:2QCQ>%S92Q51%S<231%SI2T@1%K3:81+?%T73TE1T5%SM2TDQE%O3421%T:3THQOT8%Q1321A+Zbh0%T=3TI1T;/01TI&K%18Q8R3QOIQFQNR2QM%Q?5Q>631QH%QA3RMQ91p0QC1p0QL1p0R61p0R:1p0R=1p0RF1p0R@1p0RE1p0RK1p0S11p0S41p0S;1p0S@1p0SF1p0SL1p0T31p0TA1p0TG1p0TO1pRLU:1pRHU;1pRDU<1pRNU=1pRFU>1pSDU?1pS:UG1pSBUB1pQ6UC1pS<UI1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_a_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_a_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_a_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_a_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_a_fn) 4%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_a_fn) 5%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_a_fn) 6%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_a_fn) 7%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_a_fn) 8%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_a_fn) 9%nat 0%nat).
Lemma art_lcdrain_a_fn : ltac:(sec_stmt2 constr:(SEC_T_art_lcdrain_a_fn) 10%nat 0%nat).
Proof using Type regs M rom raw sp ca ia c cnt h.
intros H1 H2 H10 H11 H12 H13 Hsp Hsp' W Hca Hca' Hc Hia Hh Hhc Hcnt Wca Ccnt Cmc.
zstep (ltac:(oF' 0x5495c%Z)) (ltac:(oD' 0x5495c%Z)).
zsd (ltac:(oF' 0x54960%Z)) (ltac:(oD' 0x54960%Z)) (sp - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x54964%Z)) (ltac:(oD' 0x54964%Z)) (sp - 24) 0 ltac:(zwok'). zsd (ltac:(oF' 0x54968%Z)) (ltac:(oD' 0x54968%Z)) (sp - 16) 0 ltac:(zwok').
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Ccnt' : cellA X (ca + 80 * c) 4 cnt) by zcell; assert (Cmc' : cellA X (ca + 80 * c + 4) 4 (2 * h)) by zcell end.
zlw (ltac:(oF' 0x5496c%Z)) (ltac:(oD' 0x5496c%Z)) (ca + 80 * c) Ccnt'.
zlwu (ltac:(oF' 0x54970%Z)) (ltac:(oD' 0x54970%Z)) (ca + 80 * c + 4) Cmc'.
zsd (ltac:(oF' 0x54974%Z)) (ltac:(oD' 0x54974%Z)) (sp - 56) ia ltac:(zwok'). zsd (ltac:(oF' 0x54978%Z)) (ltac:(oD' 0x54978%Z)) (sp - 48) 0 ltac:(zwok'). zsd (ltac:(oF' 0x5497c%Z)) (ltac:(oD' 0x5497c%Z)) (sp - 40) 0 ltac:(zwok'). zsd (ltac:(oF' 0x54980%Z)) (ltac:(oD' 0x54980%Z)) (sp - 32) 0 ltac:(zwok').
stepn (ltac:(oF' 0x54984%Z)) (ltac:(oD' 0x54984%Z)). rwH. rewrite (art_zb_srli_exact _ 1 h) by lia.
zstep (ltac:(oF' 0x54988%Z)) (ltac:(oD' 0x54988%Z)).
stepn (ltac:(oF' 0x5498c%Z)) (ltac:(oD' 0x5498c%Z)). rwH. rewrite (art_zb_srli_exact _ 32 cnt) by lia.
zbft (ltac:(oF' 0x54990%Z)) (ltac:(oD' 0x54990%Z)).
zstep (ltac:(oF' 0x54994%Z)) (ltac:(oD' 0x54994%Z)). zstep (ltac:(oF' 0x54998%Z)) (ltac:(oD' 0x54998%Z)).
zsw (ltac:(oF' 0x5499c%Z)) (ltac:(oD' 0x5499c%Z)) (ca + 80 * c) (cnt - h) ltac:(zwok').
zstep (ltac:(oF' 0x549a0%Z)) (ltac:(oD' 0x549a0%Z)). zstep (ltac:(oF' 0x549a4%Z)) (ltac:(oD' 0x549a4%Z)). zstep (ltac:(oF' 0x549a8%Z)) (ltac:(oD' 0x549a8%Z)). zstep (ltac:(oF' 0x549ac%Z)) (ltac:(oD' 0x549ac%Z)). zstep (ltac:(oF' 0x549b0%Z)) (ltac:(oD' 0x549b0%Z)). zstep (ltac:(oF' 0x549b4%Z)) (ltac:(oD' 0x549b4%Z)). zstep (ltac:(oF' 0x549b8%Z)) (ltac:(oD' 0x549b8%Z)).
stepn (ltac:(oF' 0x549bc%Z)) (ltac:(oD' 0x549bc%Z)).
unfold art_lcdrain_a_mem. zret.
Qed.
End SE.
Definition art_f32 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)).
Section SE.
Local Abbreviation SEC_T_art_unmap_null_fn := (ltac2:(TCodec.tc2 tcn__JbtRecycle3D "S0&Ay5'QMyR0%211%5241'5y8%611%311p061'?':&Lr5(QK+1(8%33A21%6251r2%93A21&Hr3%211r7+2%<3J1:%?231&QL%12K7%C3K31r8+:%C3Q11A%F231z%82Q21%J3Q231&Q3+Q@%221K&Q4r6&Q7+R0%22D1%5241&F&Q0r:&Q8%12K<%54431='G&MvQ<r<+acb4%Q<3QH1Q:/01QHr;%756521<&Nr9%238Q?1%Q52QOQ2%432Q81+8%QF3R41QD%QI2=1%83421+9%QJ3R81QH%QM2A1%<3421+B%QN3R<1QL%R12E1%@3421&J%14DQAAH%K5J3B1Q0%M3Q2E1p0O1p0Q61p0Q=1p0QA1p0QI1p0R11p0R51pSDR@1pS:RH1pSBRC1pQ6RD1pS<RJ1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_unmap_null_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_unmap_null_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_unmap_null_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_unmap_null_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_unmap_null_fn) 4%nat 0%nat).
Lemma art_unmap_null_fn : ltac:(sec_stmt2 constr:(SEC_T_art_unmap_null_fn) 5%nat 0%nat).
Proof using Type regs M rom raw sp.
intros H1 Hret H2 H10 Hsp Hsp' W.
zstep (ltac:(oF' 0x8ce44%Z)) (ltac:(oD' 0x8ce44%Z)).
zsd (ltac:(oF' 0x8ce48%Z)) (ltac:(oD' 0x8ce48%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x8ce4c%Z)) (ltac:(oD' 0x8ce4c%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x8ce50%Z)) (ltac:(oD' 0x8ce50%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x8ce54%Z)) (ltac:(oD' 0x8ce54%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zbtk (ltac:(oF' 0x8ce58%Z)) (ltac:(oD' 0x8ce58%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
assert (G9 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (G18 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell end.
zld (ltac:(oF' 0x8ce94%Z)) (ltac:(oD' 0x8ce94%Z)) (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x8ce98%Z)) (ltac:(oD' 0x8ce98%Z)) (sp - 16) G8. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x8ce9c%Z)) (ltac:(oD' 0x8ce9c%Z)) (sp - 24) G9. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x8cea0%Z)) (ltac:(oD' 0x8cea0%Z)) (sp - 32) G18. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x8cea4%Z)) (ltac:(oD' 0x8cea4%Z)).
stepret (ltac:(oF' 0x8cea8%Z)) (ltac:(oD' 0x8cea8%Z)) raw ltac:(reflexivity).
unfold art_f32. zret.
Qed.
End SE.
Ltac inl4 := cbn [In]; repeat (first [left; reflexivity | right]).
Section SE.
Local Abbreviation SEC_T_art_lcdrain_run := (ltac2:(TCodec.tc2 tcn__JbtRecycle3D "^5'2'?%211&Ay5'QMyR0%211%5241'5y8%611%311p061':&LrA(QK+1(8%33@21%6251r>%93@21&Hr?%211rC+2%<3I1:%?231&QL%12J7%C3J31rD+:%C3Q01A%F231%72Q0@%I3Q021rE+;%I3Q61G%L231&Q2&Q5+R@r=%3221%52H1%C2Q<1%Q53Q<81rF+<%Q53QB1Q3%Q8231%Q:3QA1HrG+=%Q:3QG1Q8%Q=231%Q?3QF1M&Q3+Vb\P0%221Q5&Q8+X@%22K1%62Q21&Q4&Q7+R0%22Q<1%42E1+XPPP0%O2G1+Q?%72QA1%@231+RPP0%B21Q8+TP0%Q62N1%E21D'9%G2R3Q1+N%I2Q31%4231%K2JQG+Q5%E2QO1%Q@2QD1%R?3RLQK1+T0%QB21QM%RB3ROQH1rM%Q42@1%Q52B2rN+Ra0%QJ221rO%Q:221'<%QN235%Q=21L%Q>2Q=5%4221&DrQ0rK%R52FQ0%443=21&Q6&1rQ8%22SE1%411%S:3SGG1%QK2S7E%QL2C;rQ1+@%QO221z%R121N+Q8%QK2S51%QM2Q11%Q?241+4rQ2%RJ2Q21%RJ231%R:21Q7+M%R42S>1%R=2Q71%R>2>Q8%R82Q9R5%QJ221&F&Q0rQ>rQ;%RB21RA%54431RBrQ?rQ:%84721QBrQ@rQ5rQ9%S>2QM1%S@231%>4=51QOrQArQ7+Q0%RK2T51%SE2<1%SG241+S`PPPP0%SI221rQ3%H4G921&ErQBrQ=%SN2SMI%T0221u4%65N521HrQCrQ<%T42T31%T62Q11%T721Q?%T72THN%=5Q56281rQD%T;2Q6Gu8%A5Q9321Q3rQE+Q@%T@2Q71%E5Q=315Q7rQF%TC2Q7QO+SoooooO%I5QA32D1rQG+QV`l0+QiaW0%M5QE32=1rQH%O5QG13?SFrQI+RQP0+ZooooPPPPoooO%Q35QK32C1rQJ%U02S?N%U22QI1%Q75QO31GRArQK%U42SCK%U62QJ1%U721RG%Q<5R441LR3rQL%U92SHL%U;2QI1+H%U=221%QB5R:51Q2R9rQM%U?2SNN%UA2QD1%UB21U@%QG5R?41Q7R>'3&=r1rR1%S@2W31%4231&>r2rR2%34W821S;%U<2S<1+O%U62V@1%U8241%TJ241rR0%V32V2Q8%V52Q11%V621SF%UB2Q=QA%V72S@1%V9231%T31?%V:2SC1%V<231%RA5S9:1R<@%U62<1p0F1pS0L1';'G&MvQ<+ZbZL%WA3WL1W?/01WL%554L1Q1ErQO%756O1Q4G%93SG31%WI2Q1W;rQN%W;2X41%WM3X431%X71X8&Q1(0+3%WO3X<1WM%X03X=T=WN+8%X23X?1X0+9%X43XA1X2+B%X63XC1X4+C%X83XE1X6+D%X:3XG1X8+E%X<3XI1X:+F%X>3XK1X<+G%X@3XM1X>%XA3XNR:X?+I%XC3Y01XA+J%XE3Y21XC+K%XG3Y41XE(4%11N%M3O31%N3Q061%O3Q191%Q03Q2<1%Q13Q3>1%Q23Q4A1%Q33Q5D1%Q43Q6G1%Q53Q7J1%Q63Q8M1%Q73Q9Q01%Q83Q:Q31%Q93Q;Q61%Q:3Q<Q81%Q<3Q=RG1r4%Y<21RDrR4%Y>21RF%Y@3YG31p061pT0QD1&O%12ROS0&I'7%12Z4Z4(6%X62QNX5%24Z7Z71X6%XL2XKSM%XN2SE1%54Z:Z:1V7%XO2T0U;%Y12T;1%Y221U:%Y22V;TI%Y4221%Y42V=T;%<4ZAZA21%Y62WET7%Y82TF1%?4ZDZD1R3%Y:22VJ%A4ZFZF1R5%Y<24Y:%C4ZHZH1R7%QA1E%R=3F21%R>3G51%R?3H81%R@3I<1%RA3JD1%RB3KH1%N31SNSO%Y12TJTL%UK5VCT1IUF1%UL5VDT2@U<W6%YI2U?TO%UN5VFT4@U>1%YK2UNU1%V05VHT6@U@1%WE2[8Q=%T92T81r3%YO2TGV;%Z12U51%Z221V:%Z32UASI%Z32W<1%Z5231rR5%T=4[BT<1WE%V<5W493V71p0;1pS0TF1%Y32?1%Y42B1%Y52E1%Y62G1%Y72J1%Y82QJ1%Y92QM1%Y:2SC1%Y;2SH1qQ8[C1%T42[D1qS>[J1%T62[K1p0T81p0U61p0U<1p0UC1p0UI1p0UN1p0V31p0V61p0V;1p0V@1p0VE1p0VJ1p0W21p0W:1p0WE1p0WL1p0X01p0X71p0X;1p0X?1p0XE1p0XL1p0Y01p0Y21p0Y41p0Y;1p0YA1p0YG1p0YM1p0YO1p0Z21p0Z61p0Z;1p0Z=1p0ZC1p0ZG1p0ZJ1p0[01p0[61p0[;1p0[?1p0[E1p0[K1p0\81p0\?1p0\G1p0\K1pS6]B1pS2]C1pS4]D1pS8]E1pS@]F1pSF]G1pRL]H1pRH]I1pRD]J1pRN]K1pRF]L1pQ2]M1pSD]N1pS:]I1pSB]D1pQ6]E1pS<]K1pSN^21")) (only parsing).
Variable ws : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 2%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 3%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 4%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 5%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 6%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 7%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 8%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 9%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 10%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 11%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 12%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 13%nat 0%nat).
Variable qris : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 14%nat 0%nat).
Variable nf : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 15%nat 0%nat).
Variable mfa : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 16%nat 0%nat).
Variable nfr : ltac:(sec_ty2 constr:(SEC_T_art_lcdrain_run) 17%nat 0%nat).
Lemma art_lcdrain_run : ltac:(sec_stmt2 constr:(SEC_T_art_lcdrain_run) 18%nat 0%nat).
Proof using Type ws regs M rom raw sp HI ca ia c cnt h spb ris qris nf mfa nfr.
intros H1 Hret H2 H10 H11 H12 H13 HHI Hsp Hsp' HHI' Hia Hia' Hc Hspb Eris Eq Hris' Hca Hca' Hcai Aca Eh Hh Hhc Hcnt
Hnf Hmfa Hmfa' Hnfr W Wca Wr Wfa Ccnt Cmc Cspb Cris Crel Cpc Cpg Crd Cmx Cnf Cmfa Cnfr Cws.
unfold apart in Aca.
pose proof (art_lcdrain_a_fn regs M rom raw sp ca ia c cnt h H1 H2 H10 H11 H12 H13 ltac:(lia) Hsp' ltac:(eapply wr_sub; [exact W|lia|lia]) Hca ltac:(lia) ltac:(lia) ltac:(lia)
Hh Hhc Hcnt Wca Ccnt Cmc) as RUN1.
unfold art_lcdrain_a_mem in RUN1.
match type of RUN1 with msteps _ _ (mkst ?R1 _ ?X1 _) =>
assert (F1 : mem_grows M X1 /\ art_agree [(sp - 272, 272); (ca + 80 * c, 4)] M X1) by (split; [zgrows|eapply art_agree_sub; [zagree|]; zsub]);
assert (C1 : cellA X1 (ia + 32) 8 spb /\ cellA X1 (ia + 48) 8 ris /\ cellA X1 (ia + 40) 4 0xffffffff /\ cellA X1 0x134380 8 0x1cc4e0 /\ cellA X1 0x1cc4e0 8 4096
/\ cellA X1 0x10400 8 0xafffff00000fffff /\ cellA X1 (ris + 128 * c) 8 0 /\ cellA X1 (ris + 128 * c + 16) 8 nf /\ cellA X1 (ris + 128 * c + 24) 8 mfa
/\ cellA X1 (ris + 128 * c + 80) 8 nfr /\ cellA X1 (sp - 8) 8 (U raw) /\ cellA X1 (sp - 32) 8 0 /\ cellA X1 (sp - 24) 8 0 /\ cellA X1 (ca + 80 * c) 4 (cnt - h))
by (repeat split; zcell);
assert (Cws1 : forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA X1 (ca + 80 * c + 16 + 4 * (cnt - h) + 4 * Z.of_nat j) 4 (nth j ws 0))
by (intros j Hj; destruct (Cws j Hj) as [Rj Cj]; split; [exact Rj|]; pose proof (proj1 (Nat2Z.inj_lt _ _) Hj); zcell);
assert (W1 : wrA X1 (sp - 272) 272 /\ wrA X1 (ris + 128 * c) 128 /\ wrA X1 (spb + c * 2 ^ 32 + 3758096384) mfa) by (repeat split; zwr);
set (Ra := R1) in *; set (Xa := X1) in *
end.
destruct F1 as (G1 & AG1). destruct W1 as (W1a & W1r & W1f).
destruct C1 as (Cspb1 & Cris1 & Crel1 & Cpc1 & Cpg1 & Crd1 & Cmx1 & Cnf1 & Cmfa1 & Cnfr1 & E8 & E32 & E24 & Ccnt1).
clearbody Xa.
destruct (art_rta_run ws Ra Xa rom (0x549c0 : bv 64)%bv (sp - 64) HI ia (sp - 56) (ca + 2560) c (ca + 80 * c + 16 + 4 * (cnt - h)) h spb ris qris nf mfa nfr
ltac:(unfold Ra; gres; bveq) ltac:(unfold ret_ok; bveq) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity)
ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; exact H13) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity)
HHI ltac:(lia) ltac:(lia) HHI' Hia Hia' Hc Hspb Eris Eq Hris' Eh ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; lia)
Hnf Hmfa Hmfa' Hnfr ltac:(lia) ltac:(lia) ltac:(eapply wr_sub; [exact W1a|lia|lia]) W1r W1f Cspb1 Cris1 Crel1 Cpc1 Cpg1 Crd1 Cmx1 Cnf1 Cmfa1 Cnfr1 Cws1)
as (r2 & M2 & RUN2 & B2 & BK & G2 & AG2 & Cmx2 & Cnf2 & Cnfr2 & Cfa2).
replace (sp - 64 - 208) with (sp - 272) in AG2 by lia.
set (W2 := [(sp - 272, 208); (spb + c * 2 ^ 32 + 3758096384 + 4 * nf, 4 * h); (ris + 128 * c, 8); (ris + 128 * c + 16, 8); (ris + 128 * c + 80, 8)]) in *.
assert (GF : forall a k, sp - 64 <= a -> a + k <= sp -> art_gap W2 a k).
{ intros a k Ha Hk. unfold W2. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
assert (GC : art_gap W2 (ca + 80 * c) 4).
{ unfold W2. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
assert (F8 : cellA M2 (sp - 8) 8 (U raw)) by (apply (art_cell_tr W2 Xa M2 _ _ _ AG2); [apply GF; cbn; lia|lia|cbn; lia|exact E8]).
assert (F32 : cellA M2 (sp - 32) 8 0) by (apply (art_cell_tr W2 Xa M2 _ _ _ AG2); [apply GF; cbn; lia|lia|cbn; lia|exact E32]).
assert (F24 : cellA M2 (sp - 24) 8 0) by (apply (art_cell_tr W2 Xa M2 _ _ _ AG2); [apply GF; cbn; lia|lia|cbn; lia|exact E24]).
assert (Ccnt2 : cellA M2 (ca + 80 * c) 4 (cnt - h)) by (apply (art_cell_tr W2 Xa M2 _ _ _ AG2); [exact GC|lia|cbn; lia|exact Ccnt1]).
assert (W2a : wrA M2 (sp - 64 - 48) 48) by (eapply wr_grows; [exact G2|]; eapply wr_sub; [exact W1a|lia|lia]).
eassert (RUN3 : msteps ASEGS (mkst r2 (0x549c0 : bv 64)%bv M2 rom) _).
{ zld (ltac:(oF' 0x549c0%Z)) (ltac:(oD' 0x549c0%Z)) (sp - 32) F32.
zld (ltac:(oF' 0x549c4%Z)) (ltac:(oD' 0x549c4%Z)) (sp - 24) F24.
zstep (ltac:(oF' 0x549c8%Z)) (ltac:(oD' 0x549c8%Z)).
stepn (ltac:(oF' 0x549cc%Z)) (ltac:(oD' 0x549cc%Z)).
zcall (art_unmap_null_fn _ _ _ (0x549d0 : word) (sp - 64)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (F8' : cellA X (sp - 8) 8 (U raw)) by (unfold art_f32; zcell) end.
zld (ltac:(oF' 0x549d0%Z)) (ltac:(oD' 0x549d0%Z)) (sp - 8) F8'. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x549d4%Z)) (ltac:(oD' 0x549d4%Z)).
stepret (ltac:(oF' 0x549d8%Z)) (ltac:(oD' 0x549d8%Z)) raw ltac:(reflexivity).
apply mst_refl. }
match type of RUN3 with msteps _ _ (mkst ?R3 _ ?X3 _) =>
assert (F3 : mem_grows M2 X3 /\ art_agree [(sp - 96, 32)] M2 X3) by (unfold art_f32; split; [zgrows|eapply art_agree_sub; [zagree|]; zsub]);
set (M3 := X3) in *
end.
destruct F3 as (G3 & AG3). clearbody M3.
assert (T3 : forall a (k : nat) v, apart a (Z.of_nat k) (sp - 96) 32 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M2 a k v -> cellA M3 a k v).
{ intros a k v A Ha Hk C. apply (art_cell_tr _ M2 M3 a k v AG3); [cbn [art_gap fst snd]; split; [exact A|exact I]|exact Ha|exact Hk|exact C]. }
eexists. exists M3.
split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3|].
split; [gres; f_equal; lia|].
split. { intros x Hx. cbn [In] in Hx.
repeat (destruct Hx as [<-|Hx]; [gres; rewrite ?BK by inl4; unfold Ra; gres; reflexivity|]). destruct Hx. }
split. { eapply mem_grows_trans; [exact G1|]. eapply mem_grows_trans; [exact G2|]. exact G3. }
split. { eapply art_agree_sub; [eapply art_agree_trans; [exact AG1|]; eapply art_agree_trans; [exact AG2|]; exact AG3|].
unfold W2. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; lia. }
split; [apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact Ccnt2]|].
split; [apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact Cmx2]|].
split; [apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact Cnf2]|].
split; [apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact Cnfr2]|].
intros j Hj. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact (Cfa2 j Hj)].
Qed.
End SE.
End FPX.
