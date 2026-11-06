(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JbtLeaf JbtAllocG JbtPoison JbtInitCache ArtRuns ArtRunsMem JbtFp JbtRefill1 JbtPopulate1 JbtCellEx JbtCls JbtClsRep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JbtRecycle3 JbtRecycle3D JbtRecycle3R.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtRecycle3L () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInitCache."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle3L."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"]; ["3lt"; "4nth"; "5Z"; "0HI"; "6bvmap"; "0M"; "0M'"; "7Wn"; "7apart"; "7cell"; "7wr"; "8class_size"; "9msteps"; ":ret_ok"; ";art_cls"; ";art_cls_ok"]; [";art_cls_rep"; ";art_cptr_ok"; ";art_pc_hdr"; ";art_prim_consts"; ";art_region_rep"; ";cl_au"; ";cl_cache"; ";cl_free"; ";cl_mfa"; ";cl_mu"; ";cl_na"; ";cl_nfr"; "<art_agree"; "<art_gap"; "=art_ic_mc"; "=art_ic_size"]; [">art_f48"; "?art_cls_dealloc"; "?art_cls_full"; "?art_lcd_fp"; "@getr"; "@mkst"; "@regupd"; "Amem_grows"; "Bloaded_segments"; "CIn"; "Dadd"; "Ddiv"; "Dle"; "Dlt"; "Dmodulo"; "Dmul"]; ["Dof_nat"; "Dpow"; "Dsub"; "0W"; "0c"; "0ca"; "0cl"; "0cl'"; "0cnt"; "0csz"; "0fa"; "0fx"; "0g18"; "0g19"; "0g20"; "0g8"]; ["0g9"; "0ia"; "0j"; "0mc"; "0mx"; "0mx'"; "0nf"; "0p"; "0qris"; "0r"; "0raw"; "0regs"; "0regs'"; "0ris"; "0rom"; "0sp"]; ["0spb"; "EBV"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0sv"; "0w"; "0ws"; "0x"]]).
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
Section SE.
Local Abbreviation SEC_T_art_lcd_full_a_fn := (ltac2:(TCodec.tc2 tcn__JbtRecycle3L "UO&Dy5'S3yR0%211%5241'7y8%611%311p061'B'<&QDr:(S1+1(:%33A21%6251r7%93A21r;+2%93G17%<231&S2%12H7%@3H31r<+:%@3N1>%C231%E3M16r=+;%E3Q31C%H231%J3Q21;r>+<%J3Q81H%M231%O3Q71@r?+=%O3Q=1M%Q2231%Q43Q<1E&QL&QJ+Vb\P0+Q@%3221%521I&QM&R1+R0%22Q31%42I1&J&QHrA&R2%12I<%54431=';%B2QCQ6+O%D2Q81%4231+TP0%G21Lr@+Ra0%I221%=2>H%L221z%N216%I27F%?221%Q124Q6%L2Q7I%B221%Q42R5Q9+@%Q62Q;1%F231&IrHrD&QO+R@rB%3221%Q>251u4%95Q5821IrIrErC%:291%QE231+4%QG221%A5Q=719Q<'L&QEvR;rK+Za^8%S13S=1RO/01S=rJ%756521@&QF+ZakH%RL2SC1%339S51rG%QJ21R5%S02SG1%734S31+8%S>3SL1S<rF%Q32Q2Q4%R>221%S72SN1%>3751+9%SE3T31SC%S;2T27%B3421%C31S36%S>2T5Q4%E32S01%S@2T7Q?%G32RM1+>%SN3T<1SL%SD2T;Q@%K3421+?%T23T@1T0%N3314+B%T53TC1T3%Q1331=+C%T83TF1T6%Q4331>+D%T;3TI1T9%T12THQF%Q83421+ZbZL%T?3TK1T=/01TK&Q@%14Q?Q9R7QC%QF5QE631QO%QH3S6Q@1p0QJ1p0R31p0R>1p0RC1p0RG1p0RL1p0S21p0S51p0S;1p0SB1p0SH1p0SO1p0T51p0T;1p0TA1p0TG1p0TO1pU8U:1pU@U;1pT:U<1pU4U=1pT<U>1pV0U?1pUFUG1pUNUB1pQ<UC1pUHUI1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_a_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_a_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_a_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_a_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_a_fn) 4%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_a_fn) 5%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_a_fn) 6%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_a_fn) 7%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_a_fn) 8%nat 0%nat).
Variable mc : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_a_fn) 9%nat 0%nat).
Lemma art_lcd_full_a_fn : ltac:(sec_stmt2 constr:(SEC_T_art_lcd_full_a_fn) 10%nat 0%nat).
Proof using Type regs M rom raw sp ca ia c p mc.
intros H1 H2 H10 H11 H12 H13 Hsp Hsp' W Hc Hca Hca' Hia Hp Hmc Ccnt Cmc.
zstep (ltac:(oF' 0x545c8%Z)) (ltac:(oD' 0x545c8%Z)).
zsd (ltac:(oF' 0x545cc%Z)) (ltac:(oD' 0x545cc%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x545d0%Z)) (ltac:(oD' 0x545d0%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x545d4%Z)) (ltac:(oD' 0x545d4%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x545d8%Z)) (ltac:(oD' 0x545d8%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x545dc%Z)) (ltac:(oD' 0x545dc%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x545e0%Z)) (ltac:(oD' 0x545e0%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zbft (ltac:(oF' 0x545e4%Z)) (ltac:(oD' 0x545e4%Z)).
zstep (ltac:(oF' 0x545e8%Z)) (ltac:(oD' 0x545e8%Z)).
zbft (ltac:(oF' 0x545ec%Z)) (ltac:(oD' 0x545ec%Z)).
zstep (ltac:(oF' 0x545f0%Z)) (ltac:(oD' 0x545f0%Z)). zstep (ltac:(oF' 0x545f4%Z)) (ltac:(oD' 0x545f4%Z)). zstep (ltac:(oF' 0x545f8%Z)) (ltac:(oD' 0x545f8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmc' : cellA X (ca + 80 * c + 4) 4 mc) by zcell; assert (Ccnt' : cellA X (ca + 80 * c) 4 mc) by zcell end.
zlw (ltac:(oF' 0x545fc%Z)) (ltac:(oD' 0x545fc%Z)) (ca + 80 * c + 4) Cmc'.
zbft (ltac:(oF' 0x54600%Z)) (ltac:(oD' 0x54600%Z)).
zlw (ltac:(oF' 0x54604%Z)) (ltac:(oD' 0x54604%Z)) (ca + 80 * c) Ccnt'.
zbtk (ltac:(oF' 0x54608%Z)) (ltac:(oD' 0x54608%Z)).
zstep (ltac:(oF' 0x54758%Z)) (ltac:(oD' 0x54758%Z)). zstep (ltac:(oF' 0x5475c%Z)) (ltac:(oD' 0x5475c%Z)). zstep (ltac:(oF' 0x54760%Z)) (ltac:(oD' 0x54760%Z)). zstep (ltac:(oF' 0x54764%Z)) (ltac:(oD' 0x54764%Z)). zstep (ltac:(oF' 0x54768%Z)) (ltac:(oD' 0x54768%Z)). zstep (ltac:(oF' 0x5476c%Z)) (ltac:(oD' 0x5476c%Z)). zstep (ltac:(oF' 0x54770%Z)) (ltac:(oD' 0x54770%Z)).
stepn (ltac:(oF' 0x54774%Z)) (ltac:(oD' 0x54774%Z)).
unfold art_f48. zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_lcd_full_b_fn := (ltac2:(TCodec.tc2 tcn__JbtRecycle3L "Y@&Dy5'S3yR0%211%5241'7y8%611%311p061'B'<&QDrC(S1+2(:%33A21%6251&S2&R2r?+Q@%3221%52F1%>3F71rD+8%>3L1<%A231&QJ&QO+R@r=%3221%52>1%A2Q21%J3Q281rE+9%J3Q81H%M231r@%H2Q91%Q13Q931rF+B%Q13Q?1O%Q4231%Q63Q>16rG+C%Q63QD1Q4%Q9231%Q;3QC1;rH+D%Q;3QI1Q9%Q>231%Q@3QH1@&M%11@&QL%12Q9B&QM&R1+R0%22QD1%42B1';+1%921Q1+O%;2Q31%5231+TP0%>21ErI+Ra0%QA221rJ%QM21QK%D231&QN%124QIz%R;3R<21'?rK%QK21;+RPP0%M221+Vb\P0%O215%7231%Q1257rL%R321O%Q4216%Q52>C+Q5%Q42RF1%R82>1+Q?%Q72RI1%Q9231rMrN+Q0%Q<2RN1%R?231%RA2?1+@%RB21I%RD231%S83S991%QF2OD+L%QE2S71%QG2G1%QC241%QI2I9%QE261+QO%QK2S=1%QM2M1%QI2:1%QO2OQL%QK2<1&J&QHrQ>rQ:%44321QG&IrQ?rQ;rQ9%S;2S:1%S=231u4rQ5%85<7321rQ@rQ<%SB2SA=%SD221%SE21SHu8%?5C6218rQA%SI27Q;%B5F214?rQB+R`@%SM2H1rQ6%G5K4291rQC%T;2@T4&S4%12TO;%L5Q043>1rQD%T@2>QDrQ7%Q05Q432B1rQE+H%TE2@1%Q45Q831F5rQF%TH2>R0%Q75Q;21I8rQG+Q8%TL2=1%Q;5Q?31M<rQH%TO2<TM%Q>5QB21Q0?'L&QEvR;rQJ+ZakH%U<3UH1U:/01UHrQI%756521;&QF%UA3UOSIU?%2381B%U>2UOF%432UA1%U@2V1QC%632U81%UB2V3QM%832TN1+:%UJ3V81UH%U;2Q2Q?%UG2V81%=3531+;%UO3V=1UM%UJ2SIR;%UL2V=1%B3531+<%V43VB1V2%UD2UCQE%UF2Q=1+4%UG2R?1%UI231%V52VF1%K3971+=%V=3VK1V;%V92VJR=%O3421+>%VA3VO1V?%V22RITJ%V>2VO1%Q43531%V@2W1RO%Q632UE1%VB2W3RL%Q832UB1rQ8%VE2W61%Q;33U@1&G%14ROQ?G;%V>2HSL%V>2HS6%V@221%54S341S0rQ=%VC21Q3%84RN3Q91%QM5QL:R51R1%QO3SBQG1p0R11p0R51p0R:1p0R>1p0RC1p0RH1p0RN1p0S41p0S81p0S@1p0SJ1p0T01p0T11p0T21p0T31p0T41p0T51p0T81p0T=1p0T@1p0TF1p0U11p0U81p0U:1p0U>1p0U@1p0UI1p0UN1p0V51p0V81p0V?1p0VE1p0VH1p0VK1p0W11p0W71p0W=1p0WE1p0X21pTNXB1pTLXC1pTJXD1pU2XE1pU0XF1pV<XG1pTDXH1pTBXI1pV>XJ1pV2XK1pU@XL1pT:XM1pU4XN1pT<XO1pV0Y01pUFY81pUNY31pQ<Y41pUHY:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 4%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 5%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 6%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 7%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 8%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 9%nat 0%nat).
Variable w : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 10%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 11%nat 0%nat).
Variable csz : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 12%nat 0%nat).
Variable sv : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 13%nat 0%nat).
Variable g8 : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 14%nat 0%nat).
Variable g9 : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 15%nat 0%nat).
Variable g18 : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 16%nat 0%nat).
Variable g19 : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 17%nat 0%nat).
Variable g20 : ltac:(sec_ty2 constr:(SEC_T_art_lcd_full_b_fn) 18%nat 0%nat).
Lemma art_lcd_full_b_fn : ltac:(sec_stmt2 constr:(SEC_T_art_lcd_full_b_fn) 19%nat 0%nat).
Proof using Type regs M rom raw sp ca ia c p spb w cnt csz sv g8 g9 g18 g19 g20.
intros H2 H8 H9 H18 H19 H20 Hret Hsp Hsp' Hc Hca Hca' Hca8 Hcai Hia Hia' Hspb Hspb' Ep Hw Hcnt Hcsz Hsv
Hg8 Hg9 Hg18 Hg19 Hg20 Wca Ccnt Ccsz Cspb Csv F1 F8 F9 F18 F19 F20.
zstep (ltac:(oF' 0x54778%Z)) (ltac:(oD' 0x54778%Z)). zstep (ltac:(oF' 0x5477c%Z)) (ltac:(oD' 0x5477c%Z)). zstep (ltac:(oF' 0x54780%Z)) (ltac:(oD' 0x54780%Z)). zstep (ltac:(oF' 0x54784%Z)) (ltac:(oD' 0x54784%Z)).
zlw (ltac:(oF' 0x54788%Z)) (ltac:(oD' 0x54788%Z)) (ca + 80 * c) Ccnt.
stepn (ltac:(oF' 0x5478c%Z)) (ltac:(oD' 0x5478c%Z)).
zld (ltac:(oF' 0x5460c%Z)) (ltac:(oD' 0x5460c%Z)) (ia + 32) Cspb.
zstep (ltac:(oF' 0x54610%Z)) (ltac:(oD' 0x54610%Z)). zstep (ltac:(oF' 0x54614%Z)) (ltac:(oD' 0x54614%Z)). zstep (ltac:(oF' 0x54618%Z)) (ltac:(oD' 0x54618%Z)). zstep (ltac:(oF' 0x5461c%Z)) (ltac:(oD' 0x5461c%Z)). zstep (ltac:(oF' 0x54620%Z)) (ltac:(oD' 0x54620%Z)).
zld (ltac:(oF' 0x54624%Z)) (ltac:(oD' 0x54624%Z)) (ca + 80 * c + 8) Ccsz.
zstep (ltac:(oF' 0x54628%Z)) (ltac:(oD' 0x54628%Z)).
stepn (ltac:(oF' 0x5462c%Z)) (ltac:(oD' 0x5462c%Z)). rwH. rewrite (art_zb_srli_exact _ 30 (cnt * 4)) by lia.
zstep (ltac:(oF' 0x54630%Z)) (ltac:(oD' 0x54630%Z)). zstep (ltac:(oF' 0x54634%Z)) (ltac:(oD' 0x54634%Z)).
stepn (ltac:(oF' 0x54638%Z)) (ltac:(oD' 0x54638%Z)). rwH. rewrite (art_zb_srli_exact _ 4 w) by lia.
zsw (ltac:(oF' 0x5463c%Z)) (ltac:(oD' 0x5463c%Z)) (ca + 80 * c) (cnt + 1) ltac:(rewok Wca).
zsw (ltac:(oF' 0x54640%Z)) (ltac:(oD' 0x54640%Z)) (ca + 80 * c + 16 + 4 * cnt) w ltac:(zwok').
zstep (ltac:(oF' 0x54644%Z)) (ltac:(oD' 0x54644%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csv2 : cellA X (ca + 2576) 8 sv) by zcell; assert (Wsv2 : wokA X (ca + 2576) 8) by zwok end.
zamoadd_da (ltac:(oF' 0x54648%Z)) (ltac:(oD' 0x54648%Z)) (ca + 2576) sv (0 - csz) Csv2 ltac:(exact Wsv2) ltac:(rewrite Z.add_mod, Hca8 by lia; reflexivity).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 g8) by zcell;
assert (G9 : cellA X (sp - 24) 8 g9) by zcell; assert (G18 : cellA X (sp - 32) 8 g18) by zcell;
assert (G19 : cellA X (sp - 40) 8 g19) by zcell; assert (G20 : cellA X (sp - 48) 8 g20) by zcell end.
zld (ltac:(oF' 0x5464c%Z)) (ltac:(oD' 0x5464c%Z)) (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x54650%Z)) (ltac:(oD' 0x54650%Z)) (sp - 16) G8. zld (ltac:(oF' 0x54654%Z)) (ltac:(oD' 0x54654%Z)) (sp - 24) G9. zld (ltac:(oF' 0x54658%Z)) (ltac:(oD' 0x54658%Z)) (sp - 32) G18. zld (ltac:(oF' 0x5465c%Z)) (ltac:(oD' 0x5465c%Z)) (sp - 40) G19. zld (ltac:(oF' 0x54660%Z)) (ltac:(oD' 0x54660%Z)) (sp - 48) G20.
zstep (ltac:(oF' 0x54664%Z)) (ltac:(oD' 0x54664%Z)).
stepret (ltac:(oF' 0x54668%Z)) (ltac:(oD' 0x54668%Z)) raw ltac:(reflexivity).
zret.
Qed.
End SE.
End FPX.
Definition art_cls_push (w : Z) (cl : art_cls) : art_cls :=
CLS (cl_cache cl ++ [w]) (cl_free cl) (cl_au cl) (cl_mu cl) (cl_mfa cl) (cl_na cl) (cl_nfr cl).
Definition art_cls_return (h : nat) (cl : art_cls) : art_cls :=
let k := (length (cl_cache cl) - h)%nat in
CLS (firstn k (cl_cache cl)) (cl_free cl ++ skipn k (cl_cache cl)) (cl_au cl) (cl_mu cl) (cl_mfa cl) (cl_na cl) (cl_nfr cl + Z.of_nat h).
Definition art_cls_full (c : Z) (cl : art_cls) : bool := Z.of_nat (length (cl_cache cl)) =? art_ic_mc c.
Definition art_cls_dealloc (c w : Z) (cl : art_cls) : art_cls :=
if art_cls_full c cl then art_cls_push w (art_cls_return (Z.to_nat (art_ic_mc c / 2)) cl) else art_cls_push w cl.
Lemma art_ic_mc_half : ltac2:(TCodec.tc2 tcn__JbtRecycle3L "J'B';&QL+1r1%3221+O%5231%7231'<&Q>r2%211&QO+2&QK%1242%4231%93B61%A2@3+8%C251%E231%F251p0@1pT:I1").
Proof.
intros c Hc. unfold art_ic_mc. set (m := Z.max 1 (Z.min 8 (1024 / art_ic_size c))).
assert (Hm : 1 <= m <= 8) by (unfold m; lia).
replace (2 * m / 2) with m by (symmetry; rewrite Z.mul_comm; apply Z.div_mul; lia). lia.
Qed.
Definition art_lcd_fp (sp ca spb ris c nf : Z) : list (Z * Z) :=
[ (sp - 320, 320); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8); (ris + 128 * c, 128); (spb + c * 2 ^ 32 + 3758096384 + 4 * nf, 32) ].
Section SE.
Local Abbreviation SEC_T_art_cls_dealloc_ok := (ltac2:(TCodec.tc2 tcn__JbtRecycle3L "R='B'N';&QL+1r3%3221+N%5231%7231&Or4r2%3221&R0&3&Q6%11<%32B1%511&Q>r5%211%D241&Q1&Kr6%211&Q5%11B%63319&>&QI&0%B1=&Q7%11?%43Q531%63Q6<1%811'<'1&QBr8%221B(9%63521&QO+4&QJr7%@11%Q52QD1%Q711&QKr9%Q411+2%4221%:261%=2<1&Q8%11<%QL231p0B1&QA%13;G@%QI2<1p041p0N1p0Q81p0Q@1p0QK1p0R01pT>R91pV>R;1pT:R<1")) (only parsing).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_cls_dealloc_ok) 0%nat 0%nat).
Variable w : ltac:(sec_ty2 constr:(SEC_T_art_cls_dealloc_ok) 1%nat 0%nat).
Variable cl : ltac:(sec_ty2 constr:(SEC_T_art_cls_dealloc_ok) 2%nat 0%nat).
Lemma art_cls_dealloc_ok : ltac:(sec_stmt2 constr:(SEC_T_art_cls_dealloc_ok) 3%nat 0%nat).
Proof.
intros Hc OK Hlen Hw Hnin Hroom.
destruct OK as (L16 & Hau & Hcarve & Hmu & Hauk & Hmu' & Hmfa & Hmfa' & Hfree & Hall & Hnd).
apply NoDup_ListNoDup in Hnd.
destruct (art_ic_mc_half c ltac:(lia)) as (Emc & Hh). pose proof (art_ic_mc_range c ltac:(lia)) as Rmc.
unfold art_cls_dealloc. destruct (art_cls_full c cl) eqn:EF.
-
unfold art_cls_full in EF. apply Z.eqb_eq in EF. specialize (Hroom eq_refl).
set (h := Z.to_nat (art_ic_mc c / 2)). set (k := (length (cl_cache cl) - h)%nat).
assert (Hk : (k + h = length (cl_cache cl))%nat) by (unfold k, h; lia).
assert (PERM : Permutation (w :: cl_cache cl ++ cl_free cl) ((firstn k (cl_cache cl) ++ [w]) ++ (cl_free cl ++ skipn k (cl_cache cl)))).
{ rewrite <- (firstn_skipn k (cl_cache cl)) at 1. rewrite <- !app_assoc. cbn [app].
eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head. apply perm_skip. apply Permutation_app_comm. }
unfold art_cls_ok, art_cls_push, art_cls_return. cbn [cl_cache cl_free cl_au cl_mu cl_mfa]. fold h k.
split. { rewrite length_app, length_firstn. cbn [length]. lia. }
split; [exact Hau|]. split; [exact Hcarve|]. split; [exact Hmu|]. split; [exact Hauk|]. split; [exact Hmu'|]. split; [exact Hmfa|]. split; [exact Hmfa'|].
split. { rewrite length_app, length_skipn. unfold h in *. lia. }
split.
+ eapply Permutation_Forall; [exact PERM|]. constructor; assumption.
+ apply NoDup_ListNoDup. eapply Permutation_NoDup; [exact PERM|]. constructor; assumption.
- unfold art_cls_full in EF. apply Z.eqb_neq in EF.
assert (PERM : Permutation (w :: cl_cache cl ++ cl_free cl) ((cl_cache cl ++ [w]) ++ cl_free cl)).
{ rewrite <- app_assoc. cbn [app]. apply Permutation_middle. }
unfold art_cls_ok, art_cls_push. cbn [cl_cache cl_free cl_au cl_mu cl_mfa].
split. { rewrite length_app. cbn [length]. pose proof (art_ic_mc_range c ltac:(lia)). lia. }
split; [exact Hau|]. split; [exact Hcarve|]. split; [exact Hmu|]. split; [exact Hauk|]. split; [exact Hmu'|]. split; [exact Hmfa|]. split; [exact Hmfa'|].
split; [exact Hfree|].
split.
+ eapply Permutation_Forall; [exact PERM|]. constructor; assumption.
+ apply NoDup_ListNoDup. eapply Permutation_NoDup; [exact PERM|]. constructor; assumption.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_region_rep_ret := (ltac2:(TCodec.tc2 tcn__JbtRecycle3L "U@'B'N'S3yR0%211'7y8%511%311p051'4'8%12<<%311%41>&QJr;&QOr9&R1+2+Q0%3221%6251%9281+S`PPPP0%;221+T0r:%<221%?2>1&R0&3&Q7r8%211%42Q41%611&QLzr2%3221&QMr3%M21A+R0%K2J1%5231r5%;2:1r6+M%Q12Q01%Q6231%<218+4%Q7218%C215'<r=%K11&0r>%N11%33R01Q>%73QC51&Q8%115r?%311%<3R631&Q5%114r@%311%A3R;31&Q9%114rA%311%F3R@31&Q:%114rB%311%K3RE31&Q4rHrGrFrErC%6654321>&QG%12;@&Q<%13B5=&Q=+H%RD2O1+QH%43B21%RE2Q?Q2%63<I1&I&QHu8rI%453BN21+@%RO2K1rD%R@2S@1%RB11%S32Q41%;5:J591+R@%S62J1&Q;%11<%@5?Q03>1'5&@r1%RL2SLQ4%3221rJ%S01RG%SA2Q61%S@2R:1%SC2Q:1u4&A%14T5RMQ>RN%N5M8431p0:1pU6?1rQ1rQ0rOrMrK%QH654321Q3p071p0H1p0N1p0Q61p0Q<1p0Q?1p0QE1p0QH1p0QK1p0R31p0R91p0R?1p0RE1p0RK1p0S41p0S81p0S>1p0SA1p0SH1tU>U2SM1tUDU3T51tTFU4T:1pV@TG1pT8TI1pQ>TN1pQ<TO1pT@U81pT>U91pU<U;1pU:U<1pT:U=1pULU>1pV2U?1")) (only parsing).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_ret) 0%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_ret) 1%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_ret) 2%nat 0%nat).
Variable mx : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_ret) 3%nat 0%nat).
Variable mx' : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_ret) 4%nat 0%nat).
Variable cl : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_ret) 5%nat 0%nat).
Variable cl' : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_ret) 6%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_ret) 7%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_ret) 8%nat 0%nat).
Variable W : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_ret) 9%nat 0%nat).
Variable ws : ltac:(sec_ty2 constr:(SEC_T_art_region_rep_ret) 10%nat 0%nat).
Lemma art_region_rep_ret : ltac:(sec_stmt2 constr:(SEC_T_art_region_rep_ret) 11%nat 0%nat).
Proof.
intros fa r nf Hr Hr' Hfa Hfa' Hnf Efree Emfa Eau Emu Ena RR G A G24 GFA Cmx Cnf Cnfr Cws.
destruct RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
fold r in Rmx, Rnf, Rmfa, Rau, Ram, Rmu, Rmm, Rna, Rnfr, Wr. fold fa in Rfa, Wfa. fold nf in Rnf.
assert (Hnf0 : 0 <= nf) by (unfold nf; lia).
unfold art_region_rep. fold r fa. rewrite Emfa, Eau, Emu, Ena, Efree.
assert (T : forall a (n : nat) v, r + 24 <= a -> a + Z.of_nat n <= r + 80 -> cellA M a n v -> cellA M' a n v).
{ intros a n v Ha Hn C. apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G24|lia|lia]|lia|lia|exact C]. }
split; [exact Cmx|].
split. { rewrite length_app, Nat2Z.inj_add. exact Cnf. }
split; [apply T; [lia|cbn; lia|exact Rmfa]|]. split; [apply T; [lia|cbn; lia|exact Rau]|]. split; [apply T; [lia|cbn; lia|exact Ram]|].
split; [apply T; [lia|cbn; lia|exact Rmu]|]. split; [apply T; [lia|cbn; lia|exact Rmm]|]. split; [apply T; [lia|cbn; lia|exact Rna]|].
split; [exact Cnfr|].
split. { intros j Hj. rewrite length_app in Hj. destruct (Nat.lt_ge_cases j (length (cl_free cl))) as [Lt|Ge].
- rewrite app_nth1 by exact Lt. pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Hj'. fold nf in Hj'.
apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact GFA|lia|cbn; lia]|lia|cbn; lia|apply Rfa; exact Lt].
- rewrite app_nth2 by exact Ge. replace (Z.of_nat j) with (nf + Z.of_nat (j - length (cl_free cl))) by (unfold nf; lia). apply Cws. lia. }
split; [eapply wr_grows; [exact G|exact Wr]|]. split; [eapply wr_grows; [exact G|exact Wfa]|eapply wr_grows; [exact G|exact Wu]].
Qed.
End SE.
Section FPY. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_lcd_run := (ltac2:(TCodec.tc2 tcn__JbtRecycle3L "Z>&Dy5'S3yR0%211%5241'7y8%611%311p061'B'N'<&QDr?(S1+1(:%33B21%6251r<%93B21&Mr=%211rA+2%<3K1:%?231&S2%12L7%C3L31rB+:%C3Q21A%F231%72Q2@%I3Q221rC+;%I3Q81G%L231+QWTnH%>2Q91%Q03Q931rD+<%Q03Q?1N%Q3231%Q53Q>1CrE+=%Q53QD1Q3%Q8231%Q:3QC1H&QL+Vb\P0%221Q0&R2+Z0%22F1%62M1&QM&R1+R0%22Q71%42E1&QJ+XPPP0%22H1+Q?%82Q=1%A231';%C2QJQ4+N%E2Q61%4231%G2FQ>+Q5%A2QF1%>2Q;1%R63R8QB1&QO+T0%221QE%R:3R<Q@1+TP0%E2Q;1rI%Q3221%Q4242rJ+Ra0%K221rK%Q9221&QN+8%2241z%RI3RK21'?rL%Q521;+RPP0%QC221%QD2QC4%6221&HrM%Q<2OH%342CD1&J&QHrQ3rQ0%QK21QJ%54431QKrQ4rO%84721L&Q3rQ5%23>E1&Q2rQ1(9rQ6%43321&Q0rQ2rNrQ7%463>28Q:1&O%125Q9&R0&3&Q6%11Q5%32T31%511&Q>%11M%RJ231+Q0%RD2SI1%R12M1%RB2B1+@%R421O%RE231%T=3T?Q61%S32QFQ6+L%RM2T21%RO2Q91%RE241&IrQ<+R`@%RO2M1u8%55QB421Q@'1&QB%12Q2QC%TL331Q9+4&Q7%11Q=%Q22U21%Q411&QKrQ8%Q111%321TG%S?251%S02:1&Q8%11QG%SO231p0?1'='L&QEvR;rQA+Za^8%U?3UL1U=/01ULrQ@rQ?%8576321r2rQ>r1%<5;3215%>3RE51%UK25U=rQ=%U=2V81%UO3V831%V;1V<&QI(2+3%V13V@1UO%V23VAQ8V0%V33VBS@V1+9%V53VD1V3+B%V73VF1V5+C%V93VH1V7+D%V;3VJ1V9+E%V=3VL1V;+F%V?3VN1V=+G%VA3W01V?+H%VC3W21VA+I%VE3W41VC+J%VG3W61VE+K%VI3W81VG(6%11N%M3O31%N3Q061%O3Q191%Q03Q2<1%Q13Q3?1%Q23Q4B1%Q33Q5E1%Q43Q6H1%Q53Q7K1%Q63Q8N1%Q73Q9Q11%Q83Q:Q41%Q93Q;Q61%Q:3Q<Q81%Q<3Q=QD1r4%W>21QHrQC%W@21QJ%WB3WK31p061pVBQD1&QG%12R2QM&Q<&QCrQ;rQ:%RM1TD%SN2WN1%T011%66R15RKT541%831R;R6&QA%137TBTJ%T<69ROT981R9%V<2:S>&Q?%11;%VH2TK1%SD5U1R>4S@1%V;261%V<2:1%V=2D1%V>2G1%V?2R=1%V@2RB1qQ>XA1%S32XB1qUJXH1%S52XI1p0S71p0SK1p0T21p0T81p0TA1p0TK1p0TN1p0U41p0U:1p0U>1p0UB1p0UI1p0UN1p0V61p0V<1p0VB1p0VD1p0VI1p0VN1p0W31p0W51p0W;1p0WB1p0WH1p0WM1p0X11p0X71p0X=1p0XE1p0XL1p0Y41p0Y81pT>YC1pV<YE1pV>YF1pUBYG1pULYH1pV2YI1pU@YJ1pT:YK1pT<YL1pQ8YM1pV0YN1pUFZ61pUNZ11pQ<Z21pUHZ81")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 4%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 5%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 6%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 7%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 8%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 9%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 10%nat 0%nat).
Variable qris : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 11%nat 0%nat).
Variable w : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 12%nat 0%nat).
Variable sv : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 13%nat 0%nat).
Variable cl : ltac:(sec_ty2 constr:(SEC_T_art_lcd_run) 14%nat 0%nat).
Lemma art_lcd_run : ltac:(sec_stmt2 constr:(SEC_T_art_lcd_run) 15%nat 0%nat).
Proof using Type regs M rom raw sp HI ca c p spb ris qris w sv cl.
intros H1 Hret H2 H10 H11 H12 H13 HHI Hsp Hsp' HHI' Hc Hspb Eris Eq Hris' Hca Hca' Hca8 Hcai Aca
W Wca PC PH [CR RR] OK Hlen Ep Hw Csv Hroom.
destruct PC as (Cspb & Cris & Crel & _ & Crd & Cpc & Cpg & _ & _).
destruct (PH c ltac:(lia)) as [Cmc Ccsz].
destruct CR as [Ccnt Cch].
pose proof RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
pose proof OK as (L16 & Hau & Hcarve & Hmu & Hauk & Hmu' & Hmfa & Hmfa' & Hfree & Hall & Hnd).
destruct (art_ic_mc_half c ltac:(lia)) as (Emc & Hh). pose proof (art_ic_mc_range c ltac:(lia)) as Rmc. pose proof (art_ic_size_pos c ltac:(lia)) as Rsz.
pose proof (art_cell_norm _ _ _ _ Csv) as Csvn. pose proof (art_mod64_range sv) as Hsvn.
pose proof (art_cell_norm _ _ _ _ Rnfr) as Rnfrn. pose proof (art_mod64_range (cl_nfr cl)) as Hnfrn.
set (cnt := Z.of_nat (length (cl_cache cl))) in *. set (nf := Z.of_nat (length (cl_free cl))) in *.
set (r := ris + 128 * c) in *. set (fa := spb + c * 2 ^ 32 + 3758096384) in *.
assert (Er : r = ris + 128 * c) by reflexivity. assert (Efa : fa = spb + c * 2 ^ 32 + 3758096384) by reflexivity.
assert (Hcnt0 : 0 <= cnt) by (unfold cnt; lia). assert (Hnf0 : 0 <= nf) by (unfold nf; lia).
unfold apart in Aca.
unfold art_cls_dealloc. destruct (art_cls_full c cl) eqn:EF; unfold art_cls_full in EF; fold cnt in EF.
-
apply Z.eqb_eq in EF. specialize (Hroom eq_refl).
set (h := art_ic_mc c / 2) in *. set (hn := Z.to_nat h). set (k := (length (cl_cache cl) - hn)%nat).
assert (Ehn : Z.of_nat hn = h) by (unfold hn; lia).
assert (Ek : Z.of_nat k = cnt - h) by (unfold k, cnt in *; lia).
set (ws := skipn k (cl_cache cl)).
assert (Lws : length ws = hn) by (unfold ws; rewrite length_skipn; unfold k; unfold cnt in *; lia).
assert (Nws : forall j, nth j ws 0 = nth (k + j) (cl_cache cl) 0) by (intros j; unfold ws; apply nth_skipn).
rewrite EF in Ccnt.
pose proof (art_lcd_full_a_fn regs M rom raw sp ca 1283032 c p (art_ic_mc c) H1 H2 H10 H11 H12 H13 ltac:(lia) Hsp' ltac:(eapply wr_sub; [exact W|lia|lia])
ltac:(lia) Hca ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ccnt Cmc) as RUN1.
destruct (art_f48_facts M sp raw regs ltac:(lia) Hsp') as (G1 & AG1).
destruct (art_f48_cells M sp raw regs ltac:(lia) Hsp') as (E1 & E8 & E9 & E18 & E19 & E20).
match type of RUN1 with msteps _ _ (mkst ?R1 _ _ _) => set (Ra := R1) in * end.
set (Xa := art_f48 M sp raw regs) in *.
assert (W1a : wrA Xa (sp - 48 - 272) 272) by (eapply wr_grows; [exact G1|]; eapply wr_sub; [exact W|lia|lia]).
assert (W1c : wrA Xa ca 2592) by (eapply wr_grows; [exact G1|exact Wca]).
assert (W1r : wrA Xa r 128) by (eapply wr_grows; [exact G1|exact Wr]).
assert (W1f : wrA Xa fa (cl_mfa cl)) by (eapply wr_grows; [exact G1|exact Wfa]).
assert (T1 : forall a (n : nat) v, apart a (Z.of_nat n) (sp - 48) 48 -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> cellA M a n v -> cellA Xa a n v).
{ intros a n v Ap Ha Hn C. apply (art_cell_tr _ M Xa a n v AG1); [cbn [art_gap fst snd]; split; [exact Ap|exact I]|exact Ha|exact Hn|exact C]. }
assert (Cspb1 : cellA Xa (1283032 + 32) 8 spb) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Cspb]).
assert (Cris1 : cellA Xa (1283032 + 48) 8 ris) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Cris]).
assert (Crel1 : cellA Xa (1283032 + 40) 4 0xffffffff) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Crel]).
assert (Cpc1 : cellA Xa 0x134380 8 0x1cc4e0) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Cpc]).
assert (Cpg1 : cellA Xa 0x1cc4e0 8 4096) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Cpg]).
assert (Crd1 : cellA Xa 0x10400 8 0xafffff00000fffff) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Crd]).
assert (Cmx1 : cellA Xa r 8 0) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Rmx]).
assert (Cnf1 : cellA Xa (r + 16) 8 nf) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Rnf]).
assert (Cmfa1 : cellA Xa (r + 24) 8 (cl_mfa cl)) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Rmfa]).
assert (Cnfr1 : cellA Xa (r + 80) 8 (cl_nfr cl mod 2 ^ 64)) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Rnfrn]).
assert (Ccnt1 : cellA Xa (ca + 80 * c) 4 (art_ic_mc c)) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Ccnt]).
assert (Cmc1 : cellA Xa (ca + 80 * c + 4) 4 (2 * h)) by (rewrite <- Emc; apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Cmc]).
clearbody Xa.
assert (Cws1 : forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA Xa (ca + 80 * c + 16 + 4 * (art_ic_mc c - h) + 4 * Z.of_nat j) 4 (nth j ws 0)).
{ intros j Hj. rewrite Lws in Hj. rewrite (Nws j).
assert (Lt : (k + j < length (cl_cache cl))%nat) by (unfold k; unfold cnt in *; lia).
split.
- assert (X : art_cptr_ok (AsanTab.class_size c) (cl_au cl) (nth (k + j) (cl_cache cl) 0)).
{ apply (proj1 (Forall_forall _ _) Hall). apply in_or_app. left. apply nth_In. exact Lt. }
pose proof (art_class_size_facts c Hc) as (Hsz & _).
pose proof (art_cptr_lt (AsanTab.class_size c) (cl_au cl) _ ltac:(lia) ltac:(lia) X). lia.
- pose proof (Cch (k + j)%nat Lt) as Cj. rewrite <- EF.
replace (ca + 80 * c + 16 + 4 * (cnt - h) + 4 * Z.of_nat j) with (ca + 80 * c + 16 + 4 * Z.of_nat (k + j)) by lia.
pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Hj'. fold cnt in Hj'.
apply (art_cell_tr _ M Xa _ _ _ AG1); [zgap|lia|cbn; lia|exact Cj]. }
destruct (art_lcdrain_run ws Ra Xa rom (0x54778 : bv 64)%bv (sp - 48) HI ca 1283032 c (art_ic_mc c) h spb ris qris nf (cl_mfa cl) (cl_nfr cl mod 2 ^ 64)
ltac:(unfold Ra; gres; bveq) ltac:(unfold ret_ok; bveq) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; exact H10) ltac:(unfold Ra; gres; reflexivity)
ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity)
HHI ltac:(lia) ltac:(lia) HHI' ltac:(lia) ltac:(lia) Hc Hspb Eris Eq Hris' Hca Hca' Hcai ltac:(unfold apart; lia)
ltac:(rewrite Lws; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hnfrn
W1a W1c W1r W1f Ccnt1 Cmc1 Cspb1 Cris1 Crel1 Cpc1 Cpg1 Crd1 Cmx1 Cnf1 Cmfa1 Cnfr1 Cws1)
as (r2 & M2 & RUN2 & B2 & BK & G2 & AG2 & Ccnt2 & Cmx2 & Cnf2 & Cnfr2 & Cfa2).
fold r fa in AG2, Cmx2, Cnf2, Cnfr2, Cfa2.
replace (sp - 48 - 272) with (sp - 320) in AG2 by lia.
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Q8. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as Q9. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as Q18.
pose proof (bv_unsigned_in_range 64 (getr regs 19)) as Q19. pose proof (bv_unsigned_in_range 64 (getr regs 20)) as Q20.
change (bv_modulus 64) with (2 ^ 64) in Q8, Q9, Q18, Q19, Q20.
assert (Csz2 : cellA M2 (ca + 80 * c + 8) 8 (art_ic_size c)) by ztr.
assert (Cspb2 : cellA M2 (1283032 + 32) 8 spb) by ztr.
assert (Csv2 : cellA M2 (ca + 2576) 8 (sv mod 2 ^ 64)) by ztr.
assert (D1 : cellA M2 (sp - 8) 8 (U raw)) by ztr. assert (D8 : cellA M2 (sp - 16) 8 (U (getr regs 8))) by ztr. assert (D9 : cellA M2 (sp - 24) 8 (U (getr regs 9))) by ztr.
assert (D18 : cellA M2 (sp - 32) 8 (U (getr regs 18))) by ztr. assert (D19 : cellA M2 (sp - 40) 8 (U (getr regs 19))) by ztr. assert (D20 : cellA M2 (sp - 48) 8 (U (getr regs 20))) by ztr.
pose proof (art_lcd_full_b_fn r2 M2 rom raw sp ca 1283032 c p spb w (art_ic_mc c - h) (art_ic_size c) (sv mod 2 ^ 64)
(U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))
B2 ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity) ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity) ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity)
ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity) ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity)
Hret ltac:(lia) Hsp' ltac:(lia) Hca ltac:(lia) Hca8 Hcai ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ep Hw ltac:(lia) ltac:(lia) Hsvn Q8 Q9 Q18 Q19 Q20
ltac:(eapply wr_grows; [exact G2|exact W1c]) Ccnt2 Csz2 Cspb2 Csv2 D1 D8 D9 D18 D19 D20) as RUN3.
match type of RUN3 with msteps _ _ (mkst ?R3 _ ?X3 _) => set (Rf := R3) in *; set (Mf := X3) in * end.
assert (G3 : mem_grows M2 Mf) by (unfold Mf; zgrows).
assert (AG3 : art_agree [(ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8)] M2 Mf).
{ unfold Mf. eapply art_agree_sub; [zagree|]. zsub. }
assert (Gf : mem_grows M Mf) by (eapply mem_grows_trans; [exact G1|]; eapply mem_grows_trans; [exact G2|exact G3]).
assert (Af : art_agree [(sp - 320, 320); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8); (fa + 4 * nf, 4 * h); (r, 8); (r + 16, 8); (r + 80, 8)] M Mf).
{ eapply art_agree_sub; [eapply art_agree_trans; [exact AG1|]; eapply art_agree_trans; [exact AG2|exact AG3]|]. zsub. }
exists Rf, Mf.
split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|exact RUN3]|].
split; [unfold Rf; gres; reflexivity|].
split. { intros x Hx. cbn [In] in Hx.
repeat (destruct Hx as [<-|Hx]; [unfold Rf; gres; first [reflexivity | apply Z_to_bv_bv_unsigned | rewrite BK by inl; unfold Ra; gres; reflexivity]|]). destruct Hx. }
split; [exact Gf|].
split. { eapply art_agree_sub; [exact Af|]. unfold art_lcd_fp. fold r fa. zsub. }
split.
+ split.
*
unfold art_cls_push, art_cls_return. cbn [cl_cache]. fold hn k. split.
-- rewrite length_app, length_firstn. cbn [length].
replace (Z.of_nat (Nat.min k (length (cl_cache cl)) + 1)) with (art_ic_mc c - h + 1) by (unfold cnt in *; lia). unfold Mf. zcell.
-- intros j Hj. rewrite length_app, length_firstn in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j k) as [Lt|Ge].
++ rewrite app_nth1 by (rewrite length_firstn; unfold cnt in *; lia). rewrite nth_firstn. replace (j <? k)%nat with true by (symmetry; apply Nat.ltb_lt; exact Lt).
assert (Ltc : (j < length (cl_cache cl))%nat) by (unfold k in Lt; lia).
pose proof (Cch j Ltc) as Cj. pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Hj'.
assert (Cj2 : cellA M2 (ca + 80 * c + 16 + 4 * Z.of_nat j) 4 (nth j (cl_cache cl) 0)) by ztr.
unfold Mf. zcell.
++ assert (Ej : j = k) by (unfold cnt in *; lia). subst j. rewrite app_nth2 by (rewrite length_firstn; unfold cnt in *; lia).
rewrite length_firstn. replace (k - Nat.min k (length (cl_cache cl)))%nat with O by (unfold cnt in *; lia). cbn [nth].
replace (Z.of_nat k) with (art_ic_mc c - h) by lia. unfold Mf. zcell.
*
apply (art_region_rep_ret spb ris c 0 0 cl (art_cls_push w (art_cls_return hn cl)) M Mf
[(sp - 320, 320); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8); (fa + 4 * nf, 4 * h); (r, 8); (r + 16, 8); (r + 80, 8)] ws);
try reflexivity; fold r fa nf; first [ lia | exact RR | exact Gf | exact Af | idtac ].
-- zgap.
-- zgap.
-- unfold Mf. zcell.
-- rewrite Lws, Ehn. unfold Mf. zcell.
-- cbn [art_cls_push art_cls_return cl_nfr]. rewrite Ehn. apply art_cell_mod_add. unfold Mf. zcell.
-- intros j Hj. pose proof (Cfa2 j Hj) as Cj. rewrite Lws in Hj. unfold Mf. zcell.
+ replace (sv - art_ic_size c) with (sv + (0 - art_ic_size c)) by lia. apply art_cell_mod_add. unfold Mf. zcell.
-
apply Z.eqb_neq in EF. clear Hroom.
pose proof (art_lcd_push_fn regs M rom raw sp ca 1283032 c p spb w (art_ic_mc c) cnt (art_ic_size c) (sv mod 2 ^ 64) H1 Hret H2 H10 H11 H12 H13
ltac:(lia) Hsp' ltac:(eapply wr_sub; [exact W|lia|lia]) ltac:(lia) Hca ltac:(lia) Hca8 Hcai ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ep Hw
ltac:(lia) ltac:(lia) ltac:(lia) Hsvn Wca Ccnt Cmc Ccsz Cspb Csvn) as RUN.
match type of RUN with msteps _ _ (mkst ?R _ ?X _) => set (Rf := R) in *; set (Mf := X) in * end.
assert (G : mem_grows M Mf) by (unfold Mf, art_f48; zgrows).
assert (A : art_agree [(sp - 48, 48); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8)] M Mf).
{ unfold Mf, art_f48. eapply art_agree_sub; [zagree|]. zsub. }
exists Rf, Mf.
split; [exact RUN|].
split; [unfold Rf; gres; reflexivity|].
split. { intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [unfold Rf; gres; reflexivity|]). destruct Hx. }
split; [exact G|].
split. { eapply art_agree_sub; [exact A|]. unfold art_lcd_fp. zsub. }
split.
+ split.
*
unfold art_cls_push. cbn [cl_cache]. split.
-- rewrite length_app. cbn [length]. replace (Z.of_nat (length (cl_cache cl) + 1)) with (cnt + 1) by (unfold cnt; lia). unfold Mf. zcell.
-- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length (cl_cache cl))) as [Lt|Ge].
++ rewrite app_nth1 by exact Lt. pose proof (Cch j Lt) as Cj. pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Hj'. fold cnt in Hj'.
unfold Mf, art_f48. zcell.
++ assert (Ej : j = length (cl_cache cl)) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. fold cnt.
unfold Mf. zcell.
*
apply (art_region_rep_ret spb ris c 0 0 cl (art_cls_push w cl) M Mf [(sp - 48, 48); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8)] []);
try reflexivity; fold r fa nf; first [ lia | exact RR | exact G | exact A | idtac ].
-- cbn [art_cls_push cl_free]. symmetry. apply app_nil_r.
-- zgap.
-- zgap.
-- ztr.
-- cbn [length]. replace (nf + Z.of_nat 0) with nf by lia. ztr.
-- cbn [art_cls_push cl_nfr]. ztr.
-- intros j Hj. cbn [length] in Hj. lia.
+ replace (sv - art_ic_size c) with (sv + (0 - art_ic_size c)) by lia. apply art_cell_mod_add. unfold Mf. zcell.
Qed.
End SE.
End FPY.
