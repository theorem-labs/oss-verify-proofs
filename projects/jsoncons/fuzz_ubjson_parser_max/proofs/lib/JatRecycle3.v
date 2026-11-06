(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JatLeaf JatAllocG JatPoison ArtRuns ArtRunsMem JatFp JatPopulate1 JatCellEx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatRecycle3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle3.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"]; ["5wr"; "6class_size"; "7msteps"; "8ret_ok"; "9art_agree"; ";art_f80"; ":art_f48"; "<getr"; "<mkst"; "<regupd"; "=mem_grows"; ">loaded_segments"; "?In"; "@add"; "@le"; "@lt"]; ["@modulo"; "@mul"; "@pow"; "@sub"; "0c"; "0ca"; "0cnt"; "0csz"; "0fx"; "0g18"; "0g19"; "0g20"; "0g21"; "0g22"; "0g23"; "0g8"]; ["0g9"; "0ia"; "0j"; "0mc"; "0nfr"; "0nfree"; "0p"; "0r"; "0raw"; "0regs"; "0regs'"; "0ris"; "0rom"; "0sp"; "0spb"; "ABV"]; ["AZ_to_bv"; "Abv"; "Abv_unsigned"; "0sv"; "0sz"; "0w"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Ltac zamoadd_da F D a old v CELL oktac altac :=
chain_step; [reflexivity
| eapply (art_step_amoadd_d_x0 _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a : word) (Z_to_bv 64 v : word) (Z_to_bv 64 old : word));
[ exact F | reflexivity | exact D
| gres; rwH; rewrite ?art_zb_addi, ?art_zb_add; first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]
| rewrite art_u_lit by lia; altac
| exact CELL | apply bytes_le_to_Z_8
| gres; rwH; first [reflexivity | f_equal; lia]
| oktac ]
| step_simpl ];
rewrite ?art_zb_add;
change (wbytes ?M0 (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 (old + v)))) with (Wn 8 M0 a (old + v)).
Definition art_f48 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20)).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_lcd_push_fn := (ltac2:(TCodec.tc2 tcn__JatRecycle3 "XK&;y5'R1yR0%211%5241'2y8%611%311p061':'7&Gr?(QO+1(5%33A21%6251r<%93A21&Cr=%211rA+2%<3J1:%?231&R0%12K7%C3K31rB+:%C3Q11A%F231%H3Q016rC+;%H3Q61F%K231%M3Q51;rD+<%M3Q;1K%Q0231%Q23Q:1@rE+=%Q23Q@1Q0%Q5231%Q73Q?1E&N&M+VbTP0+Q@%3221%521I&O&Q2+R0%22Q31%42I1&@&KrG&Q3%12I<%54431='6%B2QFQ6+O%D2Q81%4231+TP0%G21LrF+Ra0%I221%=2>H%L221&Q0+8%22B1z%R93R:21'9rH%Q321;+RPP0%Q6221%Q72Q54%6221%Q9246rI%Q:21Q3%Q<21Q:%Q=2=Q0+Q5%Q82R91%Q?2=1+Q?%Q;2R<1%Q=231rJ&Q1rK+Q0%QA2RB1%4231%QI2@1+@%721I%QL231%S63S7:1%QO2OE+L%QJ2RK1%QL2H1%QB241%R42Q4Q1%QO2Q2K%QE221%R72C<+QO%R22S31%R42Q01%QJ2<1%R62Q2R3%QL2>1rQ7rQ3%R54R421QG&?rQ8rQ4+R@rQ2%Q1221%RF241u4rM%95R>8321rQ9rQ5%Q829>%RM221+4%RO221rO%A5RF72:1rQ:rQ6%Q@2AB%S5221%S621R9u8rN%I5RN7321rQ;%S;28QE%L5S1215NrQ<+R`@%S?2N1%Q05S5319@'B&HvQ8rQ>+Z`gH%TL3U81TJ/01U8rQ=%756521<&I%137TNA%TD2U>J%332TG1%U43UBS1U2%U72;1%63321+9%U83UF1U6%U;2?1%:3421%T52Q;G%TN2UH1%=33TJ1rQ1%SL2S:1%U22UL1%A34TI1%RH2QOQI%T=2QC1%RJ2QJQ@%T?221%U82V21%G36TJ1%U:2V4R0%I32TG1+>%UK3V91UI%TF2R2UK%U?2V91%N3531+?%V03V>1UN%UC2V=R=%Q23421+B%V43VB1V2%V72Q;1%Q63421+C%V83VF1V6%V;2Q?1%Q:3421+D%V<3VJ1V:%V?2QC1%Q>3421&=&F%14QCR9R1QG%SH2RIRO%U=2RC1%54RG31H%U?22SE%SL2RBRL%UA221%94RK41S0rQ0%UD21Q;%<4R>3Q@1%R45R3>R<1R9%R63U<QN1p0R81p0R=1p0RA1p0RJ1p0S31p0S>1p0SB1p0SE1p0SJ1p0SL1p0T01p0T61p0TB1p0TI1p0TK1p0TO1p0U11p0U91p0U?1p0UE1p0UH1p0UN1p0V51p0V;1p0VB1p0VH1p0VN1p0W41p0W:1p0WB1p0WF1pT8X11pR@X21pR>X31pS8X41pT<X51pSNX61pS>X71pR:X81pS4X91pR<X:1pSLX;1pSBXC1pSJX>1pJX?1pSDXE1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 4%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 5%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 6%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 7%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 8%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 9%nat 0%nat).
Variable w : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 10%nat 0%nat).
Variable mc : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 11%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 12%nat 0%nat).
Variable csz : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 13%nat 0%nat).
Variable sv : ltac:(sec_ty2 constr:(SEC_T_art_lcd_push_fn) 14%nat 0%nat).
Lemma art_lcd_push_fn : ltac:(sec_stmt2 constr:(SEC_T_art_lcd_push_fn) 15%nat 0%nat).
Proof using Type regs M rom raw sp ca ia c p spb w mc cnt csz sv.
intros H1 Hret H2 H10 H11 H12 H13 Hsp Hsp' W Hc Hca Hca' Hca8 Hcai Hia Hia' Hspb Hspb' Ep Hw Hcnt Hmc Hcsz Hsv Wca Ccnt Cmc Ccsz Cspb Csv.
zstep (ltac:(oF' 0x542f8%Z)) (ltac:(oD' 0x542f8%Z)).
zsd (ltac:(oF' 0x542fc%Z)) (ltac:(oD' 0x542fc%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x54300%Z)) (ltac:(oD' 0x54300%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x54304%Z)) (ltac:(oD' 0x54304%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x54308%Z)) (ltac:(oD' 0x54308%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x5430c%Z)) (ltac:(oD' 0x5430c%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x54310%Z)) (ltac:(oD' 0x54310%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zbft (ltac:(oF' 0x54314%Z)) (ltac:(oD' 0x54314%Z)).
zstep (ltac:(oF' 0x54318%Z)) (ltac:(oD' 0x54318%Z)).
zbft (ltac:(oF' 0x5431c%Z)) (ltac:(oD' 0x5431c%Z)).
zstep (ltac:(oF' 0x54320%Z)) (ltac:(oD' 0x54320%Z)). zstep (ltac:(oF' 0x54324%Z)) (ltac:(oD' 0x54324%Z)). zstep (ltac:(oF' 0x54328%Z)) (ltac:(oD' 0x54328%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmc' : cellA X (ca + 80 * c + 4) 4 mc) by zcell; assert (Ccnt' : cellA X (ca + 80 * c) 4 cnt) by zcell;
assert (Cspb' : cellA X (ia + 32) 8 spb) by zcell; assert (Ccsz' : cellA X (ca + 80 * c + 8) 8 csz) by zcell; assert (Csv' : cellA X (ca + 2576) 8 sv) by zcell;
assert (Wca' : wrA X ca 2592) by zwr end.
zlw (ltac:(oF' 0x5432c%Z)) (ltac:(oD' 0x5432c%Z)) (ca + 80 * c + 4) Cmc'.
zbft (ltac:(oF' 0x54330%Z)) (ltac:(oD' 0x54330%Z)).
zlw (ltac:(oF' 0x54334%Z)) (ltac:(oD' 0x54334%Z)) (ca + 80 * c) Ccnt'.
zbft (ltac:(oF' 0x54338%Z)) (ltac:(oD' 0x54338%Z)).
zld (ltac:(oF' 0x5433c%Z)) (ltac:(oD' 0x5433c%Z)) (ia + 32) Cspb'.
zstep (ltac:(oF' 0x54340%Z)) (ltac:(oD' 0x54340%Z)). zstep (ltac:(oF' 0x54344%Z)) (ltac:(oD' 0x54344%Z)). zstep (ltac:(oF' 0x54348%Z)) (ltac:(oD' 0x54348%Z)). zstep (ltac:(oF' 0x5434c%Z)) (ltac:(oD' 0x5434c%Z)). zstep (ltac:(oF' 0x54350%Z)) (ltac:(oD' 0x54350%Z)).
zld (ltac:(oF' 0x54354%Z)) (ltac:(oD' 0x54354%Z)) (ca + 80 * c + 8) Ccsz'.
zstep (ltac:(oF' 0x54358%Z)) (ltac:(oD' 0x54358%Z)).
stepn (ltac:(oF' 0x5435c%Z)) (ltac:(oD' 0x5435c%Z)). rwH. rewrite (art_zb_srli_exact _ 30 (cnt * 4)) by lia.
zstep (ltac:(oF' 0x54360%Z)) (ltac:(oD' 0x54360%Z)). zstep (ltac:(oF' 0x54364%Z)) (ltac:(oD' 0x54364%Z)).
stepn (ltac:(oF' 0x54368%Z)) (ltac:(oD' 0x54368%Z)). rwH. rewrite (art_zb_srli_exact _ 4 w) by lia.
zsw (ltac:(oF' 0x5436c%Z)) (ltac:(oD' 0x5436c%Z)) (ca + 80 * c) (cnt + 1) ltac:(zwok').
zsw (ltac:(oF' 0x54370%Z)) (ltac:(oD' 0x54370%Z)) (ca + 80 * c + 16 + 4 * cnt) w ltac:(zwok').
zstep (ltac:(oF' 0x54374%Z)) (ltac:(oD' 0x54374%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csv2 : cellA X (ca + 2576) 8 sv) by zcell; assert (Wsv2 : wokA X (ca + 2576) 8) by zwok end.
zamoadd_da (ltac:(oF' 0x54378%Z)) (ltac:(oD' 0x54378%Z)) (ca + 2576) sv (0 - csz) Csv2 ltac:(exact Wsv2) ltac:(rewrite Z.add_mod, Hca8 by lia; reflexivity).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
assert (G9 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (G18 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell;
assert (G19 : cellA X (sp - 40) 8 (U (getr regs 19))) by zcell; assert (G20 : cellA X (sp - 48) 8 (U (getr regs 20))) by zcell end.
zld (ltac:(oF' 0x5437c%Z)) (ltac:(oD' 0x5437c%Z)) (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x54380%Z)) (ltac:(oD' 0x54380%Z)) (sp - 16) G8. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x54384%Z)) (ltac:(oD' 0x54384%Z)) (sp - 24) G9. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x54388%Z)) (ltac:(oD' 0x54388%Z)) (sp - 32) G18. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x5438c%Z)) (ltac:(oD' 0x5438c%Z)) (sp - 40) G19. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x54390%Z)) (ltac:(oD' 0x54390%Z)) (sp - 48) G20. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x54394%Z)) (ltac:(oD' 0x54394%Z)).
stepret (ltac:(oF' 0x54398%Z)) (ltac:(oD' 0x54398%Z)) raw ltac:(reflexivity).
unfold art_f48. zret.
Qed.
End SE.
Definition art_f80 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)))
(sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22))) (sp - 72) (U (getr regs 23)).
Section SE.
Local Abbreviation SEC_T_art_mrtos_a := (ltac2:(TCodec.tc2 tcn__JatRecycle3 "V;&;y5'R1yR0%211%5241'2y8%611%311p061':'7&Gr8(QO+1(5%33A21%6251r5%93A21r9+2%93G17%<231&R0%12H7%@3H31r:+:%@3N1>%C231%E3M16r;+<%E3Q31C%H231%J3Q21;r<+=%J3Q81H%M231z%B2Q91%Q13Q931&N&M+VbTP0+R@%3221%521M&O&Q2+R0%22Q01%42K1&@&Kr>&Q3%12K<%54431='6%B2Q@Q3+N%D2Q51%4231+RPP0%G21Nr=%H21A%J21H%K2NQ2+QO%F2QD1%H2Q51%>241&?rCr?+Q@%Q3221u8%65J521>'8'B&HvQ8rF+ZcVH%R<3RH1R:/01RHrErD%8576321r1+ZcZD%RC3RO1RA/01RO&ErB%2491G=%@5?7419%B3Q>91%RL29RA%Q>25QI%RA2S81%S03S831+B%RO3S=1RM%S22?1&Ar@%211%RI2S@1%S83S@51+C%S73SE1S5%S:2G1rA%RO2SF1%S>3SF31+E%S=3SK1S;%S@2M1%SB3SJ1RB+F%SA3SO1S?%SD2Q11%S82SOQB%SG3SO21+;%SF3T41SD%SI2Q61&Q1+7%RD2SB1%32I1%SA2T81%T03T861%T;1T<&L(0+3%T23T@1T0+4%T43TB1T2+H%T63TD1T4+I%T83TF1T6+J%T:3TH1T8+K%T<3TJ1T:(1%11@%?3A31%@3B61%A3C91%B3D<1%C3E?1%D3FB1%F3GR41r3r2%TJ221rH%TL213%TN3U631p071pS@O1%S>2Q11%S?2Q;1%S@2QA1%SA2QF1%SB2QM1%SC2R61%SD2R;1qSFU?1%S02U@1p0S21p0S:1p0S@1p0SD1p0SG1p0SM1p0T41p0T:1p0TA1p0TI1p0TO1p0U51p0U=1pSHUH1pR:UI1pS4UJ1pSLUK1pSBV31pSJUN1pJUO1pSDV51")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_a) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_a) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_a) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_a) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_a) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_a) 5%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_a) 6%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_a) 7%nat 0%nat).
Lemma art_mrtos_a : ltac:(sec_stmt2 constr:(SEC_T_art_mrtos_a) 8%nat 0%nat).
Proof using Type regs M rom raw sp ia c ris.
intros H1 H2 H10 H12 H13 Hsp Hsp' W Hc Hia Hia' Hris Cris.
destruct (Z_le_gt_dec c 16) as [Lc|Gc].
- eexists. split.
{ zstep (ltac:(oF' 0x54cd8%Z)) (ltac:(oD' 0x54cd8%Z)).
zsd (ltac:(oF' 0x54cdc%Z)) (ltac:(oD' 0x54cdc%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x54ce0%Z)) (ltac:(oD' 0x54ce0%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd (ltac:(oF' 0x54ce4%Z)) (ltac:(oD' 0x54ce4%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x54ce8%Z)) (ltac:(oD' 0x54ce8%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd (ltac:(oF' 0x54cec%Z)) (ltac:(oD' 0x54cec%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x54cf0%Z)) (ltac:(oD' 0x54cf0%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x54cf4%Z)) (ltac:(oD' 0x54cf4%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd (ltac:(oF' 0x54cf8%Z)) (ltac:(oD' 0x54cf8%Z)) (sp - 64) (U (getr regs 22)) ltac:(rewok W). zsd (ltac:(oF' 0x54cfc%Z)) (ltac:(oD' 0x54cfc%Z)) (sp - 72) (U (getr regs 23)) ltac:(rewok W).
zstep (ltac:(oF' 0x54d00%Z)) (ltac:(oD' 0x54d00%Z)). zstep (ltac:(oF' 0x54d04%Z)) (ltac:(oD' 0x54d04%Z)). zstep (ltac:(oF' 0x54d08%Z)) (ltac:(oD' 0x54d08%Z)). zstep (ltac:(oF' 0x54d0c%Z)) (ltac:(oD' 0x54d0c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cris' : cellA X (ia + 48) 8 ris) by zcell end.
zld (ltac:(oF' 0x54d10%Z)) (ltac:(oD' 0x54d10%Z)) (ia + 48) Cris'.
zstep (ltac:(oF' 0x54d14%Z)) (ltac:(oD' 0x54d14%Z)). zstep (ltac:(oF' 0x54d18%Z)) (ltac:(oD' 0x54d18%Z)).
zbft (ltac:(oF' 0x54d1c%Z)) (ltac:(oD' 0x54d1c%Z)).
zstep (ltac:(oF' 0x54d20%Z)) (ltac:(oD' 0x54d20%Z)).
zbft (ltac:(oF' 0x54d24%Z)) (ltac:(oD' 0x54d24%Z)).
zstep (ltac:(oF' 0x54d28%Z)) (ltac:(oD' 0x54d28%Z)).
stepn (ltac:(oF' 0x54d2c%Z)) (ltac:(oD' 0x54d2c%Z)).
unfold art_f80. apply mst_refl. }
rewrite (art_class_size_small c ltac:(lia)).
split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
- eexists. split.
{ zstep (ltac:(oF' 0x54cd8%Z)) (ltac:(oD' 0x54cd8%Z)).
zsd (ltac:(oF' 0x54cdc%Z)) (ltac:(oD' 0x54cdc%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x54ce0%Z)) (ltac:(oD' 0x54ce0%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd (ltac:(oF' 0x54ce4%Z)) (ltac:(oD' 0x54ce4%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x54ce8%Z)) (ltac:(oD' 0x54ce8%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd (ltac:(oF' 0x54cec%Z)) (ltac:(oD' 0x54cec%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x54cf0%Z)) (ltac:(oD' 0x54cf0%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x54cf4%Z)) (ltac:(oD' 0x54cf4%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd (ltac:(oF' 0x54cf8%Z)) (ltac:(oD' 0x54cf8%Z)) (sp - 64) (U (getr regs 22)) ltac:(rewok W). zsd (ltac:(oF' 0x54cfc%Z)) (ltac:(oD' 0x54cfc%Z)) (sp - 72) (U (getr regs 23)) ltac:(rewok W).
zstep (ltac:(oF' 0x54d00%Z)) (ltac:(oD' 0x54d00%Z)). zstep (ltac:(oF' 0x54d04%Z)) (ltac:(oD' 0x54d04%Z)). zstep (ltac:(oF' 0x54d08%Z)) (ltac:(oD' 0x54d08%Z)). zstep (ltac:(oF' 0x54d0c%Z)) (ltac:(oD' 0x54d0c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cris' : cellA X (ia + 48) 8 ris) by zcell end.
zld (ltac:(oF' 0x54d10%Z)) (ltac:(oD' 0x54d10%Z)) (ia + 48) Cris'.
zstep (ltac:(oF' 0x54d14%Z)) (ltac:(oD' 0x54d14%Z)). zstep (ltac:(oF' 0x54d18%Z)) (ltac:(oD' 0x54d18%Z)).
zbft (ltac:(oF' 0x54d1c%Z)) (ltac:(oD' 0x54d1c%Z)).
zstep (ltac:(oF' 0x54d20%Z)) (ltac:(oD' 0x54d20%Z)).
zbtk (ltac:(oF' 0x54d24%Z)) (ltac:(oD' 0x54d24%Z)).
zstep (ltac:(oF' 0x54d30%Z)) (ltac:(oD' 0x54d30%Z)). zstep (ltac:(oF' 0x54d34%Z)) (ltac:(oD' 0x54d34%Z)). zstep (ltac:(oF' 0x54d38%Z)) (ltac:(oD' 0x54d38%Z)). zstep (ltac:(oF' 0x54d3c%Z)) (ltac:(oD' 0x54d3c%Z)). zstep (ltac:(oF' 0x54d40%Z)) (ltac:(oD' 0x54d40%Z)). zstep (ltac:(oF' 0x54d44%Z)) (ltac:(oD' 0x54d44%Z)).
zstep (ltac:(oF' 0x54d48%Z)) (ltac:(oD' 0x54d48%Z)). zstep (ltac:(oF' 0x54d4c%Z)) (ltac:(oD' 0x54d4c%Z)). zstep (ltac:(oF' 0x54d50%Z)) (ltac:(oD' 0x54d50%Z)).
fold (art_pop_szw c). rewrite (art_pop_szw_ok c ltac:(lia)).
unfold art_f80. apply mst_refl. }
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_mrtos_b := (ltac2:(TCodec.tc2 tcn__JatRecycle3 "Z7&;y5'R1yR0%211%5241'2y8%611%311p061':'7&GrD(QO+2(5%33A21%6251&R0&Q3r@+R@%3221%52F1%>3F71rE+B%>3L1<%A231r=%<2M1%E3M31rF+C%E3Q31C%H231rA%C2Q41%L3Q431rG+E%L3Q:1J%O231z%J2Q;1%Q33Q;31rH+F%Q33QA1Q1%Q6231%Q83Q@1=rI+;%Q83QF1Q6%Q;231&Q1rC&Q2+7%22Q=1%5241%Q;2QL1%QD3QL81&C%11I&N%12Q=K&O+R0%<2QG1%32H1'6+1%821Q2+N%:2Q41%5231+RPP0%=21K&MrJ%221=+VbTP0%B221%C2Q9Q1+T0%O21B%8271+Q?%Q02R;1%G231+Q0%K21<%L2=@%G221%N2QD?+Q8%Q82RC1%O2B1%L241%Q12DO%N261&?&KrQ=+QVY`Hu8+QiYm0%6554321rQ>+TP0%9582451rQ?rQ;%Q321Bu4+SoooooO%?5>5321rQ@rQ:%R12Q37%Q:221+@%Q<221rQ8%G5F72C1rQArQ<%R92Q;1%QB2@1%QC21S=%M5L51I7rQB%R>2Q@M%QG271+RH%QI221%Q35Q251O=rQC+8%SI2F1&R2%12T=@%Q95Q853Q51rQD%SN2CGrQ9%Q=5Q<32Q91rQE+H%T32B1%QA5Q@31Q=5rQF%T62?QN%QD5QC21Q@8rQG%T92<QL%QG5QF21QC;rQH+Q@%T=2<1%QK5QJ31QG?rQI+QH%TA2<1%QO5QN31QKCrQJ%TD2<S3%R25R121QNFrQK+R8%TH2=1%R65R531R2J'8'B&HvQ8rQN+ZcZD%U63UB1U4/01UBrQMrQL%8576321r1%:591@43%<3RC31%U@23U;%U:2UKF%UC3UK21%UA3UOQCU?%UD271%U>2UOQL%UG3UO21+9%UF3V41UD%UI2<1%UC2V4R7%UL3V421%UL2?U<%UF2V7RB%UO3V721%UO2BU8%UI2V:RK%V23V:21+D%V13V?1UO%V42G1%UN2V?S3%V73V?21%V72JU9%V12VBS;%V:3VB21%V:2MU5%V42VERG%V=3VE21+G%V<3VJ1V:%V?2Q21%V92VJS:%VB3VJ21%VM1VN&L(0+3%VD3W21VB+4%VF3W41VD%VG3W5R?VE+I%VI3W71VG+J%VK3W91VI+K%VM3W;1VK(1%11?%>3@31%?3A61%@3B91%A3C<1%B3D>1%C3EA1%E3FQK1r3r2%W;221rR0%W=213%W?3WG31p071pS@N1%UE2Q01%UF2Q61%UG2Q:1%UH2Q>1%UI2QD1%UJ2QH1%UK2QL1%UL2R21%UM2R71%UN2R;1qSFX31%RJ2X41p0RL1p0S11p0S51p0S:1p0S?1p0SC1p0SG1p0SL1p0T11p0T81p0T?1p0TF1p0TO1p0U61p0U:1p0UB1p0UC1p0UD1p0UE1p0UF1p0UG1p0UH1p0UI1p0UJ1p0UK1p0UN1p0V41p0V91p0V@1p0VB1p0VH1p0VK1p0W21p0W71p0W:1p0W=1p0WJ1p0X01p0X81p0X@1p0XH1pRNY81pRLY91pRJY:1pRHY;1pRFY<1pRDY=1pS2Y>1pS0Y?1pS6Y@1pS:YA1pS<YB1pT:YC1pSHYD1pR:YE1pS4YF1pSLYG1pSBYO1pSJYJ1pJYK1pSDZ11")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 5%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 6%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 7%nat 0%nat).
Variable sz : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 8%nat 0%nat).
Variable nfree : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 9%nat 0%nat).
Variable nfr : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 10%nat 0%nat).
Variable j : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 11%nat 0%nat).
Variable g8 : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 12%nat 0%nat).
Variable g9 : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 13%nat 0%nat).
Variable g18 : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 14%nat 0%nat).
Variable g19 : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 15%nat 0%nat).
Variable g20 : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 16%nat 0%nat).
Variable g21 : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 17%nat 0%nat).
Variable g22 : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 18%nat 0%nat).
Variable g23 : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_b) 19%nat 0%nat).
Lemma art_mrtos_b : ltac:(sec_stmt2 constr:(SEC_T_art_mrtos_b) 20%nat 0%nat).
Proof using Type regs M rom raw sp ia c ris sz nfree nfr j g8 g9 g18 g19 g20 g21 g22 g23.
intros H2 H18 H19 H21 H22 H11 Hret Hsp Hsp' Hc Hia Hia' Hris Hris' Hsz Hnfree Hnfr Hj
Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 Hg23 Cpc Cpg Crel Cnfree Cnfr Cj F1 F8 F9 F18 F19 F20 F21 F22 F23.
assert (HP : 0 <= nfree * sz < 2 ^ 64) by nia.
set (P := nfree * sz) in *.
set (Y := ((nfr - j) * sz) mod 2 ^ 64).
assert (HY : 0 <= Y < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (EPI : forall rg, getr rg 2 = Z_to_bv 64 (sp - 80) ->
exists regs', msteps ASEGS (mkst rg (0x54e80 : word) M rom) (mkst regs' raw M rom)
/\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18 /\ getr regs' 19 = Z_to_bv 64 g19
/\ getr regs' 20 = Z_to_bv 64 g20 /\ getr regs' 21 = Z_to_bv 64 g21 /\ getr regs' 22 = Z_to_bv 64 g22 /\ getr regs' 23 = Z_to_bv 64 g23
/\ (forall r : reg, In r [3; 4; 24; 25; 26; 27]%bv -> getr regs' r = getr rg r)).
{ intros rg G2. eexists. split.
{ zld (ltac:(oF' 0x54e80%Z)) (ltac:(oD' 0x54e80%Z)) (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x54e84%Z)) (ltac:(oD' 0x54e84%Z)) (sp - 16) F8. zld (ltac:(oF' 0x54e88%Z)) (ltac:(oD' 0x54e88%Z)) (sp - 24) F9. zld (ltac:(oF' 0x54e8c%Z)) (ltac:(oD' 0x54e8c%Z)) (sp - 32) F18. zld (ltac:(oF' 0x54e90%Z)) (ltac:(oD' 0x54e90%Z)) (sp - 40) F19.
zld (ltac:(oF' 0x54e94%Z)) (ltac:(oD' 0x54e94%Z)) (sp - 48) F20. zld (ltac:(oF' 0x54e98%Z)) (ltac:(oD' 0x54e98%Z)) (sp - 56) F21. zld (ltac:(oF' 0x54e9c%Z)) (ltac:(oD' 0x54e9c%Z)) (sp - 64) F22. zld (ltac:(oF' 0x54ea0%Z)) (ltac:(oD' 0x54ea0%Z)) (sp - 72) F23.
zstep (ltac:(oF' 0x54ea4%Z)) (ltac:(oD' 0x54ea4%Z)).
stepret (ltac:(oF' 0x54ea8%Z)) (ltac:(oD' 0x54ea8%Z)) raw ltac:(reflexivity).
apply mst_refl. }
split; [gres; f_equal; lia|]. do 8 (split; [gres; reflexivity|]).
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
eassert (RUN0 : msteps ASEGS (mkst regs (0x54d54 : word) M rom) _).
{ stepn (ltac:(oF' 0x54d54%Z)) (ltac:(oD' 0x54d54%Z)).
zld (ltac:(oF' 0x54d58%Z)) (ltac:(oD' 0x54d58%Z)) 0x132618 Cpc.
zld (ltac:(oF' 0x54d5c%Z)) (ltac:(oD' 0x54d5c%Z)) 0x1ca7a0 Cpg.
zstep (ltac:(oF' 0x54d60%Z)) (ltac:(oD' 0x54d60%Z)).
zbft (ltac:(oF' 0x54d64%Z)) (ltac:(oD' 0x54d64%Z)).
zld (ltac:(oF' 0x54d68%Z)) (ltac:(oD' 0x54d68%Z)) (ris + 128 * c + 16) Cnfree.
zstep (ltac:(oF' 0x54d6c%Z)) (ltac:(oD' 0x54d6c%Z)). fold P.
apply mst_refl. }
destruct (Z_lt_le_dec P 4096) as [LP|GP].
-
eassert (RUN1 : msteps ASEGS _ _).
{ eapply msteps_trans; [exact RUN0|]. zbft (ltac:(oF' 0x54d70%Z)) (ltac:(oD' 0x54d70%Z)). stepn (ltac:(oF' 0x54d74%Z)) (ltac:(oD' 0x54d74%Z)). apply mst_refl. }
match type of RUN1 with msteps _ _ (mkst ?R _ _ _) => destruct (EPI R ltac:(gres; exact H2)) as (r' & RUN2 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & EK) end.
exists r'. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
do 9 (split; [assumption|]). intros r Hr. rewrite (EK r Hr). cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
- eassert (RUN1 : msteps ASEGS _ _).
{ eapply msteps_trans; [exact RUN0|]. zbtk (ltac:(oF' 0x54d70%Z)) (ltac:(oD' 0x54d70%Z)).
zld (ltac:(oF' 0x54d8c%Z)) (ltac:(oD' 0x54d8c%Z)) (ris + 128 * c + 80) Cnfr.
zld (ltac:(oF' 0x54d90%Z)) (ltac:(oD' 0x54d90%Z)) (ris + 128 * c + 88) Cj.
zstep (ltac:(oF' 0x54d94%Z)) (ltac:(oD' 0x54d94%Z)). zstep (ltac:(oF' 0x54d98%Z)) (ltac:(oD' 0x54d98%Z)).
rewrite <- (art_zb_mod64 ((nfr - j) * sz)). fold Y.
apply mst_refl. }
destruct (Z_lt_le_dec Y 4096) as [LY|GY].
+
eassert (RUN1b : msteps ASEGS _ _).
{ eapply msteps_trans; [exact RUN1|]. zbtk (ltac:(oF' 0x54d9c%Z)) (ltac:(oD' 0x54d9c%Z)). apply mst_refl. }
match type of RUN1b with msteps _ _ (mkst ?R _ _ _) => destruct (EPI R ltac:(gres; exact H2)) as (r' & RUN2 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & EK) end.
exists r'. split; [eapply msteps_trans; [exact RUN1b|exact RUN2]|].
do 9 (split; [assumption|]). intros r Hr. rewrite (EK r Hr). cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
+
eassert (RUN1b : msteps ASEGS _ _).
{ eapply msteps_trans; [exact RUN1|]. zbft (ltac:(oF' 0x54d9c%Z)) (ltac:(oD' 0x54d9c%Z)). zbft (ltac:(oF' 0x54da0%Z)) (ltac:(oD' 0x54da0%Z)).
zlw (ltac:(oF' 0x54da4%Z)) (ltac:(oD' 0x54da4%Z)) (ia + 40) Crel.
stepb_tk (ltac:(oF' 0x54da8%Z)) (ltac:(oD' 0x54da8%Z)) ltac:(rwH; reflexivity).
apply mst_refl. }
match type of RUN1b with msteps _ _ (mkst ?R _ _ _) => destruct (EPI R ltac:(gres; exact H2)) as (r' & RUN2 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & EK) end.
exists r'. split; [eapply msteps_trans; [exact RUN1b|exact RUN2]|].
do 9 (split; [assumption|]). intros r Hr. rewrite (EK r Hr). cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_mrtos_ret := (ltac2:(TCodec.tc2 tcn__JatRecycle3 "WH&;y5'R1yR0%211%5241'2y8%611%311p061':'7&Gr:(QO+1(5%33A21%6251r7%93A21&Cr8%211r<+2%<3J1:%?231&R0%12K7%C3K31r=+:%C3Q11A%F231%H3Q016r>+<%H3Q61F%K231%M3Q51;r?+=%M3Q;1K%Q0231z%B2Q<1%Q43Q<31&N&M+VbTP0+R@%3221%521M&O&Q2+R0%22Q01%42K1&@&KrA&Q3%12K<%54431='6%B2QCQ3+N%D2Q51%4231+RPP0%G21Nr@%H21A%J21H%K2IQ2&Q1+T0%221F%N271+Q?%J2QH1%L231&>rD%G21Q2rB%;2:1%Q72K1%644Q61<%Q:2Q=M+Q8%Q52R31%Q72Q01%M241%Q92Q2Q6%O261rJrE%G2F1%QC2@1%Q:4Q941H&?rKrG+Q@%QI221u8%65Q@521:rL+QVY`H+QiYm0%:5QD3251rM+TP0%=5QG2481rN%R42DJu4+SoooooO%B5QL4321rOrI%Q?2Q>J%R;221+@%R=221rH%J5R472E1rQ0%QF2QEK%RB2Q21%RC21RA%O5R941J6'8'B&HvQ8rQ3+ZcVH%SN3T:1SL/01T:rQ2rQ1%8576321r1&E%145JB9%<5;3C15%>3RI51%T:25SL%SK2TEN%T=3TE21%TH1TI&L(0+3%T?3TM1T=+4%TA3TO1T?+8%TC3U11TA+9%TE3U31TC+B%TG3U51TE+C%TI3U71TG+D%TK3U91TI+E%TM3U;1TK+F%TO3U=1TM+G%U13U?1TO+H%U33UA1U1+I%U53UC1U3+J%U73UE1U5+K%U93UG1U7(1%11Q0%O3Q131%Q03Q261%Q13Q391%Q23Q4<1%Q33Q5?1%Q43Q6B1%Q53Q7E1%Q63Q8H1%Q73Q9K1%Q83Q:N1%Q93Q;Q11%Q:3Q<Q41%Q;3Q=Q71%Q<3Q>Q:1%Q>3Q?QG1r3r2%UO221rQ5%V1213%V33V;31p071pS@QG1%T@2QI1%TA2QM1qSFV?1%R>2V@1p0R@1p0RF1p0RO1p0S51p0S91p0S>1p0SF1p0SL1p0SO1p0T51p0T=1p0TE1p0TG1p0TK1p0TN1p0U41p0U;1p0UA1p0UH1p0V01p0V61p0V<1p0VD1p0VH1pS:W31pS<W41pSHW51pR:W61pS4W71pSLW81pSBW@1pSJW;1pJW<1pSDWB1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_ret) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_ret) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_ret) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_ret) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_ret) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_ret) 5%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_ret) 6%nat 0%nat).
Variable ris : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_ret) 7%nat 0%nat).
Variable nfree : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_ret) 8%nat 0%nat).
Variable nfr : ltac:(sec_ty2 constr:(SEC_T_art_mrtos_ret) 9%nat 0%nat).
Lemma art_mrtos_ret : ltac:(sec_stmt2 constr:(SEC_T_art_mrtos_ret) 10%nat 0%nat).
Proof using Type regs M rom raw sp ia c ris nfree nfr.
intros H1 Hret H2 H10 H12 H13 Hsp Hsp' W Hc Hia Hia' Hris Hris' Ar Hnfree Hnfr Wr Cris Cpc Cpg Crel Cnfree Cnfr.
destruct (art_cell_exists M (ris + 128 * c + 88) 8 ltac:(lia) ltac:(right; lia) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wr|lia|cbn; lia])) as (j & Hj & Cj).
destruct (art_mrtos_a regs M rom raw sp ia c ris H1 H2 H10 H12 H13 Hsp Hsp' W Hc Hia Hia' ltac:(lia) Cris) as (r1 & RUN1 & A2 & A18 & A19 & A21 & A22 & A11 & AK).
destruct (art_class_size_facts c Hc) as [Hsz _].
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R8. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R9. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as R18.
pose proof (bv_unsigned_in_range 64 (getr regs 19)) as R19. pose proof (bv_unsigned_in_range 64 (getr regs 20)) as R20. pose proof (bv_unsigned_in_range 64 (getr regs 21)) as R21.
pose proof (bv_unsigned_in_range 64 (getr regs 22)) as R22. pose proof (bv_unsigned_in_range 64 (getr regs 23)) as R23. change (bv_modulus 64) with (2 ^ 64) in *.
unfold apart in Ar.
assert (CELLS : let X := art_f80 M sp raw regs in
cellA X 0x132618 8 0x1ca7a0 /\ cellA X 0x1ca7a0 8 4096 /\ cellA X (ia + 40) 4 0xffffffff
/\ cellA X (ris + 128 * c + 16) 8 nfree /\ cellA X (ris + 128 * c + 80) 8 nfr /\ cellA X (ris + 128 * c + 88) 8 j
/\ cellA X (sp - 8) 8 (U raw) /\ cellA X (sp - 16) 8 (U (getr regs 8)) /\ cellA X (sp - 24) 8 (U (getr regs 9)) /\ cellA X (sp - 32) 8 (U (getr regs 18))
/\ cellA X (sp - 40) 8 (U (getr regs 19)) /\ cellA X (sp - 48) 8 (U (getr regs 20)) /\ cellA X (sp - 56) 8 (U (getr regs 21)) /\ cellA X (sp - 64) 8 (U (getr regs 22))
/\ cellA X (sp - 72) 8 (U (getr regs 23))).
{ cbv zeta. unfold art_f80. repeat split; zcell. }
cbv zeta in CELLS. destruct CELLS as (X1 & X2 & X3 & X4 & X5 & X6 & G1 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23).
destruct (art_mrtos_b r1 (art_f80 M sp raw regs) rom raw sp ia c ris (AsanTab.class_size c) nfree nfr j _ _ _ _ _ _ _ _ A2 A18 A19 A21 A22 A11 Hret ltac:(lia) Hsp' Hc Hia Hia' ltac:(lia) Hris' Hsz
Hnfree Hnfr Hj R8 R9 R18 R19 R20 R21 R22 R23 X1 X2 X3 X4 X5 X6 G1 G8 G9 G18 G19 G20 G21 G22 G23) as (r2 & RUN2 & B2 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & BK).
exists r2. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|]. split; [exact B2|].
intros r Hr. cbn [In] in Hr.
destruct Hr as [<-|Hr]; [rewrite BK by (cbn; tauto); apply AK; cbn; tauto|]. destruct Hr as [<-|Hr]; [rewrite BK by (cbn; tauto); apply AK; cbn; tauto|].
destruct Hr as [<-|Hr]; [rewrite B8; apply Z_to_bv_bv_unsigned|]. destruct Hr as [<-|Hr]; [rewrite B9; apply Z_to_bv_bv_unsigned|].
destruct Hr as [<-|Hr]; [rewrite B18; apply Z_to_bv_bv_unsigned|]. destruct Hr as [<-|Hr]; [rewrite B19; apply Z_to_bv_bv_unsigned|].
destruct Hr as [<-|Hr]; [rewrite B20; apply Z_to_bv_bv_unsigned|]. destruct Hr as [<-|Hr]; [rewrite B21; apply Z_to_bv_bv_unsigned|].
destruct Hr as [<-|Hr]; [rewrite B22; apply Z_to_bv_bv_unsigned|]. destruct Hr as [<-|Hr]; [rewrite B23; apply Z_to_bv_bv_unsigned|].
repeat (destruct Hr as [<-|Hr]; [rewrite BK by (cbn; tauto); apply AK; cbn; tauto|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_f80_facts := (ltac2:(TCodec.tc2 tcn__JatRecycle3 "QA'R1yR0%211'2y8%511%311p051':&;y5%2219&N+R@r3%3221&Or4&Q2+2+R0%3221%6251'6&Jr6&Er5%2431;>%5241&D(0'4%12II(3&Q3%129G%34MM1H(1%116%93731%;31@=%C2=1p0E1p0M1pSDQ21pSBQ<1pSLQ71pJQ91")) (only parsing).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_f80_facts) 0%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_f80_facts) 1%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_f80_facts) 2%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_f80_facts) 3%nat 0%nat).
Lemma art_f80_facts : ltac:(sec_stmt2 constr:(SEC_T_art_f80_facts) 4%nat 0%nat).
Proof using Type M sp raw regs.
intros Hsp Hsp'.
unfold art_f80. split; [zgrows|]. eapply art_agree_sub; [zagree|]. zsub. Qed.
End SE.
#[using="Type"] Lemma art_f48_facts : ltac2:(TCodec.tc2 tcn__JatRecycle3 "QA'R1yR0%211'2y8%511%311p051':&;y5%2219&N+Q@r3%3221&Or4&Q2+2+R0%3221%6251'6&Jr6&Fr5%2431;>%5241&D(0'4%12II(3&Q3%129G%34MM1H(1%116%93731%;31@=%C2=1p0E1p0M1pSDQ21pSBQ<1pSLQ71pJQ91").
Proof. intros M sp raw regs Hsp Hsp'. unfold art_f48. split; [zgrows|]. eapply art_agree_sub; [zagree|]. zsub. Qed.
#[using="Type"] Lemma art_f48_cells : ltac2:(TCodec.tc2 tcn__JatRecycle3 "RD'R1yR0%211'2y8%511%311p051':&;y5%2219&N+Q@r3%3221&Or4&Q2+2+R0%3221%6251'6&?&K&Fr6r5%3421<?&Q3+8%2241u8&R2%12Q2B%<5;7431+@%82:1&G(QO(5%23Q0;1%42M1%:2Q;1%E5D@7<1+H%A2C1+9%93Q718%;2Q41%A2QB1%L5KG5C1+Q0%H2J1+B%@3Q>1?%B2Q;1%H2QI1%Q35Q2N5J1+Q8%O2Q11+C%G3QE1F%I2QB1%O2R01%Q:5Q9Q55Q11%Q52Q7QF+D%M3QK1L%O2QH1%Q52R61%Q@5Q?Q;5Q71%QB271%QC2?1%QD2G1%QE2O1%QF2Q91p0QH1p0R01pSDR51pSBR?1pSLR:1pJR<1").
Proof. intros M sp raw regs H1 H2. unfold art_f48. repeat split; zcell. Qed.
End FPX.
