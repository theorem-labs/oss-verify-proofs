(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JbtLeaf JbtAllocG JbtPoison JbtSecAlloc ArtRuns ArtRunsMem JbtFp JbtCellEx JbtImgCell JbtSecRSpec JbtPoison3 JbtRecycle1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtRecycle2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle2.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "3Z"; "0HI"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"; "5wok"; "5wr"; "6msteps"; "7ret_ok"; "8art_tsd"]; [":art_secd_d_mem"; "9art_secd_a_mem"; ";getr"; ";mkst"; ";regupd"; "<loaded_segments"; "=add"; "=le"; "=lt"; "=modulo"; "=mul"; "=pow"; "=sub"; "0c88"; "0c96"; "0ca"]; ["0ctx"; "0fx"; "0h"; "0idx"; "0key"; "0last"; "0ms"; "0n"; "0nf"; "0parr"; "0raw"; "0regs"; "0rom"; "0s16"; "0s24"; "0sp"]; [">BV"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0t"; "0tp"; "0tsd"; "0x18"; "0x8"; "0x9"]]).
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
Definition art_secd_a_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (ms parr idx n last nf ca s16 s24 : Z) : word -> option byte :=
Wn 1 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 8 (Wn 4 (art_flush_frame M sp raw regs)
(0x139418 + 616) 1) (0x139418 + 56) (n - 1)) (0x139418 + 64) 0) (0x139418 + 80) (nf + 1)) (0x139418 + 88) (ca - ms)) (parr + 8 * idx) last) (last + 24) idx)
(0x139688 + 16) (s16 + (0 - ms))) (0x139688 + 24) (s24 + (0 - ms))) (0x139418 + 616) 0.
Ltac zamoadd_dc F D a old v CELL oktac :=
chain_step; [reflexivity
| eapply (art_step_amoadd_d_x0 _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a : word) (Z_to_bv 64 v : word) (Z_to_bv 64 old : word));
[ exact F | reflexivity | exact D
| gres; rwH; rewrite ?art_zb_addi, ?art_zb_add; first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]
| rewrite art_u_lit by lia; reflexivity
| exact CELL | apply bytes_le_to_Z_8
| gres; rwH; first [reflexivity | f_equal; lia]
| oktac ]
| step_simpl ];
rewrite ?art_zb_add;
change (wbytes ?M0 (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 (old + v)))) with (Wn 8 M0 a (old + v)).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_secd_a_fn := (ltac2:(TCodec.tc2 tcn__JbtRecycle2 "Y6&6y5'QByR0%211%5241'0y8%611%311p061'4'3&Br@(Q@+1(1%33A21%6251r=%93A21rA+2%93G17%<231&QA%12H7%@3H31rB+:%@3N1>%C231+QWUPH%82O1%G3O31rC+;%G3Q51E%J231+QWUd8%?2Q61%N3Q631rD+<%N3Q<1L%Q1231&Fr>+TP0%3221%I2Q@1%Q83Q@61&G+Vb\P0%221Q9&L+Q0%22M1%62Q51&H&K+R0%22Q81%42L1&<&ErG%<2I;%44321<%A2@Q2%H2LFrE%D221&I%123Jz%R13R221%I2HQH%Q02QBFrH%L221&9+H%Q52Q@1+8+@%543271%Q32Q2E&JrF%2261%Q=2<1rK%Q9221rI%72;M%?4214Q@rJ%:2>C%B421Q1Q;'2%QA2J4%Q;258%3221+D%Q=2RC1%Q?291rN%QH2Q11%QB22Q?%:221%QD2>QA%<2;1&:rQ9u8%35QC2RD1R4rQ:+c8%R92RG1u4%85QH421Q>rQ;%R=2RKQ7rQ4%<5QL32:1rQ<+QH%RB2S01rQ3%A5R142?1rQ=+R@%RG2S51rQ2%F5R642D1rQ>+RH%RL2S:1%J5R:31H5rQ?%RO2S6QH%M5R=21K8rQ@%S22S9QN%Q05R@21N;rQA%Q25RB1EQ0ErQB%S72BR1%Q55RE21Q3HrQC%S:2@R6%Q85RH21Q6OrQD%R32R7M%S>2I1%Q<5RL31Q:ArQE%S82Q1T@%R82R<1%SC2I1%QA5S141Q?Q8&;rQF%R=2RAM%SH2J1%44S631QDrQG%SK2Q6RG%74S921QG'=&CvQ1rQI+Zal@%U23U>1U0/01U>rQH%756521;&D+ZbT4%TM2UD1%339U61%T12JT0%U02UG1%633U31+5%U>3UL1U<%T62QOQ9%U52UL1%;3531+6%UC3V11UA%U92V0SG%?3421%UF3V4S@UD%U<2V3Q>%B3321+9%UJ3V81UH%E3314%F31U<5%UB2V9QG%H32U71%I31U1;+=%V13V?1UO%UG2V>R1%M3421+>%V53VC1V3+QWUdH%UL2VC1%Q23531+?%V:3VH1V8%V02VGRA%Q63421%V=3VKT6V;%U52TAR8%V42VK1%Q:3431+A%VB3W01V@%Q=331F+B%VE3W31VC%Q@331I+_YU@%VH3W41VF/01W4&A%1=QGR;R5QKRERGRJRMS1S6S;S?SD%QN5QM631R2%R03U:QH1p0R21p0R61p0R<1p0RB1p0RG1p0RK1p0RO1p0S21p0S61p0S:1p0S?1p0SE1p0SK1p0T01p0T61p0T;1p0T<1p0T=1p0T>1p0TA1p0TF1p0TJ1p0TO1p0U31p0U71p0U>1p0U@1p0UG1p0UK1p0UM1p0V21p0V61p0V81p0V>1p0VD1p0VI1p0VM1p0W81p0W@1p0WH1p0X01pRNX;1pRLX<1pR0X=1pRBX>1pR<X?1pR@X@1pR8XA1pRDXB1pR>XC1pR6XD1p<XE1pS0XF1pRFXN1pRJXI1p@XJ1pRHY01")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 4%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 5%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 6%nat 0%nat).
Variable ms : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 7%nat 0%nat).
Variable parr : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 8%nat 0%nat).
Variable idx : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 9%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 10%nat 0%nat).
Variable last : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 11%nat 0%nat).
Variable nf : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 12%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 13%nat 0%nat).
Variable s16 : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 14%nat 0%nat).
Variable s24 : ltac:(sec_ty2 constr:(SEC_T_art_secd_a_fn) 15%nat 0%nat).
Lemma art_secd_a_fn : ltac:(sec_stmt2 constr:(SEC_T_art_secd_a_fn) 16%nat 0%nat).
Proof using Type regs M rom raw sp HI h ms parr idx n last nf ca s16 s24.
intros H1 H2 H10 H11 H12 HHI Hsp Hsp' W Hh Hh' Hh4 Hl Hl' Alh Hparr Hparr' Aph Apl Hidx Hn Hms Hnf Hca Hs16 Hs24
Cpg Clk Cparr Cn Cnf Cca C16 C24 Chh Chms Chidx Cslot Clast Wslot Wlast.
pose proof (art_img_wr M 0x139418 1024 ltac:(lia) ltac:(lia) ltac:(lia)) as Wimg.
zstep (ltac:(oF' 0x54790%Z)) (ltac:(oD' 0x54790%Z)).
zsd (ltac:(oF' 0x54794%Z)) (ltac:(oD' 0x54794%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x54798%Z)) (ltac:(oD' 0x54798%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x5479c%Z)) (ltac:(oD' 0x5479c%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x547a0%Z)) (ltac:(oD' 0x547a0%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg' : cellA X 0x139418 8 4096) by zcell end.
zld (ltac:(oF' 0x547a4%Z)) (ltac:(oD' 0x547a4%Z)) 0x139418 Cpg'.
zstep (ltac:(oF' 0x547a8%Z)) (ltac:(oD' 0x547a8%Z)).
stepn (ltac:(oF' 0x547ac%Z)) (ltac:(oD' 0x547ac%Z)). rwH. rewrite art_zb_and by lia.
replace (Z.land 4095 (h + 4096)) with 0 by (change 4095 with (Z.ones 12); rewrite Z.land_comm, Z.land_ones by lia; change (2 ^ 12) with 4096; rewrite Z.add_mod, Hh4 by lia; reflexivity).
zbft (ltac:(oF' 0x547b0%Z)) (ltac:(oD' 0x547b0%Z)).
zstep (ltac:(oF' 0x547b4%Z)) (ltac:(oD' 0x547b4%Z)). zstep (ltac:(oF' 0x547b8%Z)) (ltac:(oD' 0x547b8%Z)).
stepn (ltac:(oF' 0x547bc%Z)) (ltac:(oD' 0x547bc%Z)). rwH. zclosed (0x139418 + 616).
zstep (ltac:(oF' 0x547c0%Z)) (ltac:(oD' 0x547c0%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x139418 + 616) 4 0) by zcell; assert (Wlk' : wokA X (0x139418 + 616) 4) by zwok end.
zcas6 (ltac:(oF' 0x547c4%Z)) (ltac:(oD' 0x547c4%Z)) (ltac:(oF' 0x547c8%Z)) (ltac:(oD' 0x547c8%Z)) (ltac:(oF' 0x547cc%Z)) (ltac:(oD' 0x547cc%Z)) (ltac:(oF' 0x547d0%Z)) (ltac:(oD' 0x547d0%Z)) (ltac:(oF' 0x547d4%Z)) (ltac:(oD' 0x547d4%Z)) (ltac:(oF' 0x547d8%Z)) (ltac:(oD' 0x547d8%Z)) (0x139418 + 616) 0 1 1 1 Clk' Wlk'.
zbft (ltac:(oF' 0x547dc%Z)) (ltac:(oD' 0x547dc%Z)).
stepn (ltac:(oF' 0x547e0%Z)) (ltac:(oD' 0x547e0%Z)). rwH. zclosed 0.
zstep (ltac:(oF' 0x547e4%Z)) (ltac:(oD' 0x547e4%Z)). replace (h + 4096 - 4096) with h by lia.
zbft (ltac:(oF' 0x547e8%Z)) (ltac:(oD' 0x547e8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chidx' : cellA X (h + 24) 8 idx) by zcell; assert (Cparr' : cellA X (0x139418 + 8) 8 parr) by zcell;
assert (Cslot' : cellA X (parr + 8 * idx) 8 h) by zcell; assert (Cn' : cellA X (0x139418 + 56) 8 n) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell;
assert (Cnf' : cellA X (0x139418 + 80) 8 nf) by zcell; assert (Cca' : cellA X (0x139418 + 88) 8 ca) by zcell; assert (Clast' : cellA X (parr + 8 * (n - 1)) 8 last) by zcell end.
zld (ltac:(oF' 0x547ec%Z)) (ltac:(oD' 0x547ec%Z)) (h + 24) Chidx'.
zld (ltac:(oF' 0x547f0%Z)) (ltac:(oD' 0x547f0%Z)) (0x139418 + 8) Cparr'.
zstep (ltac:(oF' 0x547f4%Z)) (ltac:(oD' 0x547f4%Z)). zstep (ltac:(oF' 0x547f8%Z)) (ltac:(oD' 0x547f8%Z)).
zld (ltac:(oF' 0x547fc%Z)) (ltac:(oD' 0x547fc%Z)) (parr + 8 * idx) Cslot'.
zbft (ltac:(oF' 0x54800%Z)) (ltac:(oD' 0x54800%Z)).
zld (ltac:(oF' 0x54804%Z)) (ltac:(oD' 0x54804%Z)) (0x139418 + 56) Cn'.
zbft (ltac:(oF' 0x54808%Z)) (ltac:(oD' 0x54808%Z)).
zstep (ltac:(oF' 0x5480c%Z)) (ltac:(oD' 0x5480c%Z)).
zld (ltac:(oF' 0x54810%Z)) (ltac:(oD' 0x54810%Z)) (h + 8) Chms'.
zstep (ltac:(oF' 0x54814%Z)) (ltac:(oD' 0x54814%Z)).
zld (ltac:(oF' 0x54818%Z)) (ltac:(oD' 0x54818%Z)) (0x139418 + 80) Cnf'.
zld (ltac:(oF' 0x5481c%Z)) (ltac:(oD' 0x5481c%Z)) (0x139418 + 88) Cca'.
zstep (ltac:(oF' 0x54820%Z)) (ltac:(oD' 0x54820%Z)).
zld (ltac:(oF' 0x54824%Z)) (ltac:(oD' 0x54824%Z)) (parr + 8 * (n - 1)) Clast'.
zstep (ltac:(oF' 0x54828%Z)) (ltac:(oD' 0x54828%Z)). zstep (ltac:(oF' 0x5482c%Z)) (ltac:(oD' 0x5482c%Z)).
zsd (ltac:(oF' 0x54830%Z)) (ltac:(oD' 0x54830%Z)) (0x139418 + 56) (n - 1) ltac:(zwok').
zsb (ltac:(oF' 0x54834%Z)) (ltac:(oD' 0x54834%Z)) (0x139418 + 64) 0 ltac:(zwok').
zsd (ltac:(oF' 0x54838%Z)) (ltac:(oD' 0x54838%Z)) (0x139418 + 80) (nf + 1) ltac:(zwok').
zsd (ltac:(oF' 0x5483c%Z)) (ltac:(oD' 0x5483c%Z)) (0x139418 + 88) (ca - ms) ltac:(zwok').
zstep (ltac:(oF' 0x54840%Z)) (ltac:(oD' 0x54840%Z)). zstep (ltac:(oF' 0x54844%Z)) (ltac:(oD' 0x54844%Z)).
zsd (ltac:(oF' 0x54848%Z)) (ltac:(oD' 0x54848%Z)) (parr + 8 * idx) last ltac:(zwok').
zsd (ltac:(oF' 0x5484c%Z)) (ltac:(oD' 0x5484c%Z)) (last + 24) idx ltac:(zwok').
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (0x139688 + 16) 8 s16) by zcell; assert (W16' : wokA X (0x139688 + 16) 8) by zwok end.
zamoadd_dc (ltac:(oF' 0x54850%Z)) (ltac:(oD' 0x54850%Z)) (0x139688 + 16) s16 (0 - ms) C16' ltac:(exact W16').
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chms2 : cellA X (h + 8) 8 ms) by zcell end.
zld (ltac:(oF' 0x54854%Z)) (ltac:(oD' 0x54854%Z)) (h + 8) Chms2.
zstep (ltac:(oF' 0x54858%Z)) (ltac:(oD' 0x54858%Z)). zstep (ltac:(oF' 0x5485c%Z)) (ltac:(oD' 0x5485c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C24' : cellA X (0x139688 + 24) 8 s24) by zcell; assert (W24' : wokA X (0x139688 + 24) 8) by zwok end.
zamoadd_dc (ltac:(oF' 0x54860%Z)) (ltac:(oD' 0x54860%Z)) (0x139688 + 24) s24 (0 - ms) C24' ltac:(exact W24').
stepfence (ltac:(oF' 0x54864%Z)) (ltac:(oD' 0x54864%Z)).
zsb (ltac:(oF' 0x54868%Z)) (ltac:(oD' 0x54868%Z)) (0x139418 + 616) 0 ltac:(zwok').
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chh3 : cellA X h 8 h) by zcell; assert (Chms3 : cellA X (h + 8) 8 ms) by zcell end.
zld (ltac:(oF' 0x5486c%Z)) (ltac:(oD' 0x5486c%Z)) h Chh3.
zld (ltac:(oF' 0x54870%Z)) (ltac:(oD' 0x54870%Z)) (h + 8) Chms3.
zstep (ltac:(oF' 0x54874%Z)) (ltac:(oD' 0x54874%Z)). zstep (ltac:(oF' 0x54878%Z)) (ltac:(oD' 0x54878%Z)). zstep (ltac:(oF' 0x5487c%Z)) (ltac:(oD' 0x5487c%Z)).
stepn (ltac:(oF' 0x54880%Z)) (ltac:(oD' 0x54880%Z)).
unfold art_secd_a_mem, art_flush_frame. zret.
Qed.
End SE.
Definition art_secd_d_mem (M : word -> option byte) (sp : Z) (raw : word) (t ms x8 x9 x18 c88 c96 : Z) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 40) 0x54894) (sp - 56) 0x82434) (t + 2800 + 88) (c88 + 1)) (t + 2800 + 96) (c96 + ms)) (sp - 8) (U raw)) (sp - 16) x8) (sp - 24) x9) (sp - 32) x18.
Section SE.
Local Abbreviation SEC_T_art_secd_d_fn := (ltac2:(TCodec.tc2 tcn__JbtRecycle2 "WM&6y5'QByR0%211%5241'0y8%611%311p061'4'3&BrB(Q@+2(1%33A21%6251&QA&Lr>+Q0%3221%52F1%>3F71rC+4%>3L1<%A231r=%<2M1%E3M31rD+8%E3Q31C%H231r9%C2Q41%L3Q431rE+B%L3Q:1J%O231%Q13Q916&G+Vb\P0rA%3221+S0%N2H1%62Q61&H&K+R0%22Q81%42G1&<&ErH%Q82D6%443217r?%B2A1&Fr@+TP0%3221rF%H221'2z%D217%E28B%4221%N24:%6213&?rQ1rLrKrJrI%6654321H%Q72B2%E24CrO%Q:221%H22QFrQ0%Q=221rN&J%12QK7%N231%O21QM%QC21B+U0%Q2271rQ2%QG221&9rM%24<Q51Q5rQ8%Q@4Q?1CQ7&:rQ9rQ6%RI21R;u8&QCrQ7%22S?1%85QH7541rQ:+@%S1251%<5QL318KrQ;+H%S52A1%@5R031<OrQ<%S82AS6%C5R321?Q2rQ=rQ3%F5R621B1rQ>rQ4%R321S1%J5R:31F5rQ?+Rg@%R72K1+RH%R9221%Q05R@51LQArQ@%R<2L6%R=21RL%Q45RD31Q0QE'=&CvQ1rQB+ZbT@%T63TB1T4/01TBrQA%756521<&D+1%T<3TJ1T:+accD%T92TJ1%53;31+Q@%T;2N1%T=2TN1%934T@1%T?2U0QF%;32T01+9%TG3U51TE%TC2U4RO%?3421+:%TK3U91TI%TG2U8QJ%C3421+;%TO3U=1TM%F331<+<%U23U@1U0%I331;+=%U53UC1U3%SD2S6R8%U22UC1%N3531+>%U:3UH1U8%SI2RFQ0%U72UH1%Q33531+A%U?3UM1U=+VG%U<2UM1%Q83531%Q931TGG+a]`4%UE3V11UC/01V1&@rQ5%2:QAR6R2RORK1R5R8S4SI%QH5QG741QM%QJ3T?QB1p0QL1p0R11p0R81p0R=1p0RA1p0RE1p0RJ1p0RO1p0S91p0S<1p0S@1p0SE1p0SL1p0T01p0T41p0T61p0T>1p0T?1p0T@1p0TA1p0TB1p0TE1p0TK1p0U21p0U51p0U;1p0UA1p0UE1p0UJ1p0V01p0V81p0V@1pQNW01pQLW11pS@W21pSDW31pSBW41pR>W51pR6W61pS:W71pR2W81pS>W91pR:W:1pS<W;1p<W<1pS0W=1pRFWE1pRJW@1p@WA1pRHWG1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 4%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 5%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 6%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 7%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 8%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 9%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 10%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 11%nat 0%nat).
Variable ms : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 12%nat 0%nat).
Variable x8 : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 13%nat 0%nat).
Variable x9 : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 14%nat 0%nat).
Variable x18 : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 15%nat 0%nat).
Variable c88 : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 16%nat 0%nat).
Variable c96 : ltac:(sec_ty2 constr:(SEC_T_art_secd_d_fn) 17%nat 0%nat).
Lemma art_secd_d_fn : ltac:(sec_stmt2 constr:(SEC_T_art_secd_d_fn) 18%nat 0%nat).
Proof using Type regs M rom raw sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96.
intros H2 H4 H8 H18 HHI Hsp Hsp' W Hh Hh' Hms Hx8 Hx9 Hx18 Hc88 Hc96 TSD Ht Ht' Htp Htsd Hctx Ath Wt F1 F8 F9 F18 Chh Chms C88 C96.
pose proof TSD as (_ & _ & _ & _ & _ & R).
stepn (ltac:(oF' 0x54890%Z)) (ltac:(oD' 0x54890%Z)).
zcall (art_thread_stats_fn _ _ _ (0x54894 : word) (sp - 32) tp key tsd ctx t).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C96' : cellA X (t + 2800 + 96) 8 c96) by zcell; assert (C88' : cellA X (t + 2800 + 88) 8 c88) by zcell;
assert (Chh' : cellA X h 8 h) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell; assert (Wt' : wrA X t 4096) by zwr end.
zld (ltac:(oF' 0x54894%Z)) (ltac:(oD' 0x54894%Z)) (t + 2800 + 96) C96'.
zld (ltac:(oF' 0x54898%Z)) (ltac:(oD' 0x54898%Z)) (t + 2800 + 88) C88'.
zld (ltac:(oF' 0x5489c%Z)) (ltac:(oD' 0x5489c%Z)) h Chh'.
zld (ltac:(oF' 0x548a0%Z)) (ltac:(oD' 0x548a0%Z)) (h + 8) Chms'.
zstep (ltac:(oF' 0x548a4%Z)) (ltac:(oD' 0x548a4%Z)). zstep (ltac:(oF' 0x548a8%Z)) (ltac:(oD' 0x548a8%Z)).
zsd (ltac:(oF' 0x548ac%Z)) (ltac:(oD' 0x548ac%Z)) (t + 2800 + 88) (c88 + 1) ltac:(zwok').
zsd (ltac:(oF' 0x548b0%Z)) (ltac:(oD' 0x548b0%Z)) (t + 2800 + 96) (c96 + ms) ltac:(zwok').
zstep (ltac:(oF' 0x548b4%Z)) (ltac:(oD' 0x548b4%Z)). zstep (ltac:(oF' 0x548b8%Z)) (ltac:(oD' 0x548b8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell; assert (W' : wrA X (sp - 64) 64) by zwr end.
zld (ltac:(oF' 0x548bc%Z)) (ltac:(oD' 0x548bc%Z)) (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x548c0%Z)) (ltac:(oD' 0x548c0%Z)) (sp - 16) G8.
zld (ltac:(oF' 0x548c4%Z)) (ltac:(oD' 0x548c4%Z)) (sp - 24) G9.
zld (ltac:(oF' 0x548c8%Z)) (ltac:(oD' 0x548c8%Z)) (sp - 32) G18.
zstep (ltac:(oF' 0x548cc%Z)) (ltac:(oD' 0x548cc%Z)).
stepn (ltac:(oF' 0x548d0%Z)) (ltac:(oD' 0x548d0%Z)).
zstep (ltac:(oF' 0x8ce44%Z)) (ltac:(oD' 0x8ce44%Z)).
zsd (ltac:(oF' 0x8ce48%Z)) (ltac:(oD' 0x8ce48%Z)) (sp - 8) (U raw) ltac:(zwok'). zsd (ltac:(oF' 0x8ce4c%Z)) (ltac:(oD' 0x8ce4c%Z)) (sp - 16) x8 ltac:(zwok').
zsd (ltac:(oF' 0x8ce50%Z)) (ltac:(oD' 0x8ce50%Z)) (sp - 24) x9 ltac:(zwok'). zsd (ltac:(oF' 0x8ce54%Z)) (ltac:(oD' 0x8ce54%Z)) (sp - 32) x18 ltac:(zwok').
zbft (ltac:(oF' 0x8ce58%Z)) (ltac:(oD' 0x8ce58%Z)).
zstep (ltac:(oF' 0x8ce5c%Z)) (ltac:(oD' 0x8ce5c%Z)).
zbft (ltac:(oF' 0x8ce60%Z)) (ltac:(oD' 0x8ce60%Z)).
zstep (ltac:(oF' 0x8ce64%Z)) (ltac:(oD' 0x8ce64%Z)). zstep (ltac:(oF' 0x8ce68%Z)) (ltac:(oD' 0x8ce68%Z)). zstep (ltac:(oF' 0x8ce6c%Z)) (ltac:(oD' 0x8ce6c%Z)).
stepn (ltac:(oF' 0x8ce70%Z)) (ltac:(oD' 0x8ce70%Z)).
zstep (ltac:(oF' 0x8b600%Z)) (ltac:(oD' 0x8b600%Z)).
unfold art_secd_d_mem. zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_secd_e_fn := (ltac2:(TCodec.tc2 tcn__JbtRecycle2 "U:&6y5'QByR0%211%5241'0y8%611%311p061'4'3&Br9(Q@+1(1%33A21%6251&QA+accD%22C1%;3C41r:+2%;3I19%>231&Lr6+Q@%3221%<2M1%E3M61r;+8%E3Q31C%H231%B2Q39%K3Q321r<+:%K3Q91I%N231z%I2Q:1%Q23Q:31&>%11H&G&F+Vb\P0%221F%421M&H&K+R0%22Q01%42H1'2%;2@J%2213&;&ErCr@+Q4%Q7221u4%746521&:rDrA%Q=21Q6u8&QCrB%22R:1%85?7541rE+@%QE251%<5C318ArF+H%QI2E1%@5G31<ErG+Q0%QM2B1%D5K31@IrH+QV`l@+Qii[8%H5O32D1rI+T@%Q?241%L5Q331HQF'=&CvQ1rK+a]`8%RI3S51RG/01S5rJ%756521<&D%137RKB%RJ2S;G%332RE1%RL2S=Q1%532R=1+9%S43SB1S2%S02SAQ=%93421%S22SCQ3%;32R=1+;%S:3SH1S8%>331R=+<%S=3SK1S;+_ooooooooolP0%S:2SK1%C3531+=%SB3T01S@+_ooooooooolP1%S?2T01%H3531+B%SG3T51SE%SC2T4R7%L3421&8%S>2QCR8+_oooooneZeZe:%34R8Q221%Q95Q85QB1Q>%Q;3R?Q31p0Q=1p0QB1p0QG1p0QL1p0R11p0R61p0R@1p0RI1p0RJ1p0RK1p0RL1p0S01p0S61p0S<1p0S?1p0SG1p0SN1p0T91pS@TF1pSDTG1pSBTH1pR>TI1pS0TJ1pRFU21pRJTM1p@TN1pRHU41")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_secd_e_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_secd_e_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_secd_e_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_secd_e_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_secd_e_fn) 4%nat 0%nat).
Variable ms : ltac:(sec_ty2 constr:(SEC_T_art_secd_e_fn) 5%nat 0%nat).
Variable x8 : ltac:(sec_ty2 constr:(SEC_T_art_secd_e_fn) 6%nat 0%nat).
Variable x9 : ltac:(sec_ty2 constr:(SEC_T_art_secd_e_fn) 7%nat 0%nat).
Variable x18 : ltac:(sec_ty2 constr:(SEC_T_art_secd_e_fn) 8%nat 0%nat).
Lemma art_secd_e_fn : ltac:(sec_stmt2 constr:(SEC_T_art_secd_e_fn) 9%nat 0%nat).
Proof using Type regs M rom raw sp ms x8 x9 x18.
intros H1 H2 H8 H10 Hret Hsp Hsp' Hms Hx8 Hx9 Hx18 Wk F1 F8 F9 F18 CF C144.
stepret (ltac:(oF' 0x8b608%Z)) (ltac:(oD' 0x8b608%Z)) (Z_to_bv 64 0x8ce74 : word) ltac:(rwH; reflexivity).
zstep (ltac:(oF' 0x8ce74%Z)) (ltac:(oD' 0x8ce74%Z)). zstep (ltac:(oF' 0x8ce78%Z)) (ltac:(oD' 0x8ce78%Z)).
zsw (ltac:(oF' 0x8ce7c%Z)) (ltac:(oD' 0x8ce7c%Z)) (sp - 36) 18446744072277895850 ltac:(exact Wk).
zstep (ltac:(oF' 0x8ce80%Z)) (ltac:(oD' 0x8ce80%Z)).
stepn (ltac:(oF' 0x8ce84%Z)) (ltac:(oD' 0x8ce84%Z)).
zstep (ltac:(oF' 0x8b5d4%Z)) (ltac:(oD' 0x8b5d4%Z)). zstep (ltac:(oF' 0x8b5d8%Z)) (ltac:(oD' 0x8b5d8%Z)).
zbtk (ltac:(oF' 0x8b5dc%Z)) (ltac:(oD' 0x8b5dc%Z)).
zstep (ltac:(oF' 0x8b5ec%Z)) (ltac:(oD' 0x8b5ec%Z)).
stepret (ltac:(oF' 0x8b5f0%Z)) (ltac:(oD' 0x8b5f0%Z)) (Z_to_bv 64 0x8ce88 : word) ltac:(rwH; reflexivity).
zbft (ltac:(oF' 0x8ce88%Z)) (ltac:(oD' 0x8ce88%Z)).
zstep (ltac:(oF' 0x8ce8c%Z)) (ltac:(oD' 0x8ce8c%Z)).
stepn (ltac:(oF' 0x8ce90%Z)) (ltac:(oD' 0x8ce90%Z)).
zstep (ltac:(oF' 0x87500%Z)) (ltac:(oD' 0x87500%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CF' : cellA X 0x134390 8 0x1ce568) by zcell; assert (C144' : cellA X (0x1ce568 + 144) 8 0) by zcell;
assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell end.
zld (ltac:(oF' 0x87504%Z)) (ltac:(oD' 0x87504%Z)) 0x134390 CF'.
zld (ltac:(oF' 0x87508%Z)) (ltac:(oD' 0x87508%Z)) (0x1ce568 + 144) C144'.
zbtk (ltac:(oF' 0x8750c%Z)) (ltac:(oD' 0x8750c%Z)).
stepret (ltac:(oF' 0x87520%Z)) (ltac:(oD' 0x87520%Z)) (Z_to_bv 64 0x8ce94 : word) ltac:(rwH; reflexivity).
zld (ltac:(oF' 0x8ce94%Z)) (ltac:(oD' 0x8ce94%Z)) (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x8ce98%Z)) (ltac:(oD' 0x8ce98%Z)) (sp - 16) G8.
zld (ltac:(oF' 0x8ce9c%Z)) (ltac:(oD' 0x8ce9c%Z)) (sp - 24) G9.
zld (ltac:(oF' 0x8cea0%Z)) (ltac:(oD' 0x8cea0%Z)) (sp - 32) G18.
zstep (ltac:(oF' 0x8cea4%Z)) (ltac:(oD' 0x8cea4%Z)).
stepret (ltac:(oF' 0x8cea8%Z)) (ltac:(oD' 0x8cea8%Z)) raw ltac:(reflexivity).
zret.
Qed.
End SE.
End FPX.
