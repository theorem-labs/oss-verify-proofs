(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import muslA.Jb0SumsMemset_code muslA.Jb0SumsMemset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtPoison () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "1option"; "2I"; "2and"; "2eq"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5wr"; "6msteps"; "7SB"; "7art_layout"; "7art_poison_frame"; "7kHighMemBeg"]; ["7kHighMemEnd"; "8getr"; "8mkst"; "8regupd"; "9loaded_segments"; ":add"; ":div"; ":le"; ":lt"; ":modulo"; ":of_nat"; ":pow"; ":sub"; "0a"; "0fx"; "0n"]; ["0p"; "0raw"; "0regs"; "0rom"; "0sp"; ";BV"; ";Z_to_bv"; ";bv"; ";bv_unsigned"; "0v"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition SB : Z := 0x7fff8000.
Definition kHighMemEnd : Z := 0x7fffffffffff.
Definition kHighMemBeg : Z := 0x10007fff8000.
Definition art_layout (M : word -> option byte) : Prop :=
cellA M 0x1343a0 8 0x13ca38 /\ cellA M 0x13ca38 8 SB
/\ cellA M 0x1343a8 8 0x13d728 /\ cellA M 0x13d728 8 0
/\ cellA M 0x1343b0 8 0x13d730 /\ cellA M 0x13d730 8 0
/\ cellA M 0x1343b8 8 0x13d720 /\ cellA M 0x13d720 8 kHighMemEnd
/\ cellA M 0x134398 8 0x13a238 /\ cellA M (0x13a238 + 78) 1 1
/\ cellA M 0x1343c0 8 0x1363b0 /\ cellA M 0x1363b0 8 0x126be8
/\ cellA M 0x134390 8 0x1ce568 /\ cellA M (0x1ce568 + 120) 8 18446744073709551615
/\ cellA M 0x13c29c 1 1.
Section SE.
Local Abbreviation SEC_T_art_layout_Wn := (ltac2:(TCodec.tc2 tcn__JbtPoison "QF'0'Q7yR0%211'1y8%511%311p051'5&Gzr2%3221&H&Er3&Jr5%211%5241&K+2+R0%3221%;251&9r4r6%<11+QV`QH+Q`P0%645321r7%A11+Qii[8+X0%;4C321&=%116&8r9r8%3421:?%611p061p091p0?1p0G1p0Q41pRDQ91pQLQ:1p@Q<1pR0QE1")) (only parsing).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_layout_Wn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_layout_Wn) 1%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_layout_Wn) 2%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_art_layout_Wn) 3%nat 0%nat).
Lemma art_layout_Wn : ltac:(sec_stmt2 constr:(SEC_T_art_layout_Wn) 4%nat 0%nat).
Proof.
intros Ha Hn A1 A2 L.
unfold art_layout in *. unfold apart in *.
zsplit;
match goal with |- cell _ _ ?b ?m _ => apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; cbn; lia| tauto] end.
Qed.
End SE.
Definition art_poison_frame (M : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 : Z) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) ra) (sp - 16) s0) (sp - 24) s1) (sp - 32) s2) (sp - 40) s3) (sp - 48) s4) (sp - 56) s5.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_poison_hi_fn := (ltac2:(TCodec.tc2 tcn__JbtPoison "W1&6y5'Q7yR0%211%5241'1y8%611%311p061'5'4&Ar8(Q5+1(2%33A21%6251r5%93A21r9+2%93G17%<231&Q6%12H7%@3H31r:+:%@3N1>%C231%E3M16r;+;%E3Q31C%H231%J3Q21;r<+<%J3Q81H%M231%O3Q71@&G+R0%221H&H&K%12J4%32E1&:&Dr>&L%12E:%54431;&9%42C=+QV`QH+Q`P0%443@21r=%921B+Qii[8+X0%943E21&=rA%211&?%K21B&Er?%221E&@%421QL%Q1231&Ir@+8%3221z%R73R821%Q824@'3%Q:24B%Q82CF%3221rB%R>3R?18&FrD%221=+RPP0%Q@221p061';&BvNrJ+_YU@%RG3S31RE/01S3rIrH%8576321&CrG%239RK1rF%RE2S<1%533RH1+5%S33SA1S1&<%I2Q9Q4%Q=221%RL2SC1%<3751+6%S:3SH1S8+QTjo8%S12SH1%A3531+7%S?3SM1S=%S52SLQD%E3421%SB3T0QAS@%SE2N1%H3321+9%SF3T41SD%SI2Q21%L3421rE%Q>21QI%R22G1%SA2T81%Q135S=1rC%SD2T;1%Q433S;1%SF2T=QC%Q632S81+=%T43TB1T2%SJ2TA;%Q:3421+>%T83TF1T6%SN2TER6%Q>3421+?%T<3TJ1T:%T22TIQ8%QB3421+@%T@3TN1T>%S:2S?T@%T72TN1%QG3531+A%TE3U31TC%QJ331=+B%TH3U61TF%TK2R41%QN3421+C%TL3U:1TJ%TO2R81%R23421+D%U03U>1TN%U32R<1%R63421+E%U43UB1U2%U72R@1%R:3421+L%U83UF1U6%R=331QI%U:3UFQOU8/01UF&>&Q8%12UJRA%22UKQL%32ULQI%42UMH%52UNE%62UOB%72V0?%99RLRF7654321%S35S2=;1RL%S53TBRL1p0S71p0S@1p0SE1p0SG1p0SH1p0SO1p0T61p0T91p0T=1p0TC1p0TI1p0U01p0U51p0U91p0U?1p0UE1p0UK1p0V31pRDV>1pR0V?1pR2V@1pR:VA1pR4VI1pR8VD1p@VE1pR6VK1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_fn) 4%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_fn) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_fn) 6%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi_fn) 7%nat 0%nat).
Lemma art_poison_hi_fn : ltac:(sec_stmt2 constr:(SEC_T_art_poison_hi_fn) 8%nat 0%nat).
Proof using Type regs M rom raw sp p n v.
intros H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn Hv Hthr.
unfold kHighMemBeg, kHighMemEnd in *.
zstep (ltac:(oF' 0x7a4b0%Z)) (ltac:(oD' 0x7a4b0%Z)).
zsd (ltac:(oF' 0x7a4b4%Z)) (ltac:(oD' 0x7a4b4%Z)) (sp - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x7a4b8%Z)) (ltac:(oD' 0x7a4b8%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x7a4bc%Z)) (ltac:(oD' 0x7a4bc%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x7a4c0%Z)) (ltac:(oD' 0x7a4c0%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x7a4c4%Z)) (ltac:(oD' 0x7a4c4%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W).
zsd (ltac:(oF' 0x7a4c8%Z)) (ltac:(oD' 0x7a4c8%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x7a4cc%Z)) (ltac:(oD' 0x7a4cc%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W).
match goal with |- msteps _ (mkst _ _ ?X _) _ => set (Mf := X) end.
assert (L1 : art_layout Mf) by (unfold Mf; repeat (apply art_layout_Wn; [lia|lia|unfold apart in *; cbn; lia|unfold apart in *; cbn; lia|]); exact L).
assert (Cra : cellA Mf (sp - 8) 8 (U raw)) by (unfold Mf; do 6 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
assert (Cs0 : cellA Mf (sp - 16) 8 (U (getr regs 8))) by (unfold Mf; do 5 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
assert (Cs1 : cellA Mf (sp - 24) 8 (U (getr regs 9))) by (unfold Mf; do 4 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
assert (Cs2 : cellA Mf (sp - 32) 8 (U (getr regs 18))) by (unfold Mf; do 3 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
assert (Cs3 : cellA Mf (sp - 40) 8 (U (getr regs 19))) by (unfold Mf; do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
assert (Cs4 : cellA Mf (sp - 48) 8 (U (getr regs 20))) by (unfold Mf; do 1 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia).
assert (Cs5 : cellA Mf (sp - 56) 8 (U (getr regs 21))) by (unfold Mf; apply cell_Wn_hit; lia).
destruct L1 as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
assert (Hp8' : p / 8 * 8 = p) by lia. assert (Hn8' : n / 8 * 8 = n) by lia.
destruct (Z.eq_dec v 0) as [V0|V1].
- zbtk (ltac:(oF' 0x7a4d0%Z)) (ltac:(oD' 0x7a4d0%Z)).
stepn (ltac:(oF' 0x7a4e4%Z)) (ltac:(oD' 0x7a4e4%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
zbft (ltac:(oF' 0x7a4e8%Z)) (ltac:(oD' 0x7a4e8%Z)).
zstep (ltac:(oF' 0x7a4ec%Z)) (ltac:(oD' 0x7a4ec%Z)).
zld (ltac:(oF' 0x7a4f0%Z)) (ltac:(oD' 0x7a4f0%Z)) 0x1343a0 G48.
zld (ltac:(oF' 0x7a4f4%Z)) (ltac:(oD' 0x7a4f4%Z)) 0x13ca38 Csb. unfold SB in *.
zstep (ltac:(oF' 0x7a4f8%Z)) (ltac:(oD' 0x7a4f8%Z)). zstep (ltac:(oF' 0x7a4fc%Z)) (ltac:(oD' 0x7a4fc%Z)). zstep (ltac:(oF' 0x7a500%Z)) (ltac:(oD' 0x7a500%Z)).
zstep (ltac:(oF' 0x7a504%Z)) (ltac:(oD' 0x7a504%Z)).
zbft (ltac:(oF' 0x7a508%Z)) (ltac:(oD' 0x7a508%Z)).
zstep (ltac:(oF' 0x7a50c%Z)) (ltac:(oD' 0x7a50c%Z)). zld (ltac:(oF' 0x7a510%Z)) (ltac:(oD' 0x7a510%Z)) 0x1343a8 G50.
zstep (ltac:(oF' 0x7a514%Z)) (ltac:(oD' 0x7a514%Z)). zld (ltac:(oF' 0x7a518%Z)) (ltac:(oD' 0x7a518%Z)) 0x1343b0 G58.
zld (ltac:(oF' 0x7a51c%Z)) (ltac:(oD' 0x7a51c%Z)) 0x13d728 Cmb. zld (ltac:(oF' 0x7a520%Z)) (ltac:(oD' 0x7a520%Z)) 0x13d730 Cme.
zstep (ltac:(oF' 0x7a524%Z)) (ltac:(oD' 0x7a524%Z)).
zbtk (ltac:(oF' 0x7a528%Z)) (ltac:(oD' 0x7a528%Z)).
zstep (ltac:(oF' 0x7a530%Z)) (ltac:(oD' 0x7a530%Z)). zld (ltac:(oF' 0x7a534%Z)) (ltac:(oD' 0x7a534%Z)) 0x1343b8 G60. zld (ltac:(oF' 0x7a538%Z)) (ltac:(oD' 0x7a538%Z)) 0x13d720 Che.
zstep (ltac:(oF' 0x7a53c%Z)) (ltac:(oD' 0x7a53c%Z)).
zstep (ltac:(oF' 0x7a540%Z)) (ltac:(oD' 0x7a540%Z)).
zbft (ltac:(oF' 0x7a544%Z)) (ltac:(oD' 0x7a544%Z)).
zbtk (ltac:(oF' 0x7a548%Z)) (ltac:(oD' 0x7a548%Z)).
zld (ltac:(oF' 0x7a610%Z)) (ltac:(oD' 0x7a610%Z)) 0x13d720 Che.
zstep (ltac:(oF' 0x7a614%Z)) (ltac:(oD' 0x7a614%Z)).
zstep (ltac:(oF' 0x7a618%Z)) (ltac:(oD' 0x7a618%Z)).
zbft (ltac:(oF' 0x7a61c%Z)) (ltac:(oD' 0x7a61c%Z)).
zbtk (ltac:(oF' 0x7a620%Z)) (ltac:(oD' 0x7a620%Z)).
stepn (ltac:(oF' 0x7a6e0%Z)) (ltac:(oD' 0x7a6e0%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
zbft (ltac:(oF' 0x7a6e4%Z)) (ltac:(oD' 0x7a6e4%Z)).
zstep (ltac:(oF' 0x7a6e8%Z)) (ltac:(oD' 0x7a6e8%Z)). zstep (ltac:(oF' 0x7a6ec%Z)) (ltac:(oD' 0x7a6ec%Z)).
zbft (ltac:(oF' 0x7a6f0%Z)) (ltac:(oD' 0x7a6f0%Z)).
zstep (ltac:(oF' 0x7a6f4%Z)) (ltac:(oD' 0x7a6f4%Z)). zld (ltac:(oF' 0x7a6f8%Z)) (ltac:(oD' 0x7a6f8%Z)) 0x1343a8 G50.
zstep (ltac:(oF' 0x7a6fc%Z)) (ltac:(oD' 0x7a6fc%Z)). zld (ltac:(oF' 0x7a700%Z)) (ltac:(oD' 0x7a700%Z)) 0x1343b0 G58.
zld (ltac:(oF' 0x7a704%Z)) (ltac:(oD' 0x7a704%Z)) 0x13d728 Cmb. zld (ltac:(oF' 0x7a708%Z)) (ltac:(oD' 0x7a708%Z)) 0x13d730 Cme.
zstep (ltac:(oF' 0x7a70c%Z)) (ltac:(oD' 0x7a70c%Z)).
zbtk (ltac:(oF' 0x7a710%Z)) (ltac:(oD' 0x7a710%Z)).
zstep (ltac:(oF' 0x7a718%Z)) (ltac:(oD' 0x7a718%Z)). zld (ltac:(oF' 0x7a71c%Z)) (ltac:(oD' 0x7a71c%Z)) 0x1343b8 G60. zld (ltac:(oF' 0x7a720%Z)) (ltac:(oD' 0x7a720%Z)) 0x13d720 Che.
zstep (ltac:(oF' 0x7a724%Z)) (ltac:(oD' 0x7a724%Z)).
zstep (ltac:(oF' 0x7a728%Z)) (ltac:(oD' 0x7a728%Z)).
zbft (ltac:(oF' 0x7a72c%Z)) (ltac:(oD' 0x7a72c%Z)).
zbft (ltac:(oF' 0x7a730%Z)) (ltac:(oD' 0x7a730%Z)).
zstep (ltac:(oF' 0x7a734%Z)) (ltac:(oD' 0x7a734%Z)). zld (ltac:(oF' 0x7a738%Z)) (ltac:(oD' 0x7a738%Z)) 0x1343c0 G68. zld (ltac:(oF' 0x7a73c%Z)) (ltac:(oD' 0x7a73c%Z)) 0x1363b0 Crm.
zbft (ltac:(oF' 0x7a740%Z)) (ltac:(oD' 0x7a740%Z)).
stepn (ltac:(oF' 0x7a744%Z)) (ltac:(oD' 0x7a744%Z)). rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
stepn (ltac:(oF' 0x7a748%Z)) (ltac:(oD' 0x7a748%Z)). rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
zstep (ltac:(oF' 0x7a74c%Z)) (ltac:(oD' 0x7a74c%Z)). zstep (ltac:(oF' 0x7a750%Z)) (ltac:(oD' 0x7a750%Z)). zstep (ltac:(oF' 0x7a754%Z)) (ltac:(oD' 0x7a754%Z)).
zbft (ltac:(oF' 0x7a758%Z)) (ltac:(oD' 0x7a758%Z)).
zstep (ltac:(oF' 0x7a75c%Z)) (ltac:(oD' 0x7a75c%Z)). zld (ltac:(oF' 0x7a760%Z)) (ltac:(oD' 0x7a760%Z)) 0x134390 G38. zld (ltac:(oF' 0x7a764%Z)) (ltac:(oD' 0x7a764%Z)) (0x1ce568 + 120) Cth.
zbtk (ltac:(oF' 0x7a768%Z)) (ltac:(oD' 0x7a768%Z)).
zstep (ltac:(oF' 0x7a818%Z)) (ltac:(oD' 0x7a818%Z)). stepn (ltac:(oF' 0x7a81c%Z)) (ltac:(oD' 0x7a81c%Z)).
zstep (ltac:(oF' 0x7a828%Z)) (ltac:(oD' 0x7a828%Z)).
zld (ltac:(oF' 0x7a82c%Z)) (ltac:(oD' 0x7a82c%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a830%Z)) (ltac:(oD' 0x7a830%Z)) (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a834%Z)) (ltac:(oD' 0x7a834%Z)) (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a838%Z)) (ltac:(oD' 0x7a838%Z)) (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a83c%Z)) (ltac:(oD' 0x7a83c%Z)) (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a840%Z)) (ltac:(oD' 0x7a840%Z)) (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a844%Z)) (ltac:(oD' 0x7a844%Z)) (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x7a848%Z)) (ltac:(oD' 0x7a848%Z)).
stepjr (ltac:(oF' 0x7a84c%Z)) (ltac:(oD' 0x7a84c%Z)) (0x126be8 : bv 64)%bv ltac:(gres; bveq).
unfold Mf, art_poison_frame, SB. subst v. zret.
- zbft (ltac:(oF' 0x7a4d0%Z)) (ltac:(oD' 0x7a4d0%Z)).
zstep (ltac:(oF' 0x7a4d4%Z)) (ltac:(oD' 0x7a4d4%Z)).
zlb (ltac:(oF' 0x7a4d8%Z)) (ltac:(oD' 0x7a4d8%Z)) 0x13c29c Ccp.
stepfence (ltac:(oF' 0x7a4dc%Z)) (ltac:(oD' 0x7a4dc%Z)).
zbft (ltac:(oF' 0x7a4e0%Z)) (ltac:(oD' 0x7a4e0%Z)).
stepn (ltac:(oF' 0x7a4e4%Z)) (ltac:(oD' 0x7a4e4%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
zbft (ltac:(oF' 0x7a4e8%Z)) (ltac:(oD' 0x7a4e8%Z)).
zstep (ltac:(oF' 0x7a4ec%Z)) (ltac:(oD' 0x7a4ec%Z)).
zld (ltac:(oF' 0x7a4f0%Z)) (ltac:(oD' 0x7a4f0%Z)) 0x1343a0 G48.
zld (ltac:(oF' 0x7a4f4%Z)) (ltac:(oD' 0x7a4f4%Z)) 0x13ca38 Csb. unfold SB in *.
zstep (ltac:(oF' 0x7a4f8%Z)) (ltac:(oD' 0x7a4f8%Z)). zstep (ltac:(oF' 0x7a4fc%Z)) (ltac:(oD' 0x7a4fc%Z)). zstep (ltac:(oF' 0x7a500%Z)) (ltac:(oD' 0x7a500%Z)).
zstep (ltac:(oF' 0x7a504%Z)) (ltac:(oD' 0x7a504%Z)).
zbft (ltac:(oF' 0x7a508%Z)) (ltac:(oD' 0x7a508%Z)).
zstep (ltac:(oF' 0x7a50c%Z)) (ltac:(oD' 0x7a50c%Z)). zld (ltac:(oF' 0x7a510%Z)) (ltac:(oD' 0x7a510%Z)) 0x1343a8 G50.
zstep (ltac:(oF' 0x7a514%Z)) (ltac:(oD' 0x7a514%Z)). zld (ltac:(oF' 0x7a518%Z)) (ltac:(oD' 0x7a518%Z)) 0x1343b0 G58.
zld (ltac:(oF' 0x7a51c%Z)) (ltac:(oD' 0x7a51c%Z)) 0x13d728 Cmb. zld (ltac:(oF' 0x7a520%Z)) (ltac:(oD' 0x7a520%Z)) 0x13d730 Cme.
zstep (ltac:(oF' 0x7a524%Z)) (ltac:(oD' 0x7a524%Z)).
zbtk (ltac:(oF' 0x7a528%Z)) (ltac:(oD' 0x7a528%Z)).
zstep (ltac:(oF' 0x7a530%Z)) (ltac:(oD' 0x7a530%Z)). zld (ltac:(oF' 0x7a534%Z)) (ltac:(oD' 0x7a534%Z)) 0x1343b8 G60. zld (ltac:(oF' 0x7a538%Z)) (ltac:(oD' 0x7a538%Z)) 0x13d720 Che.
zstep (ltac:(oF' 0x7a53c%Z)) (ltac:(oD' 0x7a53c%Z)).
zstep (ltac:(oF' 0x7a540%Z)) (ltac:(oD' 0x7a540%Z)).
zbft (ltac:(oF' 0x7a544%Z)) (ltac:(oD' 0x7a544%Z)).
zbtk (ltac:(oF' 0x7a548%Z)) (ltac:(oD' 0x7a548%Z)).
zld (ltac:(oF' 0x7a610%Z)) (ltac:(oD' 0x7a610%Z)) 0x13d720 Che.
zstep (ltac:(oF' 0x7a614%Z)) (ltac:(oD' 0x7a614%Z)).
zstep (ltac:(oF' 0x7a618%Z)) (ltac:(oD' 0x7a618%Z)).
zbft (ltac:(oF' 0x7a61c%Z)) (ltac:(oD' 0x7a61c%Z)).
zbtk (ltac:(oF' 0x7a620%Z)) (ltac:(oD' 0x7a620%Z)).
stepn (ltac:(oF' 0x7a6e0%Z)) (ltac:(oD' 0x7a6e0%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
zbft (ltac:(oF' 0x7a6e4%Z)) (ltac:(oD' 0x7a6e4%Z)).
zstep (ltac:(oF' 0x7a6e8%Z)) (ltac:(oD' 0x7a6e8%Z)). zstep (ltac:(oF' 0x7a6ec%Z)) (ltac:(oD' 0x7a6ec%Z)).
zbft (ltac:(oF' 0x7a6f0%Z)) (ltac:(oD' 0x7a6f0%Z)).
zstep (ltac:(oF' 0x7a6f4%Z)) (ltac:(oD' 0x7a6f4%Z)). zld (ltac:(oF' 0x7a6f8%Z)) (ltac:(oD' 0x7a6f8%Z)) 0x1343a8 G50.
zstep (ltac:(oF' 0x7a6fc%Z)) (ltac:(oD' 0x7a6fc%Z)). zld (ltac:(oF' 0x7a700%Z)) (ltac:(oD' 0x7a700%Z)) 0x1343b0 G58.
zld (ltac:(oF' 0x7a704%Z)) (ltac:(oD' 0x7a704%Z)) 0x13d728 Cmb. zld (ltac:(oF' 0x7a708%Z)) (ltac:(oD' 0x7a708%Z)) 0x13d730 Cme.
zstep (ltac:(oF' 0x7a70c%Z)) (ltac:(oD' 0x7a70c%Z)).
zbtk (ltac:(oF' 0x7a710%Z)) (ltac:(oD' 0x7a710%Z)).
zstep (ltac:(oF' 0x7a718%Z)) (ltac:(oD' 0x7a718%Z)). zld (ltac:(oF' 0x7a71c%Z)) (ltac:(oD' 0x7a71c%Z)) 0x1343b8 G60. zld (ltac:(oF' 0x7a720%Z)) (ltac:(oD' 0x7a720%Z)) 0x13d720 Che.
zstep (ltac:(oF' 0x7a724%Z)) (ltac:(oD' 0x7a724%Z)).
zstep (ltac:(oF' 0x7a728%Z)) (ltac:(oD' 0x7a728%Z)).
zbft (ltac:(oF' 0x7a72c%Z)) (ltac:(oD' 0x7a72c%Z)).
zbft (ltac:(oF' 0x7a730%Z)) (ltac:(oD' 0x7a730%Z)).
zstep (ltac:(oF' 0x7a734%Z)) (ltac:(oD' 0x7a734%Z)). zld (ltac:(oF' 0x7a738%Z)) (ltac:(oD' 0x7a738%Z)) 0x1343c0 G68. zld (ltac:(oF' 0x7a73c%Z)) (ltac:(oD' 0x7a73c%Z)) 0x1363b0 Crm.
zbft (ltac:(oF' 0x7a740%Z)) (ltac:(oD' 0x7a740%Z)).
stepn (ltac:(oF' 0x7a744%Z)) (ltac:(oD' 0x7a744%Z)). rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
stepn (ltac:(oF' 0x7a748%Z)) (ltac:(oD' 0x7a748%Z)). rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
zstep (ltac:(oF' 0x7a74c%Z)) (ltac:(oD' 0x7a74c%Z)). zstep (ltac:(oF' 0x7a750%Z)) (ltac:(oD' 0x7a750%Z)). zstep (ltac:(oF' 0x7a754%Z)) (ltac:(oD' 0x7a754%Z)).
zbtk (ltac:(oF' 0x7a758%Z)) (ltac:(oD' 0x7a758%Z)).
zstep (ltac:(oF' 0x7a818%Z)) (ltac:(oD' 0x7a818%Z)). stepn (ltac:(oF' 0x7a81c%Z)) (ltac:(oD' 0x7a81c%Z)).
zstep (ltac:(oF' 0x7a828%Z)) (ltac:(oD' 0x7a828%Z)).
zld (ltac:(oF' 0x7a82c%Z)) (ltac:(oD' 0x7a82c%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a830%Z)) (ltac:(oD' 0x7a830%Z)) (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a834%Z)) (ltac:(oD' 0x7a834%Z)) (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a838%Z)) (ltac:(oD' 0x7a838%Z)) (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a83c%Z)) (ltac:(oD' 0x7a83c%Z)) (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a840%Z)) (ltac:(oD' 0x7a840%Z)) (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a844%Z)) (ltac:(oD' 0x7a844%Z)) (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x7a848%Z)) (ltac:(oD' 0x7a848%Z)).
stepjr (ltac:(oF' 0x7a84c%Z)) (ltac:(oD' 0x7a84c%Z)) (0x126be8 : bv 64)%bv ltac:(gres; bveq).
unfold Mf, art_poison_frame, SB. zret.
Qed.
End SE.
End FPX.
