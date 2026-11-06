(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import muslA.Ja0SumsMemset_code muslA.Ja0SumsMemset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatPoison () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "1option"; "2I"; "2and"; "2eq"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5wr"; "6msteps"; "7SB"; "7art_layout"; "7art_poison_frame"; "7kHighMemBeg"]; ["7kHighMemEnd"; "8getr"; "8mkst"; "8regupd"; "9loaded_segments"; ":add"; ":div"; ":le"; ":lt"; ":modulo"; ":of_nat"; ":pow"; ":sub"; "0a"; "0fx"; "0n"]; ["0p"; "0raw"; "0regs"; "0rom"; "0sp"; ";BV"; ";Z_to_bv"; ";bv"; ";bv_unsigned"; "0v"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition SB : Z := 0x7fff8000.
Definition kHighMemEnd : Z := 0x7fffffffffff.
Definition kHighMemBeg : Z := 0x10007fff8000.
Definition art_layout (M : word -> option byte) : Prop :=
cellA M 0x132638 8 0x13acf8 /\ cellA M 0x13acf8 8 SB
/\ cellA M 0x132640 8 0x13b9e8 /\ cellA M 0x13b9e8 8 0
/\ cellA M 0x132648 8 0x13b9f0 /\ cellA M 0x13b9f0 8 0
/\ cellA M 0x132650 8 0x13b9e0 /\ cellA M 0x13b9e0 8 kHighMemEnd
/\ cellA M 0x132630 8 0x1384f8 /\ cellA M (0x1384f8 + 78) 1 1
/\ cellA M 0x132658 8 0x134648 /\ cellA M 0x134648 8 0x124db0
/\ cellA M 0x132628 8 0x1cc828 /\ cellA M (0x1cc828 + 120) 8 18446744073709551615
/\ cellA M 0x13a55c 1 1.
Section SE.
Local Abbreviation SEC_T_art_layout_Wn := (ltac2:(TCodec.tc2 tcn__JatPoison "QF'0'Q7yR0%211'1y8%511%311p051'5&Gzr2%3221&H&Er3&Jr5%211%5241&K+2+R0%3221%;251&9r4r6%<11+QVXR0+Q`P0%645321r7%A11+QibQ8+X0%;4C321&=%116&8r9r8%3421:?%611p061p091p0?1p0G1p0Q41pRDQ91pQLQ:1p@Q<1pR0QE1")) (only parsing).
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
Local Abbreviation SEC_T_art_poison_hi_fn := (ltac2:(TCodec.tc2 tcn__JatPoison "W1&6y5'Q7yR0%211%5241'1y8%611%311p061'5'4&Ar8(Q5+1(2%33A21%6251r5%93A21r9+2%93G17%<231&Q6%12H7%@3H31r:+:%@3N1>%C231%E3M16r;+;%E3Q31C%H231%J3Q21;r<+<%J3Q81H%M231%O3Q71@&G+R0%221H&H&K%12J4%32E1&:&Dr>&L%12E:%54431;&9%42C=+QVXR0+Q`P0%443@21r=%921B+QibQ8+X0%943E21&=rA%211&?%K21B&Er?%221E&@%421QL%Q1231&Ir@+8%3221z%R73R821%Q824@'3%Q:24B%Q82CF%3221rB%R>3R?18&FrD%221=+RPP0%Q@221p061';&BvNrJ+_X_0%RG3S31RE/01S3rIrH%8576321&CrG%239RK1rF%RE2S<1%533RH1+5%S33SA1S1&<%I2Q9Q4%Q=221%RL2SC1%<3751+6%S:3SH1S8+QTc]@%S12SH1%A3531+7%S?3SM1S=%S52SLQD%E3421%SB3T0QAS@%SE2N1%H3321+9%SF3T41SD%SI2Q21%L3421rE%Q>21QI%R22G1%SA2T81%Q135S=1rC%SD2T;1%Q433S;1%SF2T=QC%Q632S81+=%T43TB1T2%SJ2TA;%Q:3421+>%T83TF1T6%SN2TER6%Q>3421+?%T<3TJ1T:%T22TIQ8%QB3421+@%T@3TN1T>%S:2S?T@%T72TN1%QG3531+A%TE3U31TC%QJ331=+B%TH3U61TF%TK2R41%QN3421+C%TL3U:1TJ%TO2R81%R23421+D%U03U>1TN%U32R<1%R63421+E%U43UB1U2%U72R@1%R:3421+L%U83UF1U6%R=331QI%U:3UFQOU8/01UF&>&Q8%12UJRA%22UKQL%32ULQI%42UMH%52UNE%62UOB%72V0?%99RLRF7654321%S35S2=;1RL%S53TBRL1p0S71p0S@1p0SE1p0SG1p0SH1p0SO1p0T61p0T91p0T=1p0TC1p0TI1p0U01p0U51p0U91p0U?1p0UE1p0UK1p0V31pRDV>1pR0V?1pR2V@1pR:VA1pR4VI1pR8VD1p@VE1pR6VK1")) (only parsing).
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
zstep (ltac:(oF' 0x7a1e0%Z)) (ltac:(oD' 0x7a1e0%Z)).
zsd (ltac:(oF' 0x7a1e4%Z)) (ltac:(oD' 0x7a1e4%Z)) (sp - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x7a1e8%Z)) (ltac:(oD' 0x7a1e8%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x7a1ec%Z)) (ltac:(oD' 0x7a1ec%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x7a1f0%Z)) (ltac:(oD' 0x7a1f0%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x7a1f4%Z)) (ltac:(oD' 0x7a1f4%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W).
zsd (ltac:(oF' 0x7a1f8%Z)) (ltac:(oD' 0x7a1f8%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x7a1fc%Z)) (ltac:(oD' 0x7a1fc%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W).
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
- zbtk (ltac:(oF' 0x7a200%Z)) (ltac:(oD' 0x7a200%Z)).
stepn (ltac:(oF' 0x7a214%Z)) (ltac:(oD' 0x7a214%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
zbft (ltac:(oF' 0x7a218%Z)) (ltac:(oD' 0x7a218%Z)).
zstep (ltac:(oF' 0x7a21c%Z)) (ltac:(oD' 0x7a21c%Z)).
zld (ltac:(oF' 0x7a220%Z)) (ltac:(oD' 0x7a220%Z)) 0x132638 G48.
zld (ltac:(oF' 0x7a224%Z)) (ltac:(oD' 0x7a224%Z)) 0x13acf8 Csb. unfold SB in *.
zstep (ltac:(oF' 0x7a228%Z)) (ltac:(oD' 0x7a228%Z)). zstep (ltac:(oF' 0x7a22c%Z)) (ltac:(oD' 0x7a22c%Z)). zstep (ltac:(oF' 0x7a230%Z)) (ltac:(oD' 0x7a230%Z)).
zstep (ltac:(oF' 0x7a234%Z)) (ltac:(oD' 0x7a234%Z)).
zbft (ltac:(oF' 0x7a238%Z)) (ltac:(oD' 0x7a238%Z)).
zstep (ltac:(oF' 0x7a23c%Z)) (ltac:(oD' 0x7a23c%Z)). zld (ltac:(oF' 0x7a240%Z)) (ltac:(oD' 0x7a240%Z)) 0x132640 G50.
zstep (ltac:(oF' 0x7a244%Z)) (ltac:(oD' 0x7a244%Z)). zld (ltac:(oF' 0x7a248%Z)) (ltac:(oD' 0x7a248%Z)) 0x132648 G58.
zld (ltac:(oF' 0x7a24c%Z)) (ltac:(oD' 0x7a24c%Z)) 0x13b9e8 Cmb. zld (ltac:(oF' 0x7a250%Z)) (ltac:(oD' 0x7a250%Z)) 0x13b9f0 Cme.
zstep (ltac:(oF' 0x7a254%Z)) (ltac:(oD' 0x7a254%Z)).
zbtk (ltac:(oF' 0x7a258%Z)) (ltac:(oD' 0x7a258%Z)).
zstep (ltac:(oF' 0x7a260%Z)) (ltac:(oD' 0x7a260%Z)). zld (ltac:(oF' 0x7a264%Z)) (ltac:(oD' 0x7a264%Z)) 0x132650 G60. zld (ltac:(oF' 0x7a268%Z)) (ltac:(oD' 0x7a268%Z)) 0x13b9e0 Che.
zstep (ltac:(oF' 0x7a26c%Z)) (ltac:(oD' 0x7a26c%Z)).
zstep (ltac:(oF' 0x7a270%Z)) (ltac:(oD' 0x7a270%Z)).
zbft (ltac:(oF' 0x7a274%Z)) (ltac:(oD' 0x7a274%Z)).
zbtk (ltac:(oF' 0x7a278%Z)) (ltac:(oD' 0x7a278%Z)).
zld (ltac:(oF' 0x7a340%Z)) (ltac:(oD' 0x7a340%Z)) 0x13b9e0 Che.
zstep (ltac:(oF' 0x7a344%Z)) (ltac:(oD' 0x7a344%Z)).
zstep (ltac:(oF' 0x7a348%Z)) (ltac:(oD' 0x7a348%Z)).
zbft (ltac:(oF' 0x7a34c%Z)) (ltac:(oD' 0x7a34c%Z)).
zbtk (ltac:(oF' 0x7a350%Z)) (ltac:(oD' 0x7a350%Z)).
stepn (ltac:(oF' 0x7a410%Z)) (ltac:(oD' 0x7a410%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
zbft (ltac:(oF' 0x7a414%Z)) (ltac:(oD' 0x7a414%Z)).
zstep (ltac:(oF' 0x7a418%Z)) (ltac:(oD' 0x7a418%Z)). zstep (ltac:(oF' 0x7a41c%Z)) (ltac:(oD' 0x7a41c%Z)).
zbft (ltac:(oF' 0x7a420%Z)) (ltac:(oD' 0x7a420%Z)).
zstep (ltac:(oF' 0x7a424%Z)) (ltac:(oD' 0x7a424%Z)). zld (ltac:(oF' 0x7a428%Z)) (ltac:(oD' 0x7a428%Z)) 0x132640 G50.
zstep (ltac:(oF' 0x7a42c%Z)) (ltac:(oD' 0x7a42c%Z)). zld (ltac:(oF' 0x7a430%Z)) (ltac:(oD' 0x7a430%Z)) 0x132648 G58.
zld (ltac:(oF' 0x7a434%Z)) (ltac:(oD' 0x7a434%Z)) 0x13b9e8 Cmb. zld (ltac:(oF' 0x7a438%Z)) (ltac:(oD' 0x7a438%Z)) 0x13b9f0 Cme.
zstep (ltac:(oF' 0x7a43c%Z)) (ltac:(oD' 0x7a43c%Z)).
zbtk (ltac:(oF' 0x7a440%Z)) (ltac:(oD' 0x7a440%Z)).
zstep (ltac:(oF' 0x7a448%Z)) (ltac:(oD' 0x7a448%Z)). zld (ltac:(oF' 0x7a44c%Z)) (ltac:(oD' 0x7a44c%Z)) 0x132650 G60. zld (ltac:(oF' 0x7a450%Z)) (ltac:(oD' 0x7a450%Z)) 0x13b9e0 Che.
zstep (ltac:(oF' 0x7a454%Z)) (ltac:(oD' 0x7a454%Z)).
zstep (ltac:(oF' 0x7a458%Z)) (ltac:(oD' 0x7a458%Z)).
zbft (ltac:(oF' 0x7a45c%Z)) (ltac:(oD' 0x7a45c%Z)).
zbft (ltac:(oF' 0x7a460%Z)) (ltac:(oD' 0x7a460%Z)).
zstep (ltac:(oF' 0x7a464%Z)) (ltac:(oD' 0x7a464%Z)). zld (ltac:(oF' 0x7a468%Z)) (ltac:(oD' 0x7a468%Z)) 0x132658 G68. zld (ltac:(oF' 0x7a46c%Z)) (ltac:(oD' 0x7a46c%Z)) 0x134648 Crm.
zbft (ltac:(oF' 0x7a470%Z)) (ltac:(oD' 0x7a470%Z)).
stepn (ltac:(oF' 0x7a474%Z)) (ltac:(oD' 0x7a474%Z)). rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
stepn (ltac:(oF' 0x7a478%Z)) (ltac:(oD' 0x7a478%Z)). rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
zstep (ltac:(oF' 0x7a47c%Z)) (ltac:(oD' 0x7a47c%Z)). zstep (ltac:(oF' 0x7a480%Z)) (ltac:(oD' 0x7a480%Z)). zstep (ltac:(oF' 0x7a484%Z)) (ltac:(oD' 0x7a484%Z)).
zbft (ltac:(oF' 0x7a488%Z)) (ltac:(oD' 0x7a488%Z)).
zstep (ltac:(oF' 0x7a48c%Z)) (ltac:(oD' 0x7a48c%Z)). zld (ltac:(oF' 0x7a490%Z)) (ltac:(oD' 0x7a490%Z)) 0x132628 G38. zld (ltac:(oF' 0x7a494%Z)) (ltac:(oD' 0x7a494%Z)) (0x1cc828 + 120) Cth.
zbtk (ltac:(oF' 0x7a498%Z)) (ltac:(oD' 0x7a498%Z)).
zstep (ltac:(oF' 0x7a548%Z)) (ltac:(oD' 0x7a548%Z)). stepn (ltac:(oF' 0x7a54c%Z)) (ltac:(oD' 0x7a54c%Z)).
zstep (ltac:(oF' 0x7a558%Z)) (ltac:(oD' 0x7a558%Z)).
zld (ltac:(oF' 0x7a55c%Z)) (ltac:(oD' 0x7a55c%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a560%Z)) (ltac:(oD' 0x7a560%Z)) (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a564%Z)) (ltac:(oD' 0x7a564%Z)) (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a568%Z)) (ltac:(oD' 0x7a568%Z)) (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a56c%Z)) (ltac:(oD' 0x7a56c%Z)) (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a570%Z)) (ltac:(oD' 0x7a570%Z)) (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a574%Z)) (ltac:(oD' 0x7a574%Z)) (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x7a578%Z)) (ltac:(oD' 0x7a578%Z)).
stepjr (ltac:(oF' 0x7a57c%Z)) (ltac:(oD' 0x7a57c%Z)) (0x124db0 : bv 64)%bv ltac:(gres; bveq).
unfold Mf, art_poison_frame, SB. subst v. zret.
- zbft (ltac:(oF' 0x7a200%Z)) (ltac:(oD' 0x7a200%Z)).
zstep (ltac:(oF' 0x7a204%Z)) (ltac:(oD' 0x7a204%Z)).
zlb (ltac:(oF' 0x7a208%Z)) (ltac:(oD' 0x7a208%Z)) 0x13a55c Ccp.
stepfence (ltac:(oF' 0x7a20c%Z)) (ltac:(oD' 0x7a20c%Z)).
zbft (ltac:(oF' 0x7a210%Z)) (ltac:(oD' 0x7a210%Z)).
stepn (ltac:(oF' 0x7a214%Z)) (ltac:(oD' 0x7a214%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land p 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
zbft (ltac:(oF' 0x7a218%Z)) (ltac:(oD' 0x7a218%Z)).
zstep (ltac:(oF' 0x7a21c%Z)) (ltac:(oD' 0x7a21c%Z)).
zld (ltac:(oF' 0x7a220%Z)) (ltac:(oD' 0x7a220%Z)) 0x132638 G48.
zld (ltac:(oF' 0x7a224%Z)) (ltac:(oD' 0x7a224%Z)) 0x13acf8 Csb. unfold SB in *.
zstep (ltac:(oF' 0x7a228%Z)) (ltac:(oD' 0x7a228%Z)). zstep (ltac:(oF' 0x7a22c%Z)) (ltac:(oD' 0x7a22c%Z)). zstep (ltac:(oF' 0x7a230%Z)) (ltac:(oD' 0x7a230%Z)).
zstep (ltac:(oF' 0x7a234%Z)) (ltac:(oD' 0x7a234%Z)).
zbft (ltac:(oF' 0x7a238%Z)) (ltac:(oD' 0x7a238%Z)).
zstep (ltac:(oF' 0x7a23c%Z)) (ltac:(oD' 0x7a23c%Z)). zld (ltac:(oF' 0x7a240%Z)) (ltac:(oD' 0x7a240%Z)) 0x132640 G50.
zstep (ltac:(oF' 0x7a244%Z)) (ltac:(oD' 0x7a244%Z)). zld (ltac:(oF' 0x7a248%Z)) (ltac:(oD' 0x7a248%Z)) 0x132648 G58.
zld (ltac:(oF' 0x7a24c%Z)) (ltac:(oD' 0x7a24c%Z)) 0x13b9e8 Cmb. zld (ltac:(oF' 0x7a250%Z)) (ltac:(oD' 0x7a250%Z)) 0x13b9f0 Cme.
zstep (ltac:(oF' 0x7a254%Z)) (ltac:(oD' 0x7a254%Z)).
zbtk (ltac:(oF' 0x7a258%Z)) (ltac:(oD' 0x7a258%Z)).
zstep (ltac:(oF' 0x7a260%Z)) (ltac:(oD' 0x7a260%Z)). zld (ltac:(oF' 0x7a264%Z)) (ltac:(oD' 0x7a264%Z)) 0x132650 G60. zld (ltac:(oF' 0x7a268%Z)) (ltac:(oD' 0x7a268%Z)) 0x13b9e0 Che.
zstep (ltac:(oF' 0x7a26c%Z)) (ltac:(oD' 0x7a26c%Z)).
zstep (ltac:(oF' 0x7a270%Z)) (ltac:(oD' 0x7a270%Z)).
zbft (ltac:(oF' 0x7a274%Z)) (ltac:(oD' 0x7a274%Z)).
zbtk (ltac:(oF' 0x7a278%Z)) (ltac:(oD' 0x7a278%Z)).
zld (ltac:(oF' 0x7a340%Z)) (ltac:(oD' 0x7a340%Z)) 0x13b9e0 Che.
zstep (ltac:(oF' 0x7a344%Z)) (ltac:(oD' 0x7a344%Z)).
zstep (ltac:(oF' 0x7a348%Z)) (ltac:(oD' 0x7a348%Z)).
zbft (ltac:(oF' 0x7a34c%Z)) (ltac:(oD' 0x7a34c%Z)).
zbtk (ltac:(oF' 0x7a350%Z)) (ltac:(oD' 0x7a350%Z)).
stepn (ltac:(oF' 0x7a410%Z)) (ltac:(oD' 0x7a410%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
zbft (ltac:(oF' 0x7a414%Z)) (ltac:(oD' 0x7a414%Z)).
zstep (ltac:(oF' 0x7a418%Z)) (ltac:(oD' 0x7a418%Z)). zstep (ltac:(oF' 0x7a41c%Z)) (ltac:(oD' 0x7a41c%Z)).
zbft (ltac:(oF' 0x7a420%Z)) (ltac:(oD' 0x7a420%Z)).
zstep (ltac:(oF' 0x7a424%Z)) (ltac:(oD' 0x7a424%Z)). zld (ltac:(oF' 0x7a428%Z)) (ltac:(oD' 0x7a428%Z)) 0x132640 G50.
zstep (ltac:(oF' 0x7a42c%Z)) (ltac:(oD' 0x7a42c%Z)). zld (ltac:(oF' 0x7a430%Z)) (ltac:(oD' 0x7a430%Z)) 0x132648 G58.
zld (ltac:(oF' 0x7a434%Z)) (ltac:(oD' 0x7a434%Z)) 0x13b9e8 Cmb. zld (ltac:(oF' 0x7a438%Z)) (ltac:(oD' 0x7a438%Z)) 0x13b9f0 Cme.
zstep (ltac:(oF' 0x7a43c%Z)) (ltac:(oD' 0x7a43c%Z)).
zbtk (ltac:(oF' 0x7a440%Z)) (ltac:(oD' 0x7a440%Z)).
zstep (ltac:(oF' 0x7a448%Z)) (ltac:(oD' 0x7a448%Z)). zld (ltac:(oF' 0x7a44c%Z)) (ltac:(oD' 0x7a44c%Z)) 0x132650 G60. zld (ltac:(oF' 0x7a450%Z)) (ltac:(oD' 0x7a450%Z)) 0x13b9e0 Che.
zstep (ltac:(oF' 0x7a454%Z)) (ltac:(oD' 0x7a454%Z)).
zstep (ltac:(oF' 0x7a458%Z)) (ltac:(oD' 0x7a458%Z)).
zbft (ltac:(oF' 0x7a45c%Z)) (ltac:(oD' 0x7a45c%Z)).
zbft (ltac:(oF' 0x7a460%Z)) (ltac:(oD' 0x7a460%Z)).
zstep (ltac:(oF' 0x7a464%Z)) (ltac:(oD' 0x7a464%Z)). zld (ltac:(oF' 0x7a468%Z)) (ltac:(oD' 0x7a468%Z)) 0x132658 G68. zld (ltac:(oF' 0x7a46c%Z)) (ltac:(oD' 0x7a46c%Z)) 0x134648 Crm.
zbft (ltac:(oF' 0x7a470%Z)) (ltac:(oD' 0x7a470%Z)).
stepn (ltac:(oF' 0x7a474%Z)) (ltac:(oD' 0x7a474%Z)). rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
stepn (ltac:(oF' 0x7a478%Z)) (ltac:(oD' 0x7a478%Z)). rwH. rewrite art_zb_srli by lia. change (2^3) with 8.
zstep (ltac:(oF' 0x7a47c%Z)) (ltac:(oD' 0x7a47c%Z)). zstep (ltac:(oF' 0x7a480%Z)) (ltac:(oD' 0x7a480%Z)). zstep (ltac:(oF' 0x7a484%Z)) (ltac:(oD' 0x7a484%Z)).
zbtk (ltac:(oF' 0x7a488%Z)) (ltac:(oD' 0x7a488%Z)).
zstep (ltac:(oF' 0x7a548%Z)) (ltac:(oD' 0x7a548%Z)). stepn (ltac:(oF' 0x7a54c%Z)) (ltac:(oD' 0x7a54c%Z)).
zstep (ltac:(oF' 0x7a558%Z)) (ltac:(oD' 0x7a558%Z)).
zld (ltac:(oF' 0x7a55c%Z)) (ltac:(oD' 0x7a55c%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a560%Z)) (ltac:(oD' 0x7a560%Z)) (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a564%Z)) (ltac:(oD' 0x7a564%Z)) (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a568%Z)) (ltac:(oD' 0x7a568%Z)) (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a56c%Z)) (ltac:(oD' 0x7a56c%Z)) (sp - 40) Cs3. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a570%Z)) (ltac:(oD' 0x7a570%Z)) (sp - 48) Cs4. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7a574%Z)) (ltac:(oD' 0x7a574%Z)) (sp - 56) Cs5. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x7a578%Z)) (ltac:(oD' 0x7a578%Z)).
stepjr (ltac:(oF' 0x7a57c%Z)) (ltac:(oD' 0x7a57c%Z)) (0x124db0 : bv 64)%bv ltac:(gres; bveq).
unfold Mf, art_poison_frame, SB. zret.
Qed.
End SE.
End FPX.
