(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtPoison JbtAllocG JbtUnwind JbtFree1 JbtFp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtFxNull () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFxNull."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "4bvmap"; "0M"; "5apart"; "5cell"; "5wr"; "6msteps"; "7ret_ok"]; ["8hid"; "9art_fx_null_mem"; ":getr"; ":mkst"; ";loaded_segments"; "0S"; "<In"; "=add"; "=le"; "=lt"; "=pow"; "=sub"; "0f22"; "0f23"; "0f24"; "0fx"]; ["0g16"; "0g24"; "0g32"; "0g40"; "0g48"; "0g56"; "0r"; "0raw0"; "0regs"; "0regs'"; "0rom"; ">BV"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0t"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_fx_null_mem (M : word -> option byte) (S t f22 : Z) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) (U (0x79344 : bv 64)%bv)) (S - 2144) S) (S - 2152) 0) (S - 2160) (U (0x792d4 : bv 64)%bv)) (S - 2168) 1)
(S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_fx_null_fn := (ltac2:(TCodec.tc2 tcn__JbtFxNull "Z2&9y5'Q=yR0%211%5241'2y8%611%311p061'8'5&Br?(Q;+2(3%33A21%6251&Q<&Kr;+RU0%3221%52F1%>3F71r@+H%>3L1<%A231&G+QoO%22;1%>2O1%G3O51&?r>%211&H+`PQoooPP0+XP0%;221%4216&I&J+Q?%22O1%42Q21+TP0%;21Q4%D2H2+R0%82Q51%:231&;rArB%Q5219%443:1B&@'7%O25=+RPP0%I221+Vb\P0%K219%6231%811'4z%Q021>%L2?C%4221&=&DrQ0rM%QI21M%54431NrQ1%74614Q0&<rQ2rO+RRH%R1221u8+_Ti@%75>6321rQ3+RS0%R72@1%;5B316ArQ4+RS8%R;2@1%?5F31:KrQ5+RS@%R?2A1&Q>+_TfD%RH3S41RF/01S4%42S61%H5O86C1rQ6+RSH%RH2C1+1%M5Q442H1rQ7+RT0%RM2D1+RR@%RO2F1%Q35Q:53N1rQ8+RT8%S32F1+RA%S52H1%Q95Q@53Q41rQ9+RT@%S92C1%Q=5QD31Q8Q1rQ:+RTH%S=2B1%QA5QH31Q<Q5rQ;%S@2?S>%QD5QK21Q?Q8rQ<+8%SD2=1%Q52T7:%QI5R042QD1rQ=+@%SI2>1%QM5R431QHQ=rQ>%SL2=SE%R05R721QKQ@rQ?+Q0%T02>1%R45R;31QOQDrQ@+Q8%T42=1%R85R?31R3QHrQA+Q@%T82=1%R<5RC31R7QLrQB+QH%T<2>1%R@5RG31R;R0'6'>&CvOrQE+`VX@%TJ3U61TH/01U6rQDrQC%8576321r1&A%145EIM%<5;3B15%>3S751%U43UBR5U2%U7261%U93UA1F%U928U4%U32UDL%U<3UD21%U:3UHQAU8%U=2<1%U72UHQD%U@3UH21+9%U?3UM1U=%UB2A1%U<2UMQL%UE3UM21+B%UD3V21UB%UG2F1%UA2V2R5%UJ3V221+C%UI3V71UG%UL2K1%UF2V7R>%UO3V721+D%UN3V<1UL%V12Q01%UK2V<RI%V43V<21+E%V33VA1V1%V62Q51%V02VAS4%V93VA21+F%V83VF1V6%V;2Q:1%V52VFR6%V>3VF21+G%V=3VK1V;%V@2Q?1%V:2VKR>%VC3VK21%VC2QBV3%V=2VNRE%VF3VN21%W11W2&F(0+3%VH3W61VF+4%VJ3W81VH+I%VL3W:1VJ+J%VN3W<1VL+K%W03W>1VN(1%11>%=3?31%>3@61%?3A91%@3B<1%A3C?1%C3DR91r3r2%W=221rQG%W?213%WA3WI31p071pR>L1%UK2N1%UL2Q21%UM2Q81%UN2Q>1%UO2QD1%V02QJ1%V12R01%V22R61%V32R<1%V42RA1%V52RE1%V62RI1qRDX71%S:2X81p0S<1p0SA1p0SF1p0SK1p0T01p0T41p0T91p0T?1p0TC1p0TH1p0TM1p0U41p0U;1p0UA1p0UK1p0V01p0V51p0V>1p0VA1p0VH1p0VI1p0VJ1p0VK1p0VL1p0VM1p0VN1p0VO1p0W01p0W61p0W@1p0WF1p0WK1p0WN1p0X41p0X:1p0X>1p0XH1pR<Y81pR:Y91pR8Y:1pR6Y;1pR4Y<1pR2Y=1pQNY>1pQLY?1pQJY@1pS0YA1pQ<YB1pR@YJ1pRFYE1pFYF1pRBYL1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 2%nat 0%nat).
Variable raw0 : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 3%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 4%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 5%nat 0%nat).
Variable f22 : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 6%nat 0%nat).
Variable f23 : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 7%nat 0%nat).
Variable f24 : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 8%nat 0%nat).
Variable g16 : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 9%nat 0%nat).
Variable g24 : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 10%nat 0%nat).
Variable g32 : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 11%nat 0%nat).
Variable g40 : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 12%nat 0%nat).
Variable g48 : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 13%nat 0%nat).
Variable g56 : ltac:(sec_ty2 constr:(SEC_T_art_fx_null_fn) 14%nat 0%nat).
Lemma art_fx_null_fn : ltac:(sec_stmt2 constr:(SEC_T_art_fx_null_fn) 15%nat 0%nat).
Proof using Type regs M rom raw0 S t f22 f23 f24 g16 g24 g32 g40 g48 g56.
intros H2 H24 Hret HS HS' Ht Ht' Atsp Timg Hf22 Hf23 Hf24 Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 W Wt
C36 C44 C52 C60 C68 C76 C84 C92 C00 C08 F8 F16 F24 F32 F40 F48 F56.
pose proof Timg as Timg'; unfold hid in Timg'. unfold apart in Atsp.
eexists. split.
{
zsb (ltac:(oF' 0x81910%Z)) (ltac:(oD' 0x81910%Z)) (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (D36 : cellA X (S - 2136) 8 0x79330) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 0) by zcell;
assert (D60 : cellA X (S - 2160) 8 (U (0x792d4 : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
zld (ltac:(oF' 0x81914%Z)) (ltac:(oD' 0x81914%Z)) (S - 2136) D36. zld (ltac:(oF' 0x81918%Z)) (ltac:(oD' 0x81918%Z)) (S - 2144) D44. zld (ltac:(oF' 0x8191c%Z)) (ltac:(oD' 0x8191c%Z)) (S - 2152) D52. zld (ltac:(oF' 0x81920%Z)) (ltac:(oD' 0x81920%Z)) (S - 2160) D60.
zld (ltac:(oF' 0x81924%Z)) (ltac:(oD' 0x81924%Z)) (S - 2168) D68. zld (ltac:(oF' 0x81928%Z)) (ltac:(oD' 0x81928%Z)) (S - 2176) D76. zld (ltac:(oF' 0x8192c%Z)) (ltac:(oD' 0x8192c%Z)) (S - 2184) D84. zld (ltac:(oF' 0x81930%Z)) (ltac:(oD' 0x81930%Z)) (S - 2192) D92.
zld (ltac:(oF' 0x81934%Z)) (ltac:(oD' 0x81934%Z)) (S - 2200) D00. zld (ltac:(oF' 0x81938%Z)) (ltac:(oD' 0x81938%Z)) (S - 2208) D08.
zstep (ltac:(oF' 0x8193c%Z)) (ltac:(oD' 0x8193c%Z)).
stepjr (ltac:(oF' 0x81940%Z)) (ltac:(oD' 0x81940%Z)) (0x79330 : bv 64)%bv ltac:(gres; bveq).
zstep (ltac:(oF' 0x79330%Z)) (ltac:(oD' 0x79330%Z)). zstep (ltac:(oF' 0x79334%Z)) (ltac:(oD' 0x79334%Z)). zstep (ltac:(oF' 0x79338%Z)) (ltac:(oD' 0x79338%Z)). zstep (ltac:(oF' 0x7933c%Z)) (ltac:(oD' 0x7933c%Z)).
stepn (ltac:(oF' 0x79340%Z)) (ltac:(oD' 0x79340%Z)).
zstep (ltac:(oF' 0x51b78%Z)) (ltac:(oD' 0x51b78%Z)). zstep (ltac:(oF' 0x51b7c%Z)) (ltac:(oD' 0x51b7c%Z)). zstep (ltac:(oF' 0x51b80%Z)) (ltac:(oD' 0x51b80%Z)). zstep (ltac:(oF' 0x51b84%Z)) (ltac:(oD' 0x51b84%Z)). zstep (ltac:(oF' 0x51b88%Z)) (ltac:(oD' 0x51b88%Z)). zstep (ltac:(oF' 0x51b8c%Z)) (ltac:(oD' 0x51b8c%Z)).
zstep (ltac:(oF' 0x51b90%Z)) (ltac:(oD' 0x51b90%Z)). zstep (ltac:(oF' 0x51b94%Z)) (ltac:(oD' 0x51b94%Z)). zstep (ltac:(oF' 0x51b98%Z)) (ltac:(oD' 0x51b98%Z)).
stepn (ltac:(oF' 0x51b9c%Z)) (ltac:(oD' 0x51b9c%Z)).
zstep (ltac:(oF' 0x51ba0%Z)) (ltac:(oD' 0x51ba0%Z)).
zsd (ltac:(oF' 0x51ba4%Z)) (ltac:(oD' 0x51ba4%Z)) (S - 2136) (U (0x79344 : bv 64)%bv) ltac:(rewok W). zsd (ltac:(oF' 0x51ba8%Z)) (ltac:(oD' 0x51ba8%Z)) (S - 2144) S ltac:(rewok W). zsd (ltac:(oF' 0x51bac%Z)) (ltac:(oD' 0x51bac%Z)) (S - 2152) 0 ltac:(rewok W).
zsd (ltac:(oF' 0x51bb0%Z)) (ltac:(oD' 0x51bb0%Z)) (S - 2160) (U (0x792d4 : bv 64)%bv) ltac:(rewok W). zsd (ltac:(oF' 0x51bb4%Z)) (ltac:(oD' 0x51bb4%Z)) (S - 2168) 1 ltac:(rewok W). zsd (ltac:(oF' 0x51bb8%Z)) (ltac:(oD' 0x51bb8%Z)) (S - 2176) (S - 2128) ltac:(rewok W).
zsd (ltac:(oF' 0x51bbc%Z)) (ltac:(oD' 0x51bbc%Z)) (S - 2184) (S - 81) ltac:(rewok W). zsd (ltac:(oF' 0x51bc0%Z)) (ltac:(oD' 0x51bc0%Z)) (S - 2192) f22 ltac:(rewok W).
zbtk (ltac:(oF' 0x51bc4%Z)) (ltac:(oD' 0x51bc4%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (E36 : cellA X (S - 2136) 8 (U (0x79344 : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell; assert (E52 : cellA X (S - 2152) 8 0) by zcell;
assert (E60 : cellA X (S - 2160) 8 (U (0x792d4 : bv 64)%bv)) by zcell; assert (E68 : cellA X (S - 2168) 8 1) by zcell;
assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (E84 : cellA X (S - 2184) 8 (S - 81)) by zcell; assert (E92 : cellA X (S - 2192) 8 f22) by zcell;
assert (G8 : cellA X (S - 8) 8 (U raw0)) by zcell; assert (G16 : cellA X (S - 16) 8 g16) by zcell; assert (G24 : cellA X (S - 24) 8 g24) by zcell;
assert (G32 : cellA X (S - 32) 8 g32) by zcell; assert (G40 : cellA X (S - 40) 8 g40) by zcell; assert (G48 : cellA X (S - 48) 8 g48) by zcell; assert (G56 : cellA X (S - 56) 8 g56) by zcell end.
zld (ltac:(oF' 0x51c00%Z)) (ltac:(oD' 0x51c00%Z)) (S - 2136) E36. zld (ltac:(oF' 0x51c04%Z)) (ltac:(oD' 0x51c04%Z)) (S - 2144) E44. zld (ltac:(oF' 0x51c08%Z)) (ltac:(oD' 0x51c08%Z)) (S - 2152) E52. zld (ltac:(oF' 0x51c0c%Z)) (ltac:(oD' 0x51c0c%Z)) (S - 2160) E60.
zld (ltac:(oF' 0x51c10%Z)) (ltac:(oD' 0x51c10%Z)) (S - 2168) E68. zld (ltac:(oF' 0x51c14%Z)) (ltac:(oD' 0x51c14%Z)) (S - 2176) E76. zld (ltac:(oF' 0x51c18%Z)) (ltac:(oD' 0x51c18%Z)) (S - 2184) E84. zld (ltac:(oF' 0x51c1c%Z)) (ltac:(oD' 0x51c1c%Z)) (S - 2192) E92.
zstep (ltac:(oF' 0x51c20%Z)) (ltac:(oD' 0x51c20%Z)).
stepjr (ltac:(oF' 0x51c24%Z)) (ltac:(oD' 0x51c24%Z)) (0x79344 : bv 64)%bv ltac:(gres; bveq).
zstep (ltac:(oF' 0x79344%Z)) (ltac:(oD' 0x79344%Z)).
zld (ltac:(oF' 0x79348%Z)) (ltac:(oD' 0x79348%Z)) (S - 8) G8. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x7934c%Z)) (ltac:(oD' 0x7934c%Z)) (S - 16) G16. zld (ltac:(oF' 0x79350%Z)) (ltac:(oD' 0x79350%Z)) (S - 24) G24. zld (ltac:(oF' 0x79354%Z)) (ltac:(oD' 0x79354%Z)) (S - 32) G32.
zld (ltac:(oF' 0x79358%Z)) (ltac:(oD' 0x79358%Z)) (S - 40) G40. zld (ltac:(oF' 0x7935c%Z)) (ltac:(oD' 0x7935c%Z)) (S - 48) G48. zld (ltac:(oF' 0x79360%Z)) (ltac:(oD' 0x79360%Z)) (S - 56) G56.
zstep (ltac:(oF' 0x79364%Z)) (ltac:(oD' 0x79364%Z)).
stepret (ltac:(oF' 0x79368%Z)) (ltac:(oD' 0x79368%Z)) raw0 ltac:(rwH; reflexivity).
unfold art_fx_null_mem. rnorm. apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity | zval | zmem_eq]. }
split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. repeat (split; [gres; reflexivity|]).
intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; gres; reflexivity.
Qed.
End SE.
End FPX.
