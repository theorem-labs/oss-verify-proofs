(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtPoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtAllocE () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"; "5wr"; "6msteps"; "7ret_ok"; "8art_layout"; "8kHighMemBeg"; "9getr"]; ["9mkst"; "9regupd"; ":loaded_segments"; ";add"; ";land"; ";le"; ";lt"; ";modulo"; ";pow"; ";sub"; "0a"; "0ab"; "0b1"; "0fx"; "0loff"; "0m"]; ["0n"; "0raw"; "0raw0"; "0regs"; "0rom"; "0rz"; "0s0v"; "0s10v"; "0s11v"; "0s1v"; "0s2v"; "0s3v"; "0s4v"; "0s5v"; "0s6v"; "0s7v"]; ["0s8v"; "0s9v"; "0sp"; "<BV"; "<Z_to_bv"; "<bv"; "<bv_unsigned"; "0tp"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma land_le_l' : ltac2:(TCodec.tc2 tcn__JbtAllocE "A'4&Ezr2%3221'2&Dr4r3%3221%9281%:224%7221p091p0:1pR0?1pQF@1").
Proof. intros a m.
intros Ha Hm. split. apply Z.land_nonneg. left; exact Ha.
rewrite Z.land_comm.
pose proof (Z.lor_ldiff_and a m) as E1. pose proof (Z.add_lor_land (Z.ldiff a m) (Z.land m a)) as E2.
rewrite (Z.land_comm m a) in E2.
assert (Z0: Z.land (Z.ldiff a m) (Z.land a m) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.ldiff_spec, Z.bits_0. destruct (Z.testbit a i), (Z.testbit m i); reflexivity. }
assert (D0: 0 <= Z.ldiff a m). { apply Z.ldiff_nonneg. left; exact Ha. }
rewrite (Z.land_comm m a). lia.
Qed.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_run_malloc_hooks_fn := (ltac2:(TCodec.tc2 tcn__JbtAllocE "SL&5y5'QEyR0%211%5241'0y8%611%311p061'4'3&?r5(QC+1(1%33A21%6251r2%93A21&<r3%211r7+2%<3J1:%?231&QD%12K7%C3K31&E+Q0r4%3221&F&H+R0%22=1%42J1&C+Vb\P0%221:r6%=221&:&Br:&I%12IA%54431B&9r;+QiiX0u8z%55:4321';&@vMr=+`na@%Q@3QL1Q>/01QLr<%756521=&A%137QBDr9%Q92R31%433Q<1+8%QJ3R81QH%QM2=1%83421+9%QN3R<1QL%R12A1%<3421+:%R23R@1R0+Qijb@%QF2R@1%A3531+<%R73RE1R5%QJ2RDO%E3421+B%R;3RI1R9%R>2N1%I3421&7%Q=2IF&QF%12RMQ@%44Q:Q031+@%QB2N1%52S1J%84Q>421+H%QF2Q21%92S5J%<4QB421%QI2Q5R9%<2S8@%?4QE321%QB5QAAQM1QH%QD3QOQ<1p0QF1p0QM1p0R41p0R:1p0R@1p0RE1p0RM1p0S11pS6S<1pR4SD1pR:S?1p>S@1pR8SF1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_run_malloc_hooks_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_run_malloc_hooks_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_run_malloc_hooks_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_run_malloc_hooks_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_run_malloc_hooks_fn) 4%nat 0%nat).
Lemma art_run_malloc_hooks_fn : ltac:(sec_stmt2 constr:(SEC_T_art_run_malloc_hooks_fn) 5%nat 0%nat).
Proof using Type regs M rom raw sp.
intros H1 Hret H2 Hsp Hsp' IMG W Ch.
zstep (ltac:(oF' 0x87a30%Z)) (ltac:(oD' 0x87a30%Z)).
zsd (ltac:(oF' 0x87a34%Z)) (ltac:(oD' 0x87a34%Z)) (sp - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x87a38%Z)) (ltac:(oD' 0x87a38%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x87a3c%Z)) (ltac:(oD' 0x87a3c%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x87a40%Z)) (ltac:(oD' 0x87a40%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zstep (ltac:(oF' 0x87a44%Z)) (ltac:(oD' 0x87a44%Z)). zstep (ltac:(oF' 0x87a48%Z)) (ltac:(oD' 0x87a48%Z)).
stepn (ltac:(oF' 0x87a4c%Z)) (ltac:(oD' 0x87a4c%Z)).
stepjr (ltac:(oF' 0x87ae8%Z)) (ltac:(oD' 0x87ae8%Z)) (0x87a50 : bv 64)%bv ltac:(gres; bveq).
zstep (ltac:(oF' 0x87a50%Z)) (ltac:(oD' 0x87a50%Z)). zstep (ltac:(oF' 0x87a54%Z)) (ltac:(oD' 0x87a54%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Ch' : cellA X 0x1ce500 8 0) by (recell Ch);
assert (Cra : cellA X (sp - 8) 8 (U raw)) by (do 3 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
assert (Cs0 : cellA X (sp - 16) 8 (U (getr regs 8))) by (do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
assert (Cs1 : cellA X (sp - 24) 8 (U (getr regs 9))) by (do 1 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]); apply cell_Wn_hit; lia);
assert (Cs2 : cellA X (sp - 32) 8 (U (getr regs 18))) by (apply cell_Wn_hit; lia) end.
zld (ltac:(oF' 0x87a58%Z)) (ltac:(oD' 0x87a58%Z)) 0x1ce500 Ch'.
zbtk (ltac:(oF' 0x87a5c%Z)) (ltac:(oD' 0x87a5c%Z)).
zld (ltac:(oF' 0x87ad0%Z)) (ltac:(oD' 0x87ad0%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x87ad4%Z)) (ltac:(oD' 0x87ad4%Z)) (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x87ad8%Z)) (ltac:(oD' 0x87ad8%Z)) (sp - 24) Cs1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x87adc%Z)) (ltac:(oD' 0x87adc%Z)) (sp - 32) Cs2. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x87ae0%Z)) (ltac:(oD' 0x87ae0%Z)).
stepret (ltac:(oF' 0x87ae4%Z)) (ltac:(oD' 0x87ae4%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_alloc_e16_fn := (ltac2:(TCodec.tc2 tcn__JbtAllocE "[G&5y5'QEyR0%211%5241'0y8%611%311p061'4'3&?rG(QC+2(1%33A21%6251&QDrC%22C1%;3C41rH+4%;3I19%>231r?%92J1%B3J31rI+8%B3Q01@%E231+1%@2Q11%I3Q131rJ+9%I3Q71G%L231rD%G2Q81%Q03Q831rK+B%Q03Q>1N%Q3231rF%N2Q?1%Q73Q?31rL+D%Q73QE1Q5%Q:231&CrE%22Q<1%Q72QH1%Q@3QH51rM+E%Q@3QN1Q>%QC231&I%:2Q:A+@%3221%QA2R21%QJ3R261&E+Q0%221Q3&F+T0%D2O1&H+R0%22QO1%6241+Vb\P0%J21:%<21O&>%>21Q1+RPP0%O2J1+Q?%<2R91%@231&GrN%221Jz%RC3RD21'2%J2QN5+Q8%F2RC1%J281%5241%O28Q9+X0%N2Q;1%9231+TP0%QC2?1%Q221M%Q62?ArQ0rO%QH221%QI21RH%Q821Q3&<rQ7%211&9&BrQ:+QVdP0u8rQ1%6554321rQ;rQ3rQ2%R8221u4%<5;521Q4&8rQ4%R=217rQ8rQ6%R@221%R821R6%745SA1R7rQ=rQ9%RE21I%R=21R;%RG21S<u1%K5J621:&:rQ>%RL2L>%RD21RB%44O31RCrQ?rQ<%RH21RA%84Q331RB&=rQ@%211rQA+QiiX0%Q:5Q921Q6R2%S92>9%S121RO%S22<RK+U0%Q243S221%S52:RN%Q44@S413rQD+SH%SB2<1&QFrQB%22U:1%QH5QG64QD1rQE+S@%SI251%QL5QK31QHQErQFrQC+S8%SN221%R15R041QMQJrQG+S0%T22B1%R55R431R1QNrQH+RH%T62?1%R95R831R5R2rQI+R@%T:2?1%R=5R<31R9R6rQJ+R8%T>2>1%RA5R@31R=R:rQK%TA2=SK%RD5RC21R@R=rQL+QH%TE2=1%RH5RG31RDRArQM+Q@%TI2=1%RL5RK31RHRErQN%TL2<SB%RO5RN21RKRHrQO%TO2<T?%S25S121RNRKrR0+H%U32<1%S65S531S2RO%VA3VBETJ';&@vMrR3+ZY\D%VD3W01VB/01W0rR2rR1%8576321&A%VJ3W8V6VH%2391A%UC2EU0%VH2W91%533VK1%VJ2W;QB%732V>1%VL2W=QH%932V91+:%W43WB1W2%UL2Q1Q9%W12WB1%>3531+;%W93WG1W7%W52WFQ:%B3421+<%W=3WK1W;%W92WJTO%F3421%W;2WLR<%H32VA1+C%WC3X11WA%W?2X0RD%L3421%WA2X2RM%N32V@1%WC2X4RC%Q032V91+F%WK3X91WI%WG2X8RO%Q43421+G%WO3X=1WM%WK2X<SA%Q83421%X23X@QGX0%WN2X?SF%Q;3321+I%X63XD1X4%X22XCSO%Q?3421+J%X:3XH1X8%X62XGT7%QC3421+K%X>3XL1X<%X:2XKTC%QG3421&7+?%W12Q>1&D+WC%22RM1%64TFR141%W62QCW4%84TH21XH%W82RCX9+ZY_8%;4UA321%W;2RFW9%=4UC21X:%W=2RHRD%?4UE21S0%W?2RJW8%A4UG21RN%RC5RBCRI1R<%RE3ULR<1p0RG1p0RI1p0RN1p0S21p0S61p0S;1p0S@1p0SD1p0SI1p0SN1p0T31p0T81p0T>1p0TC1p0TK1p0TN1p0U41p0U81p0U<1p0UA1p0UG1p0UO1p0V81p0V?1p0VG1p0VK1p0W11p0W31p0W:1p0W81p0W=1p0WD1p0WJ1p0X01p0X31p0X71p0X?1p0XC1p0XN1p0Y81p0Y@1p0YH1p0Z01p0Z81pRBZE1pR@ZF1pS4ZG1pS2ZH1pS0ZI1pRNZJ1pRLZK1pRJZL1pRHZM1pRFZN1pRDZO1pR>[01pQN[11pS@[21pQJ[31pR<[41pR2[51pQH[61pS6[71pR6[?1pR:[:1p>[;1pR8[A1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 2%nat 0%nat).
Variable raw0 : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 4%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 6%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 7%nat 0%nat).
Variable b1 : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 8%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 9%nat 0%nat).
Variable loff : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 10%nat 0%nat).
Variable s0v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 11%nat 0%nat).
Variable s1v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 12%nat 0%nat).
Variable s2v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 13%nat 0%nat).
Variable s3v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 14%nat 0%nat).
Variable s4v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 15%nat 0%nat).
Variable s5v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 16%nat 0%nat).
Variable s6v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 17%nat 0%nat).
Variable s7v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 18%nat 0%nat).
Variable s8v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 19%nat 0%nat).
Variable s9v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 20%nat 0%nat).
Variable s10v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 21%nat 0%nat).
Variable s11v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e16_fn) 22%nat 0%nat).
Lemma art_alloc_e16_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_e16_fn) 23%nat 0%nat).
Proof using Type regs M rom raw0 sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v.
intros H2 H4 H8 H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24.
intros Hrz. unfold kHighMemBeg in *.
pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
pose proof (land_le_l' b1 243 ltac:(lia) ltac:(lia)) as Lb.
stepn (ltac:(oF' 0x52594%Z)) (ltac:(oD' 0x52594%Z)).
zcall (art_lsan_off_fn _ _ _ _ tp loff).
zlbu (ltac:(oF' 0x52598%Z)) (ltac:(oD' 0x52598%Z)) (ab + rz - 16 + 1) Cb1.
zstep (ltac:(oF' 0x5259c%Z)) (ltac:(oD' 0x5259c%Z)). zstep (ltac:(oF' 0x525a0%Z)) (ltac:(oD' 0x525a0%Z)).
stepn (ltac:(oF' 0x525a4%Z)) (ltac:(oD' 0x525a4%Z)). rwH. rewrite art_zb_andi by lia.
stepn (ltac:(oF' 0x525a8%Z)) (ltac:(oD' 0x525a8%Z)). rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_r.
zstep (ltac:(oF' 0x525ac%Z)) (ltac:(oD' 0x525ac%Z)).
zsb (ltac:(oF' 0x525b0%Z)) (ltac:(oD' 0x525b0%Z)) (ab + rz - 16 + 1) (Z.land b1 243) ltac:(rewok Wh).
stepfence (ltac:(oF' 0x525b4%Z)) (ltac:(oD' 0x525b4%Z)).
zsb (ltac:(oF' 0x525b8%Z)) (ltac:(oD' 0x525b8%Z)) (ab + rz - 16) 2 ltac:(rewok Wh).
zbtk (ltac:(oF' 0x525bc%Z)) (ltac:(oD' 0x525bc%Z)).
zstep (ltac:(oF' 0x525dc%Z)) (ltac:(oD' 0x525dc%Z)). zstep (ltac:(oF' 0x525e0%Z)) (ltac:(oD' 0x525e0%Z)).
stepn (ltac:(oF' 0x525e4%Z)) (ltac:(oD' 0x525e4%Z)).
zcall (art_run_malloc_hooks_fn _ _ _ _ sp).
zstep (ltac:(oF' 0x525e8%Z)) (ltac:(oD' 0x525e8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (C120 : cellA X (sp + 120) 8 (U raw0)) by (recell F120);
assert (C112 : cellA X (sp + 112) 8 s0v) by (recell F112);
assert (C104 : cellA X (sp + 104) 8 s1v) by (recell F104);
assert (C96 : cellA X (sp + 96) 8 s2v) by (recell F96);
assert (C88 : cellA X (sp + 88) 8 s3v) by (recell F88);
assert (C80 : cellA X (sp + 80) 8 s4v) by (recell F80);
assert (C72 : cellA X (sp + 72) 8 s5v) by (recell F72);
assert (C64 : cellA X (sp + 64) 8 s6v) by (recell F64);
assert (C56 : cellA X (sp + 56) 8 s7v) by (recell F56);
assert (C48 : cellA X (sp + 48) 8 s8v) by (recell F48);
assert (C40 : cellA X (sp + 40) 8 s9v) by (recell F40);
assert (C32 : cellA X (sp + 32) 8 s10v) by (recell F32);
assert (C24 : cellA X (sp + 24) 8 s11v) by (recell F24); idtac end.
zld (ltac:(oF' 0x525ec%Z)) (ltac:(oD' 0x525ec%Z)) (sp + 120) C120. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x525f0%Z)) (ltac:(oD' 0x525f0%Z)) (sp + 112) C112.
zld (ltac:(oF' 0x525f4%Z)) (ltac:(oD' 0x525f4%Z)) (sp + 104) C104.
zld (ltac:(oF' 0x525f8%Z)) (ltac:(oD' 0x525f8%Z)) (sp + 96) C96.
zld (ltac:(oF' 0x525fc%Z)) (ltac:(oD' 0x525fc%Z)) (sp + 88) C88.
zld (ltac:(oF' 0x52600%Z)) (ltac:(oD' 0x52600%Z)) (sp + 80) C80.
zld (ltac:(oF' 0x52604%Z)) (ltac:(oD' 0x52604%Z)) (sp + 72) C72.
zld (ltac:(oF' 0x52608%Z)) (ltac:(oD' 0x52608%Z)) (sp + 64) C64.
zld (ltac:(oF' 0x5260c%Z)) (ltac:(oD' 0x5260c%Z)) (sp + 56) C56.
zld (ltac:(oF' 0x52610%Z)) (ltac:(oD' 0x52610%Z)) (sp + 48) C48.
zld (ltac:(oF' 0x52614%Z)) (ltac:(oD' 0x52614%Z)) (sp + 40) C40.
zld (ltac:(oF' 0x52618%Z)) (ltac:(oD' 0x52618%Z)) (sp + 32) C32.
zld (ltac:(oF' 0x5261c%Z)) (ltac:(oD' 0x5261c%Z)) (sp + 24) C24.
zstep (ltac:(oF' 0x52620%Z)) (ltac:(oD' 0x52620%Z)).
stepret (ltac:(oF' 0x52624%Z)) (ltac:(oD' 0x52624%Z)) raw0 ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_alloc_e32_fn := (ltac2:(TCodec.tc2 tcn__JbtAllocE "\>&5y5'QEyR0%211%5241'0y8%611%311p061'4'3&?rG(QC+2(1%33A21%6251&QDrC%22C1%;3C41rH+4%;3I19%>231r?%92J1%B3J31rI+8%B3Q01@%E231+1%@2Q11%I3Q131rJ+9%I3Q71G%L231rD%G2Q81%Q03Q831rK+B%Q03Q>1N%Q3231rF%N2Q?1%Q73Q?31rL+D%Q73QE1Q5%Q:231&CrE%22Q<1%Q72QH1%Q@3QH51rM+E%Q@3QN1Q>%QC231&I%:2Q:A+@%3221%QA2R21%QJ3R261&E+Q0%221Q3&F+T0%D2O1&H+R0%22QO1%6241+Vb\P0%J21:%<21O&>%>21Q1+RPP0%O2J1+Q?%<2R91%@231&GrN%221Jz%RC3RD21'2%J2QN5+Q8%F2RC1%J281%5241%O28Q9+X0%N2Q;1%9231+TP0%QC2?1%Q221M%Q62?ArQ0rO%QH221%QI21RH%Q821Q3&<rQ7%211&9&BrQ:+QVdP0u8rQ1%6554321rQ;rQ3rQ2%R8221u4%<5;521Q4&8rQ4%R=217rQ8rQ6%R@221%R821R6%745SA1R7rQ=rQ9%RE21I%R=21R;%RG21S<u1%K5J621:&:rQ>%RL2L>%RD21RB%44O31RCrQ?rQ<%RH21RA%84Q331RB&=rQ@%211rQA+QiiX0%Q:5Q921Q6R2%S92>9%S121RO%S22<RK+U0%Q243S221%S52:RN%Q44@S413rQD+SH%SB2<1&QFrQB%22U:1%QH5QG64QD1rQE+S@%SI251%QL5QK31QHQErQFrQC+S8%SN221%R15R041QMQJrQG+S0%T22B1%R55R431R1QNrQH+RH%T62?1%R95R831R5R2rQI+R@%T:2?1%R=5R<31R9R6rQJ+R8%T>2>1%RA5R@31R=R:rQK%TA2=SK%RD5RC21R@R=rQL+QH%TE2=1%RH5RG31RDRArQM+Q@%TI2=1%RL5RK31RHRErQN%TL2<SB%RO5RN21RKRHrQO%TO2<T?%S25S121RNRKrR0+H%U32<1%S65S531S2RO%TF2TEE+RP0%TH2G1%T0231%T62FTN%VF3VG1T4rR3%RB4S=1>U1rR4+RPjH+\hkdfgWVVmUeI%SB5SA32S>1';&@vMrR6+ZY\D%VO3W;1VM/01W;rR5%756521<&A%W43WBV@W2%2381ArR2%UN21U;%W32WD1%634W61%W52WFQA%832VI1%W72WHQG%:32VD1+:%W?3WM1W=rR1%V821Q:%W=2WN1%@3641+;%WE3X31WC%WA2X2Q<%D3421+<%WI3X71WG%WE2X6U;%H3421+=%WM3X;1WK%VE2>V:%WJ2X;1%M3531%WL2X=R@%O32W21+C%X43XB1X2%X02XARH%Q33421%X22XCRN%Q532W11%X42XES5%Q732VJ1+F%X<3XJ1X:%X82XIS=%Q;3421+G%X@3XN1X>%X<2XMSH%Q?3421%XC3Y1R8XA%X?2Y0S?%QB3321+I%XG3Y51XE%XC2Y4SK%QF3421+J%XK3Y91XI%XG2Y8T=%QJ3421+K%XO3Y=1XM%XK2Y<TC%QN3421&7+?%WB2QC1&D+WC%22S31%64U7R741%WG2QHWE%84U921Y9%X22QKXJ%:4V1213%;4V21QMRE%WL2R8XM+ZY_8%>4V5321%WO2R;WM%@4V721XN%X12R=S8%B4V921S:%X32R?WL%D4V;21R6%RL5RKFS31S1%RN3V@RF1p0S01p0S51p0S81p0S;1p0S@1p0SE1p0SI1p0SM1p0T21p0T71p0T;1p0T@1p0TE1p0TJ1p0TO1p0U51p0U:1p0UB1p0UE1p0UK1p0UO1p0V31p0V81p0V>1p0VF1p0VO1p0W61p0W>1p0WB1p0WH1p0WJ1p0X11p0WO1p0X41p0X;1p0XA1p0XG1p0XJ1p0XN1p0Y61p0Y:1p0YE1p0YO1p0Z71p0Z?1p0ZG1p0ZO1pRB[<1pR@[=1pS4[>1pS2[?1pS0[@1pRN[A1pRL[B1pRJ[C1pRH[D1pRF[E1pRD[F1pR>[G1pQN[H1pS@[I1pQJ[J1pR<[K1pR2[L1pQH[M1pS6[N1pR6\61pR:\11p>\21pR8\81")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 2%nat 0%nat).
Variable raw0 : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 4%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 6%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 7%nat 0%nat).
Variable b1 : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 8%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 9%nat 0%nat).
Variable loff : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 10%nat 0%nat).
Variable s0v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 11%nat 0%nat).
Variable s1v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 12%nat 0%nat).
Variable s2v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 13%nat 0%nat).
Variable s3v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 14%nat 0%nat).
Variable s4v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 15%nat 0%nat).
Variable s5v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 16%nat 0%nat).
Variable s6v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 17%nat 0%nat).
Variable s7v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 18%nat 0%nat).
Variable s8v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 19%nat 0%nat).
Variable s9v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 20%nat 0%nat).
Variable s10v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 21%nat 0%nat).
Variable s11v : ltac:(sec_ty2 constr:(SEC_T_art_alloc_e32_fn) 22%nat 0%nat).
Lemma art_alloc_e32_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_e32_fn) 23%nat 0%nat).
Proof using Type regs M rom raw0 sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v.
intros H2 H4 H8 H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24.
intros Hrz Hrz16 Wab Cmag. unfold kHighMemBeg in *.
pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
pose proof (land_le_l' b1 243 ltac:(lia) ltac:(lia)) as Lb.
stepn (ltac:(oF' 0x52594%Z)) (ltac:(oD' 0x52594%Z)).
zcall (art_lsan_off_fn _ _ _ _ tp loff).
zlbu (ltac:(oF' 0x52598%Z)) (ltac:(oD' 0x52598%Z)) (ab + rz - 16 + 1) Cb1.
zstep (ltac:(oF' 0x5259c%Z)) (ltac:(oD' 0x5259c%Z)). zstep (ltac:(oF' 0x525a0%Z)) (ltac:(oD' 0x525a0%Z)).
stepn (ltac:(oF' 0x525a4%Z)) (ltac:(oD' 0x525a4%Z)). rwH. rewrite art_zb_andi by lia.
stepn (ltac:(oF' 0x525a8%Z)) (ltac:(oD' 0x525a8%Z)). rwH. unfold v_or. rewrite !art_u_lit by lia. rewrite Z.lor_0_r.
zstep (ltac:(oF' 0x525ac%Z)) (ltac:(oD' 0x525ac%Z)).
zsb (ltac:(oF' 0x525b0%Z)) (ltac:(oD' 0x525b0%Z)) (ab + rz - 16 + 1) (Z.land b1 243) ltac:(rewok Wh).
stepfence (ltac:(oF' 0x525b4%Z)) (ltac:(oD' 0x525b4%Z)).
zsb (ltac:(oF' 0x525b8%Z)) (ltac:(oD' 0x525b8%Z)) (ab + rz - 16) 2 ltac:(rewok Wh).
zbft (ltac:(oF' 0x525bc%Z)) (ltac:(oD' 0x525bc%Z)).
zstep (ltac:(oF' 0x525c0%Z)) (ltac:(oD' 0x525c0%Z)).
zbft (ltac:(oF' 0x525c4%Z)) (ltac:(oD' 0x525c4%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmag' : cellA X 0x10358 8 0xcc6e96b9cc6e96b9) by (recell Cmag) end.
zstep (ltac:(oF' 0x525c8%Z)) (ltac:(oD' 0x525c8%Z)). zld (ltac:(oF' 0x525cc%Z)) (ltac:(oD' 0x525cc%Z)) 0x10358 Cmag'.
zsd (ltac:(oF' 0x525d0%Z)) (ltac:(oD' 0x525d0%Z)) (ab + 8) (ab + rz - 16) ltac:(rewok Wab).
stepfence (ltac:(oF' 0x525d4%Z)) (ltac:(oD' 0x525d4%Z)).
zsd (ltac:(oF' 0x525d8%Z)) (ltac:(oD' 0x525d8%Z)) ab 0xcc6e96b9cc6e96b9 ltac:(rewok Wab).
zstep (ltac:(oF' 0x525dc%Z)) (ltac:(oD' 0x525dc%Z)). zstep (ltac:(oF' 0x525e0%Z)) (ltac:(oD' 0x525e0%Z)).
stepn (ltac:(oF' 0x525e4%Z)) (ltac:(oD' 0x525e4%Z)).
zcall (art_run_malloc_hooks_fn _ _ _ _ sp).
zstep (ltac:(oF' 0x525e8%Z)) (ltac:(oD' 0x525e8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (C120 : cellA X (sp + 120) 8 (U raw0)) by (recell F120);
assert (C112 : cellA X (sp + 112) 8 s0v) by (recell F112);
assert (C104 : cellA X (sp + 104) 8 s1v) by (recell F104);
assert (C96 : cellA X (sp + 96) 8 s2v) by (recell F96);
assert (C88 : cellA X (sp + 88) 8 s3v) by (recell F88);
assert (C80 : cellA X (sp + 80) 8 s4v) by (recell F80);
assert (C72 : cellA X (sp + 72) 8 s5v) by (recell F72);
assert (C64 : cellA X (sp + 64) 8 s6v) by (recell F64);
assert (C56 : cellA X (sp + 56) 8 s7v) by (recell F56);
assert (C48 : cellA X (sp + 48) 8 s8v) by (recell F48);
assert (C40 : cellA X (sp + 40) 8 s9v) by (recell F40);
assert (C32 : cellA X (sp + 32) 8 s10v) by (recell F32);
assert (C24 : cellA X (sp + 24) 8 s11v) by (recell F24); idtac end.
zld (ltac:(oF' 0x525ec%Z)) (ltac:(oD' 0x525ec%Z)) (sp + 120) C120. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x525f0%Z)) (ltac:(oD' 0x525f0%Z)) (sp + 112) C112.
zld (ltac:(oF' 0x525f4%Z)) (ltac:(oD' 0x525f4%Z)) (sp + 104) C104.
zld (ltac:(oF' 0x525f8%Z)) (ltac:(oD' 0x525f8%Z)) (sp + 96) C96.
zld (ltac:(oF' 0x525fc%Z)) (ltac:(oD' 0x525fc%Z)) (sp + 88) C88.
zld (ltac:(oF' 0x52600%Z)) (ltac:(oD' 0x52600%Z)) (sp + 80) C80.
zld (ltac:(oF' 0x52604%Z)) (ltac:(oD' 0x52604%Z)) (sp + 72) C72.
zld (ltac:(oF' 0x52608%Z)) (ltac:(oD' 0x52608%Z)) (sp + 64) C64.
zld (ltac:(oF' 0x5260c%Z)) (ltac:(oD' 0x5260c%Z)) (sp + 56) C56.
zld (ltac:(oF' 0x52610%Z)) (ltac:(oD' 0x52610%Z)) (sp + 48) C48.
zld (ltac:(oF' 0x52614%Z)) (ltac:(oD' 0x52614%Z)) (sp + 40) C40.
zld (ltac:(oF' 0x52618%Z)) (ltac:(oD' 0x52618%Z)) (sp + 32) C32.
zld (ltac:(oF' 0x5261c%Z)) (ltac:(oD' 0x5261c%Z)) (sp + 24) C24.
zstep (ltac:(oF' 0x52620%Z)) (ltac:(oD' 0x52620%Z)).
stepret (ltac:(oF' 0x52624%Z)) (ltac:(oD' 0x52624%Z)) raw0 ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
End FPX.
