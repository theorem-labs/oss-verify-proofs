(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtAllocB () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "3Z"; "4bvmap"; "0M"; "5apart"; "5cell"; "5wr"; "6msteps"; "7art_alloc_memB"; "7art_hdr_b1"; "7art_hdr_b1a"; "8getr"; "8mkst"]; ["8regupd"; "9loaded_segments"; ":add"; ":div"; ":land"; ":le"; ":lor"; ":lt"; ":max"; ":modulo"; ":mul"; ":pow"; ":sub"; "0a"; "0ab"; "0b"]; ["0ctx"; "0fx"; "0m"; "0n"; "0ob"; "0regs"; "0rom"; "0rs"; "0rz"; "0sp"; ";BV"; ";Z_to_bv"; ";bv"; "0stk"; "0szt"; "0t"]; ["0trp"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_hdr_b1a (ob : Z) : Z := Z.lor (Z.land ob 18446744073709551612) 1.
Definition art_hdr_b1 (ob : Z) : Z := Z.lor (Z.land (art_hdr_b1a ob) 143) 16.
Lemma lor_lt_256 : ltac2:(TCodec.tc2 tcn__JbtAllocB "E'4'2&Ezr2%3221&G+X0%2241%8241&Fr4r3%3221%<2;1%9228%?221p081p091pR0C1pQLD1").
Proof.
intros a b Ha Hb. split. apply Z.lor_nonneg; lia.
destruct (Z.eq_dec (Z.lor a b) 0) as [E|NZ]; [rewrite E; lia|].
assert (Hl : Z.log2 (Z.lor a b) < 8).
{ rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
- destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
apply Z.log2_lt_pow2 in Hl; [exact Hl|]. pose proof (Z.lor_nonneg a b). lia.
Qed.
Lemma land_le_l : ltac2:(TCodec.tc2 tcn__JbtAllocB "A'4&Ezr2%3221'2&Dr4r3%3221%9281%:224%7221p091p0:1pR6?1pQL@1").
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
Lemma art_hdr_b1a_range : ltac2:(TCodec.tc2 tcn__JbtAllocB "B'4'2&Ezr1%3221&G+X0%2241%8241&=r2%211%;2:1%8227%>221p071pR:A1").
Proof. intros ob Hob. unfold art_hdr_b1a. apply lor_lt_256; [|lia]. pose proof (land_le_l ob 18446744073709551612 ltac:(lia) ltac:(lia)). lia. Qed.
Lemma art_hdr_b1_range : ltac2:(TCodec.tc2 tcn__JbtAllocB "B'4'2&Ezr1%3221&G+X0%2241%8241&<r2%211%;2:1%8227%>221p071pR:A1").
Proof. intros ob Hob. unfold art_hdr_b1. pose proof (art_hdr_b1a_range ob Hob). apply lor_lt_256; [|lia]. pose proof (land_le_l (art_hdr_b1a ob) 143 ltac:(lia) ltac:(lia)). lia. Qed.
Definition art_alloc_memB (M : word -> option byte) (ab rz n ob : Z) : word -> option byte :=
Wn 1 (Wn 4 (Wn 2 (Wn 1 M (ab + rz - 15) (art_hdr_b1a ob)) (ab + rz - 14) (n / 2 ^ 32)) (ab + rz - 12) n) (ab + rz - 15) (art_hdr_b1 ob).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_alloc_b_fn := (ltac2:(TCodec.tc2 tcn__JbtAllocB "YD&5y5'Q<yR0%211%5241'0y8%611%311p061'4'3&>r>(Q:+2(1%33A21%6251&Q;r;%22C1%;3C41r?+:%;3I19%>231%@3H16r@+9%@3N1>%C231%E3M1;rA+C%E3Q31C%H231&Br:%22C1%E2Q61%N3Q651rB+D%N3Q<1L%Q1231%Q33Q;1IrC+E%Q33QA1Q1%Q6231%Q02QAQ6%Q93QA21rD+G%Q93QG1Q7%Q<231r<%Q72QH1%Q@3QH31rE+I%Q@3QN1Q>%QC231+7%Q>2QO1%QG3QO31rF+J%QG3R51QE%QJ231r=%QE2R61%QN3R631rG+K%QN3R<1QL%R1231+1%QL2R=1%R53R=31&Ez%221G&G+T0%QA2C1&K+R0%22R:1%6241+TP0%;21I+RPP0%QI2D1+Q?%92RA1%=231&IrH+@%3221%RK3RL1D'2%G2J5+Q8%C2RK1%G281%5241&J&C&HrI+8%3221%R>21QC%6213%8214%S;3S<C1%Q62CD+RP0%Q82F1%C231%I2;G%SA3SB1Q:rKrJ%RJ221%Q?21Q3%Q@2Q63%RM25N%Q?21Q:%QC2Q97rL%S121Q;%QC21Q>%QG2Q=3rM%S521Q?%QG21QB%QK2QJ3+X0%QJ251%Q8231%QL27QG%Q:251&9&ArQ:&LrQ7rQ4%SC221%421QE%84761QF&8rQ;rQ8rQ5%SJ221+?%<221u1rQ1%95A8321rQ<%T12BR2u8%=5E321R4rQ=%?5G1<3CrQ>%T72>QKu4%C5K321RLrQ?%E5M1C9IrQ@rQ9%T>21R2%I5Q131=M&7%TA2;J%Q221RC%341RD9S3%TD2:D%Q521RF%641RGQ7R:%TG2;C%Q821RI%TI2Q:R=+4%;43RL21rQA%TM21G%Q>21RO%?41S0KS0':&?vQ1rQF+ZXZD%UL3V81UJ/01V8rQErQD%8576321&@%V23V@T2V0+ZXc0%V43V@1V2/01V@%53<41%V22VCR1%732UM1+;%V:3VH1V8%V62VGQ7%;3421+<%V>3VL1V<%V:2VKT;%?3421+>%VB3W01V@rQB%UM21QA%UN21QD%VA2W21%F3751+B%VI3W71VG%VE2W67%J3421%V529QK%VH2W91%M33V01%RH23T9%VK2W<1%Q033UN1+H%W33WA1W1%Q3331E%V>29QB%W12WB1%Q633UG1+cVYL%W93WE1W7/01WE&;%15Q>IR;QIRN%QE5QD631Q>%QG3S9Q>1p0QI1p0QN1p0R41p0R81p0R=1p0RB1p0RE1p0RJ1p0RM1p0S21p0S=1p0SG1p0SH1p0SK1p0T01p0T41p0T61p0T:1p0T<1p0T?1p0TA1p0TF1p0TI1p0TN1p0U91p0U@1p0UF1p0UL1p0UO1p0V71p0V;1p0VC1p0VK1p0W31p0W;1p0WB1p0WH1p0X21p0X81p0X>1pRNXK1pS2XL1pR:XM1pR2XN1pS0XO1pRLY01pRBY11pR@Y21pR8Y31pQNY41pRDY51pR>Y71p>Y81pR<Y>1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_fn) 3%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_fn) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_fn) 5%nat 0%nat).
Lemma art_alloc_b_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_b_fn) 6%nat 0%nat).
Proof using Type regs M rom sp ab n.
intros rs rz stk t ctx ob trp szt H2 H10 H9 H19 H20 H21 H23 H25 H26 H27 Hsp Hsp' Hab Hab' Hab16 Hn Hrs Hrz Hrz16 Hprim
Hstk Hstk' Ht Ht' Hctx Hctx' Hob Htrp Hszt W Cob C16 Cctx Ctid Ctrp Cszt A1 A2 A3 A4.
assert (Hrsn : n <= rs /\ rs <= n + 15) by (subst rs; split; [|]; lia).
pose proof (art_hdr_b1a_range ob Hob) as Rb1a. pose proof (art_hdr_b1_range ob Hob) as Rb1.
zstep (ltac:(oF' 0x52154%Z)) (ltac:(oD' 0x52154%Z)).
zbft (ltac:(oF' 0x52158%Z)) (ltac:(oD' 0x52158%Z)).
zstep (ltac:(oF' 0x5215c%Z)) (ltac:(oD' 0x5215c%Z)).
stepn (ltac:(oF' 0x52160%Z)) (ltac:(oD' 0x52160%Z)). rwH. rewrite art_zb_and by lia. change 7 with (Z.ones 3) at 1. rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
replace ((ab + rz) mod 8) with 0 by lia.
zstep (ltac:(oF' 0x52164%Z)) (ltac:(oD' 0x52164%Z)).
zbtk (ltac:(oF' 0x52168%Z)) (ltac:(oD' 0x52168%Z)).
zstep (ltac:(oF' 0x52174%Z)) (ltac:(oD' 0x52174%Z)).
zbft (ltac:(oF' 0x52178%Z)) (ltac:(oD' 0x52178%Z)).
zlbu (ltac:(oF' 0x5217c%Z)) (ltac:(oD' 0x5217c%Z)) (ab + rz - 15) Cob.
stepn (ltac:(oF' 0x52180%Z)) (ltac:(oD' 0x52180%Z)). rwH. rewrite art_zb_andi by lia. change (Z.land 1 3) with 1.
stepn (ltac:(oF' 0x52184%Z)) (ltac:(oD' 0x52184%Z)). rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612.
pose proof (land_le_l ob 18446744073709551612 ltac:(lia) ltac:(lia)) as Lb.
stepn (ltac:(oF' 0x52188%Z)) (ltac:(oD' 0x52188%Z)). rwH. unfold v_or. rewrite !art_u_lit by lia.
change (Z.lor (Z.land ob 18446744073709551612) 1) with (art_hdr_b1a ob).
stepn (ltac:(oF' 0x5218c%Z)) (ltac:(oD' 0x5218c%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x52190%Z)) (ltac:(oD' 0x52190%Z)). rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small n (2 ^ 48)) by lia.
zsb (ltac:(oF' 0x52194%Z)) (ltac:(oD' 0x52194%Z)) (ab + rz - 15) (art_hdr_b1a ob) ltac:(rewok W).
zsh (ltac:(oF' 0x52198%Z)) (ltac:(oD' 0x52198%Z)) (ab + rz - 14) (n / 2 ^ 32) ltac:(rewok W).
zsw (ltac:(oF' 0x5219c%Z)) (ltac:(oD' 0x5219c%Z)) (ab + rz - 12) n ltac:(rewok W).
zbft (ltac:(oF' 0x521a0%Z)) (ltac:(oD' 0x521a0%Z)).
zstep (ltac:(oF' 0x521a4%Z)) (ltac:(oD' 0x521a4%Z)).
stepn (ltac:(oF' 0x521a8%Z)) (ltac:(oD' 0x521a8%Z)). rwH. rewrite art_zb_andi by lia.
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (sp + 16) 8 16) by (unfold apart in *; recell C16) end.
zld (ltac:(oF' 0x521ac%Z)) (ltac:(oD' 0x521ac%Z)) (sp + 16) C16'.
pose proof (land_le_l (art_hdr_b1a ob) 143 ltac:(lia) ltac:(lia)) as Lb2.
stepn (ltac:(oF' 0x521b0%Z)) (ltac:(oD' 0x521b0%Z)). rwH. unfold v_or. rewrite !art_u_lit by lia.
change (Z.lor (Z.land (art_hdr_b1a ob) 143) 16) with (art_hdr_b1 ob).
zsb (ltac:(oF' 0x521b4%Z)) (ltac:(oD' 0x521b4%Z)) (ab + rz - 16 + 1) (art_hdr_b1 ob) ltac:(rewok W).
zbft (ltac:(oF' 0x521b8%Z)) (ltac:(oD' 0x521b8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Cctx' : cellA X t 8 ctx) by (unfold apart in *; recell Cctx);
assert (Ctid' : cellA X (ctx + 8) 4 0) by (unfold apart in *; recell Ctid);
assert (Ctrp' : cellA X stk 8 trp) by (unfold apart in *; recell Ctrp);
assert (Cszt' : cellA X (stk + 8) 8 szt) by (unfold apart in *; recell Cszt) end.
zld (ltac:(oF' 0x521bc%Z)) (ltac:(oD' 0x521bc%Z)) t Cctx'.
zlw (ltac:(oF' 0x521c0%Z)) (ltac:(oD' 0x521c0%Z)) (ctx + 8) Ctid'.
zstep (ltac:(oF' 0x521c4%Z)) (ltac:(oD' 0x521c4%Z)).
stepn (ltac:(oF' 0x521c8%Z)) (ltac:(oD' 0x521c8%Z)).
zld (ltac:(oF' 0x52254%Z)) (ltac:(oD' 0x52254%Z)) stk Ctrp'.
zld (ltac:(oF' 0x52258%Z)) (ltac:(oD' 0x52258%Z)) (stk + 8) Cszt'.
stepn (ltac:(oF' 0x5225c%Z)) (ltac:(oD' 0x5225c%Z)).
unfold art_alloc_memB. zret.
Qed.
End SE.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
