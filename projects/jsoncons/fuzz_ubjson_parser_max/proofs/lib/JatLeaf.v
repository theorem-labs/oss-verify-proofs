(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib
ArtMem ArtRegs ArtAtomics ArtTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatLeaf () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "1option"; "2I"; "2and"; "2eq"; "3Z"; "4bvmap"; "0M"; "5Wn"; "5apart"; "5cell"; "5wr"; "6msteps"; "7ret_ok"; "8art_tsd"; "9getr"]; ["9mkst"; "9regupd"; ":loaded_segments"; ";add"; ";le"; ";lt"; ";mul"; ";of_nat"; ";pow"; ";sub"; "0a"; "0bot"; "0ctx"; "0fx"; "0key"; "0n"]; ["0off"; "0raw"; "0regs"; "0rom"; "0sp"; "<BV"; "<Z_to_bv"; "<bv"; "<bv_unsigned"; "0t"; "0top"; "0tp"; "0tsd"; "0v"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_asan_inited_fn : ltac2:(TCodec.tc2 tcn__JatLeaf "QF&6y5'Q7yR0%211%5241'1y8%611%311p061'4&?r4(Q5+1(2%33@21%6251r1%93@21&=r2%211&:&Br5+QW^^Hu1%554321>'<&@vMr7+_nSL%E3Q01C/01Q0r6%756521<&A+:%K3Q81I&Q6%12Q8L%53;31%>5=1Q08C%@3E81p0B1p0I1p0M1pR4Q>1pR8Q91p@Q:1pR6Q@1").
Proof.
intros regs M rom raw H1 Hret C.
zstep (ltac:(oF' 0x7f87c%Z)) (ltac:(oD' 0x7f87c%Z)).
zlb (ltac:(oF' 0x7f880%Z)) (ltac:(oD' 0x7f880%Z)) 0x13b9d8 C.
stepfence (ltac:(oF' 0x7f884%Z)) (ltac:(oD' 0x7f884%Z)).
zstep (ltac:(oF' 0x7f888%Z)) (ltac:(oD' 0x7f888%Z)).
zstep (ltac:(oF' 0x7f88c%Z)) (ltac:(oD' 0x7f88c%Z)).
stepret (ltac:(oF' 0x7f890%Z)) (ltac:(oD' 0x7f890%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
#[using="Type"] Lemma art_rss_limit_fn : ltac2:(TCodec.tc2 tcn__JatLeaf "QG&6y5'Q7yR0%211%5241'1y8%611%311p061'4&?r4(Q5+1(2%33@21%6251r1%93@21&=r2%211&:&Br5+Qgck2u1z%6554321'<&@vMr7+`eZ4%F3Q11D/01Q1r6%756521=&A+:%L3Q91J&Q6%12Q9?%53;31%>5=1Q18D%@3F81p0B1p0J1p0N1pR4Q?1pR8Q:1p@Q;1pR6QA1").
Proof.
intros regs M rom raw H1 Hret C.
zstep (ltac:(oF' 0x85544%Z)) (ltac:(oD' 0x85544%Z)).
zlb (ltac:(oF' 0x85548%Z)) (ltac:(oD' 0x85548%Z)) 0x1bcf62 C.
zstep (ltac:(oF' 0x8554c%Z)) (ltac:(oD' 0x8554c%Z)).
stepret (ltac:(oF' 0x85550%Z)) (ltac:(oD' 0x85550%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
#[using="Type"] Lemma art_may_return_null_fn : ltac2:(TCodec.tc2 tcn__JatLeaf "QF&6y5'Q7yR0%211%5241'1y8%611%311p061'4&?r4(Q5+1(2%33@21%6251r1%93@21&=r2%211&:&Br5+Qgck1u1%554321>'<&@vMr7+`eXL%E3Q01C/01Q0r6%756521<&A+:%K3Q81I&Q6%12Q8L%53;31%>5=1Q08C%@3E81p0B1p0I1p0M1pR4Q>1pR8Q91p@Q:1pR6Q@1").
Proof.
intros regs M rom raw H1 Hret C.
zstep (ltac:(oF' 0x8551c%Z)) (ltac:(oD' 0x8551c%Z)).
zlb (ltac:(oF' 0x85520%Z)) (ltac:(oD' 0x85520%Z)) 0x1bcf61 C.
zstep (ltac:(oF' 0x85524%Z)) (ltac:(oD' 0x85524%Z)).
stepret (ltac:(oF' 0x85528%Z)) (ltac:(oD' 0x85528%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
#[using="Type"] Lemma art_can_poison_fn : ltac2:(TCodec.tc2 tcn__JatLeaf "QF&6y5'Q7yR0%211%5241'1y8%611%311p061'4&?r4(Q5+1(2%33@21%6251r1%93@21&=r2%211&:&Br5+QWYZLu1%554321>'<&@vMr7+_X^<%E3Q01C/01Q0r6%756521<&A+:%K3Q81I&Q6%12Q8L%53;31%>5=1Q08C%@3E81p0B1p0I1p0M1pR4Q>1pR8Q91p@Q:1pR6Q@1").
Proof.
intros regs M rom raw H1 Hret C.
zstep (ltac:(oF' 0x7a1cc%Z)) (ltac:(oD' 0x7a1cc%Z)).
zlb (ltac:(oF' 0x7a1d0%Z)) (ltac:(oD' 0x7a1d0%Z)) 0x13a55c C.
stepfence (ltac:(oF' 0x7a1d4%Z)) (ltac:(oD' 0x7a1d4%Z)).
zstep (ltac:(oF' 0x7a1d8%Z)) (ltac:(oD' 0x7a1d8%Z)).
stepret (ltac:(oF' 0x7a1dc%Z)) (ltac:(oD' 0x7a1dc%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
#[using="Type"] Lemma art_malloc_ctx_fn : ltac2:(TCodec.tc2 tcn__JatLeaf "QG&6y5'Q7yR0%211%5241'1y8%611%311p061'4&?r4(Q5+1(2%33@21%6251r1%93@21&=r2%211&:&Br5+QW^_Lu4+N%6554321'<&@vMr7+`UXD%F3Q11D/01Q1r6%756521=&A+:%L3Q91J&Q6%12Q9?%53;31%>5=1Q18D%@3F81p0B1p0J1p0N1pR4Q?1pR8Q:1p@Q;1pR6QA1").
Proof.
intros regs M rom raw H1 Hret C.
zstep (ltac:(oF' 0x81514%Z)) (ltac:(oD' 0x81514%Z)).
zlw (ltac:(oF' 0x81518%Z)) (ltac:(oD' 0x81518%Z)) 0x13b9fc C.
stepfence (ltac:(oF' 0x8151c%Z)) (ltac:(oD' 0x8151c%Z)).
stepret (ltac:(oF' 0x81520%Z)) (ltac:(oD' 0x81520%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
#[using="Type"] Lemma art_get_pc_fn : ltac2:(TCodec.tc2 tcn__JatLeaf "Q?&6y5'Q7yR0%211%5241'1y8%611%311p061'4&?r4(Q5+1(2%33@21%6251r1%93@21&=r2%211'<&B&@vMr6+cWo@%@3K1>/01Kr5%756521D&A+:%F3Q31Dr3%43:21%=5<127J%@3?71p0B1p0F1pR4Q71pR8Q21p@Q31pR6Q91").
Proof.
intros regs M rom raw H1 Hret.
zstep (ltac:(oF' 0x99ff0%Z)) (ltac:(oD' 0x99ff0%Z)).
stepret (ltac:(oF' 0x99ff4%Z)) (ltac:(oD' 0x99ff4%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
Section SE.
Local Abbreviation SEC_T_art_try_init_fn := (ltac2:(TCodec.tc2 tcn__JatLeaf "S:&6y5'Q7yR0%211%5241'1y8%611%311p061'5'4&?r5(Q5+1(2%33A21%6251r2%93A21&=r3%211r7+2%<3J1:%?231&Q6%12K7%C3K31&D+@r4%3221&E&H+R0%22=1%42J1&;&Br9&Ir6%221=%64541>&:r:+QW^^Hu1%45:321Q4&9r8%;21F%341G6Q8'<&@vMr=+`Ql<%Q?3QK1Q=/01QKr<r;%8576321&A%138QBC%Q82R2J%332Q;1+8%QI3R71QG%QL2=1%73421+:%QM3R;1QK%Q@2R:QM%;3421+;%R13R?1QO%>3314&8u8%Q82Q9=&Q8%12RCQ5%544G31%Q<2Q=QG%42RF@%847321%Q15Q0:Q:1J%Q33QBJ1p0Q51p0Q:1p0Q@1p0QH1p0QN1p0R31p0R;1p0R?1pR:RJ1pR4S21pR8RM1p@RN1pR6S41")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_try_init_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_try_init_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_try_init_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_try_init_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_try_init_fn) 4%nat 0%nat).
Lemma art_try_init_fn : ltac:(sec_stmt2 constr:(SEC_T_art_try_init_fn) 5%nat 0%nat).
Proof using Type regs M rom raw sp.
intros H1 Hret H2 Hsp Hsp' W C Ap.
zstep (ltac:(oF' 0x8078c%Z)) (ltac:(oD' 0x8078c%Z)).
zsd (ltac:(oF' 0x80790%Z)) (ltac:(oD' 0x80790%Z)) (sp - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x80794%Z)) (ltac:(oD' 0x80794%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zstep (ltac:(oF' 0x80798%Z)) (ltac:(oD' 0x80798%Z)). zstep (ltac:(oF' 0x8079c%Z)) (ltac:(oD' 0x8079c%Z)).
assert (C1 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) 0x13b9d8 1 1) by (unfold apart in *; recell C).
zlb (ltac:(oF' 0x807a0%Z)) (ltac:(oD' 0x807a0%Z)) 0x13b9d8 C1.
zstep (ltac:(oF' 0x807a4%Z)) (ltac:(oD' 0x807a4%Z)).
stepfence (ltac:(oF' 0x807a8%Z)) (ltac:(oD' 0x807a8%Z)).
zbft (ltac:(oF' 0x807ac%Z)) (ltac:(oD' 0x807ac%Z)).
assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 8) 8 (U raw)).
{ apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
assert (Cs0 : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 16) 8 (U (getr regs 8))) by (apply cell_Wn_hit; lia).
zld (ltac:(oF' 0x807b0%Z)) (ltac:(oD' 0x807b0%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x807b4%Z)) (ltac:(oD' 0x807b4%Z)) (sp - 16) Cs0. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x807b8%Z)) (ltac:(oD' 0x807b8%Z)).
stepret (ltac:(oF' 0x807bc%Z)) (ltac:(oD' 0x807bc%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_lsan_off_fn : ltac2:(TCodec.tc2 tcn__JatLeaf "RM&6y5'Q7yR0%211%5241'1y8%611%311p061'5'4&?r6(Q5+1(2%33A21%6251r3%93A21&=r4%211r8+4%<3J1:%?231&Q6%12K7%C3K31&Dzr5%3221&E&C+TP0%22I1&H+2+R0%3221%8251%=2<Or7%:2F1%;21F%=216&:&Br<+QV\dHu8%554321Nr=r:r9%F221u4%;5:521L'<&@vMr?+djk<%QD3R01QB/01R0r>%756521>&A+:%QJ3R81QH%Q=2R7Q9%43:21%=5<1H7D%?3J71p0A1p0H1p0O1p0Q41p0Q61p0Q@1p0QE1p0QM1p0R11pR2R<1pRHR=1pR4RE1pR8R@1p@RA1pR6RG1").
Proof.
intros regs M rom raw tp off H1 Hret H4 Htp Htp' Hoff Hoff' Cg Ct.
zstep (ltac:(oF' 0xa6b6c%Z)) (ltac:(oD' 0xa6b6c%Z)).
zld (ltac:(oF' 0xa6b70%Z)) (ltac:(oD' 0xa6b70%Z)) 0x133298 Cg.
zstep (ltac:(oF' 0xa6b74%Z)) (ltac:(oD' 0xa6b74%Z)).
zlw (ltac:(oF' 0xa6b78%Z)) (ltac:(oD' 0xa6b78%Z)) (tp + off) Ct.
zstep (ltac:(oF' 0xa6b7c%Z)) (ltac:(oD' 0xa6b7c%Z)).
stepret (ltac:(oF' 0xa6b80%Z)) (ltac:(oD' 0xa6b80%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
#[using="Type"] Lemma art_tsd_get_fn : ltac2:(TCodec.tc2 tcn__JatLeaf "SK&6y5'Q7yR0%211%5241'1y8%611%311p061'5'4&?r8(Q5+1(2%33A21%6251r5%93A21&=r6%211r:+4%<3J1:%?231&Q6%12K7%C3K31&D+TP0r7%3221&E&C%12H5&H+2+R0%3221%7251'3z%>21Q0+T0%<2Q21%5231r9+QP0%?221%A21;%F294%C25=%<221&:&Br@+QWY[0u1%554321Q>rA+QWY[4u4r=%:594321rB&Ir?+RH%3221u8%A5@6218rCr>&F+8%2219%Q;241%H5G618?'<&@vMrE+_]`<%R83RD1R6/01RDrD%756521?&A+:%R>3RL1R<%R12RKB%43:21+;%RB3S01R@%R52ROL%83421%A5@1Q0;I%C3Q;;1p0E1p0M1p0Q51p0Q;1p0QB1p0QF1p0QN1p0QL1p0R31p0R<1p0RA1p0RI1p0RM1pQJS81pRJS91pQNS:1pRHS;1pR4SC1pR8S>1p@S?1pR6SE1").
Proof.
intros regs M rom raw tp key tsd ctx H1 Hret H4 Htp Htp' Hkey Htsd Htsd' Hctx Ci Ck Ctsd Cctx.
zstep (ltac:(oF' 0x7b60c%Z)) (ltac:(oD' 0x7b60c%Z)). zstep (ltac:(oF' 0x7b610%Z)) (ltac:(oD' 0x7b610%Z)).
zlbu (ltac:(oF' 0x7b614%Z)) (ltac:(oD' 0x7b614%Z)) 0x13a560 Ci.
zbft (ltac:(oF' 0x7b618%Z)) (ltac:(oD' 0x7b618%Z)).
zlw (ltac:(oF' 0x7b61c%Z)) (ltac:(oD' 0x7b61c%Z)) 0x13a564 Ck.
stepn (ltac:(oF' 0x7b620%Z)) (ltac:(oD' 0x7b620%Z)).
zstep (ltac:(oF' 0x1275d8%Z)) (ltac:(oD' 0x1275d8%Z)).
zld (ltac:(oF' 0x1275dc%Z)) (ltac:(oD' 0x1275dc%Z)) (tp - 88) Ctsd.
zstep (ltac:(oF' 0x1275e0%Z)) (ltac:(oD' 0x1275e0%Z)).
stepn (ltac:(oF' 0x1275e4%Z)) (ltac:(oD' 0x1275e4%Z)). rwH. rewrite (art_zb_srli_exact _ 29 (8 * key)) by lia.
zstep (ltac:(oF' 0x1275e8%Z)) (ltac:(oD' 0x1275e8%Z)).
zld (ltac:(oF' 0x1275ec%Z)) (ltac:(oD' 0x1275ec%Z)) (tsd + 8 * key) Cctx.
stepret (ltac:(oF' 0x1275f0%Z)) (ltac:(oD' 0x1275f0%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
Definition art_tsd (M : word -> option byte) (tp key tsd ctx t : Z) : Prop :=
cellA M 0x13a560 1 1 /\ cellA M 0x13a564 4 key /\ cellA M (tp - 88) 8 tsd /\ cellA M (tsd + 8 * key) 8 ctx /\ cellA M (ctx + 152) 8 t
/\ 4096 <= tp /\ tp + 4096 < 2 ^ 64 /\ 0 <= key < 128 /\ 0 <= tsd /\ tsd + 1024 < 2 ^ 64 /\ 4096 <= ctx /\ ctx + 4096 < 2 ^ 64 /\ 0 <= t < 2 ^ 64.
#[using="Type"] Lemma art_tsd_Wn : ltac2:(TCodec.tc2 tcn__JatLeaf "R9'0'Q7yR0%211'1y8%511%311p051'5&Dzr7%3221&E&Cr8&Gr:%211%5241&H+2+R0%3221%;251&9r9r;%<11+QWY[0+8%645321r<%A11&I+RH%22E1%<4D417r=%G11&F%12;J%L2O1%B4@41=r>%M11+TH%Q12Q41%G4@31B&>%166GQ1HQ3Q7&8r@r?%3421:@%661GLQ6MQ8p061p091p0?1p0F1p0M1p0Q51p0QB1pRDQG1pQJQH1pRJQI1pQNQJ1pRHQK1pRLQL1pQFQM1p@QO1pR0R81").
Proof.
intros n M a v tp key tsd ctx t Ha Hn A1 A2 A3 A4 (C1 & C2 & C3 & C4 & C5 & R).
unfold art_tsd. unfold apart in *.
repeat split; try lia; (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia| assumption]).
Qed.
#[using="Type"] Lemma art_cur_thread_fn : ltac2:(TCodec.tc2 tcn__JatLeaf "T3&6y5'Q7yR0%211%5241'1y8%611%311p061'5'4&?r:(Q5+1(2%33A21%6251r7%93A21&=r8%211r<+2%<3J1:%?231&Q6%12K7%C3K31r=+4%C3Q11A%F231%H3Q016&D+@%221I&Er;&H+R0%22B1%5241&;&Br?&I%12I<%54431=&>r@r9%362N>Q91Q0&9r>%921D+QWY[0+8%543G21%=2>H+RH%?271%943K15%A2=L&C&F%129<%32Q61%?45Q11;rA%H21Q3+TH%82Q;1%D43Q61@'<&@vMrF+`[l<%R33R?1R1/01R?rErD%8576321&ArC%239R71rB%QN2RH1%533R11+:%R?3RM1R=%R22RLQO%93421+;%RC3S11RA%R62S0QC%=3421&8u8%QF2=Q;&Q8%12S6A%544F31%M5L7C1F%O3QMF1p0Q11p0Q71p0Q>1p0QC1p0QJ1p0QO1p0R61p0R=1p0RA1p0RG1p0RO1p0S31pRDS>1pQJS?1pRJS@1pQNSA1pRHSB1pR:SC1pR4SK1pR8SF1p@SG1pR6SM1").
Proof.
intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD A1 A2 A3 A4.
pose proof (art_tsd_Wn 8 M (sp - 8) (U raw) tp key tsd ctx t ltac:(lia) ltac:(lia)
ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) ltac:(unfold apart in *; cbn; lia) TSD)
as (C1 & C2 & C3 & C4 & C5 & R).
zstep (ltac:(oF' 0x82f8c%Z)) (ltac:(oD' 0x82f8c%Z)).
zsd (ltac:(oF' 0x82f90%Z)) (ltac:(oD' 0x82f90%Z)) (sp - 8) (U raw) ltac:(rewok W).
stepn (ltac:(oF' 0x82f94%Z)) (ltac:(oD' 0x82f94%Z)).
zcall (art_tsd_get_fn _ _ _ _ tp key tsd ctx).
zbft (ltac:(oF' 0x82f98%Z)) (ltac:(oD' 0x82f98%Z)).
zld (ltac:(oF' 0x82f9c%Z)) (ltac:(oD' 0x82f9c%Z)) (ctx + 152) C5.
assert (Cra : cellA (Wn 8 M (sp - 8) (U raw)) (sp - 8) 8 (U raw)) by (apply cell_Wn_hit; lia).
zld (ltac:(oF' 0x82fa0%Z)) (ltac:(oD' 0x82fa0%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x82fa4%Z)) (ltac:(oD' 0x82fa4%Z)).
stepret (ltac:(oF' 0x82fa8%Z)) (ltac:(oD' 0x82fa8%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
#[using="Type"] Lemma art_thread_stats_fn : ltac2:(TCodec.tc2 tcn__JatLeaf "T<&6y5'Q7yR0%211%5241'1y8%611%311p061'5'4&?r:(Q5+1(2%33A21%6251r7%93A21&=r8%211r<+2%<3J1:%?231&Q6%12K7%C3K31r=+4%C3Q11A%F231%H3Q016&D+Q0%221I&Er;&H+R0%22B1%5241&;&Br?&I%12I<%54431=&>r@r9%362N>Q91Q0%C2Q82&9%92:D+QWY[0+8%443G21%=29H+RH%?2@1%843K15rA%B21M&Cr>&F%12;G%4231%@46Q31=rB%J21Q5+TH%9281%E43Q81B'<&@vMrG+`XZH%R53RA1R3/01RArFrE%8576321&ArD%239R91rC%R02RJ1%533R31+:%RA3RO1R?+Rg@%N2M1%R62S01%;3641+;%RG3S51RE%R:2S4QB%?3421&8u8%QJ2?Q?&Q8%12S:C%544H31+H%QO2D1+`X[4%948421%Q35Q2;I1L%Q53R5L1p0Q71p0Q=1p0QF1p0QK1p0R11p0R31p0R81p0R?1p0RF1p0RJ1p0S01p0S81p0S<1pRDSG1pQJSH1pRJSI1pQNSJ1pRHSK1pR:SL1pR4T41pR8SO1p@T01pR6T61").
Proof.
intros regs M rom raw sp tp key tsd ctx t H1 Hret H2 H4 Hsp Hsp' W TSD Ht A1 A2 A3 A4.
pose proof TSD as (_ & _ & _ & _ & _ & R).
zstep (ltac:(oF' 0x82158%Z)) (ltac:(oD' 0x82158%Z)).
zsd (ltac:(oF' 0x8215c%Z)) (ltac:(oD' 0x8215c%Z)) (sp - 8) (U raw) ltac:(rewok W).
stepn (ltac:(oF' 0x82160%Z)) (ltac:(oD' 0x82160%Z)).
zcall (art_cur_thread_fn _ _ _ _ (sp - 16) tp key tsd ctx t).
{ apply art_tsd_Wn; unfold apart in *; cbn; try lia. exact TSD. }
zbft (ltac:(oF' 0x82164%Z)) (ltac:(oD' 0x82164%Z)).
zstep (ltac:(oF' 0x82168%Z)) (ltac:(oD' 0x82168%Z)). zstep (ltac:(oF' 0x8216c%Z)) (ltac:(oD' 0x8216c%Z)).
assert (Cra : cellA (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16 - 8) (U (Z_to_bv 64 0x82164 : word))) (sp - 8) 8 (U raw)).
{ apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply cell_Wn_hit; lia. }
zld (ltac:(oF' 0x82170%Z)) (ltac:(oD' 0x82170%Z)) (sp - 8) Cra. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x82174%Z)) (ltac:(oD' 0x82174%Z)).
stepret (ltac:(oF' 0x82178%Z)) (ltac:(oD' 0x82178%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
#[using="Type"] Lemma art_stack_top_fn : ltac2:(TCodec.tc2 tcn__JatLeaf "S8&6y5'Q7yR0%211%5241'1y8%611%311p061'5'4&?r7(Q5+1(2%33A21%6251r4%93A21&=r5%211r9+:%<3J1:%?231&Q6%12K7%C3K31&D+TP0r6%3221&E&C%12H5&H+2+R0%3221%7251'3z%>21<%;2=Q1%4221r8%>218&:&Br=r:+Q8%C221u1%756521=r>r;+8%I221u8%=5<521:r?r<+@%O221%B5A416?'<&@vMrA+`\Z@%QL3R81QJ/01R8r@%756521=&A%QC2R=>%238QF1+;%R43RB1R2%53314%>5=1J8D%@3Q281p0B1p0H1p0O1p0Q81p0Q;1p0QA1p0QJ1p0QO1p0R71p0R;1pQHRF1pRFRG1pRDRH1pR4S01pR8RK1p@RL1pR6S21").
Proof.
intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
zlb (ltac:(oF' 0x83150%Z)) (ltac:(oD' 0x83150%Z)) (t + 40) C40.
stepfence (ltac:(oF' 0x83154%Z)) (ltac:(oD' 0x83154%Z)).
zbtk (ltac:(oF' 0x83158%Z)) (ltac:(oD' 0x83158%Z)).
zld (ltac:(oF' 0x83190%Z)) (ltac:(oD' 0x83190%Z)) (t + 8) C8.
zld (ltac:(oF' 0x83194%Z)) (ltac:(oD' 0x83194%Z)) (t + 16) C16.
zstep (ltac:(oF' 0x83198%Z)) (ltac:(oD' 0x83198%Z)). zstep (ltac:(oF' 0x8319c%Z)) (ltac:(oD' 0x8319c%Z)).
stepn (ltac:(oF' 0x831a0%Z)) (ltac:(oD' 0x831a0%Z)). rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_l by lia | rewrite art_land_full_r by lia].
stepret (ltac:(oF' 0x831a4%Z)) (ltac:(oD' 0x831a4%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
#[using="Type"] Lemma art_stack_bottom_fn : ltac2:(TCodec.tc2 tcn__JatLeaf "S;&6y5'Q7yR0%211%5241'1y8%611%311p061'5'4&?r7(Q5+1(2%33A21%6251r4%93A21&=r5%211r9+:%<3J1:%?231&Q6%12K7%C3K31&D+TP0r6%3221&E&C%12H5&H+2+R0%3221%7251'3z%>21<%;2=Q1%4221r8%>218&:&Br=r:+Q8%C221u1%756521=r>r;+8%I221u8%=5<521:r?r<+@%O221%B5A416?'<&@vMrA+`\]8%QL3R81QJ/01R8r@%756521=&A%QC2R=D%238QF1+;%R43RB1R2&I%12Q;R5%QI2RC1%83641%A5@1M;G%C3Q5;1p0E1p0K1p0Q21p0Q;1p0Q>1p0QD1p0QM1p0R21p0R:1p0R>1pQHRI1pRFRJ1pRDRK1pR4S31pR8RN1p@RO1pR6S51").
Proof.
intros regs M rom raw t top bot H1 Hret H10 Ht Ht' Hbt Htop C40 C8 C16.
zlb (ltac:(oF' 0x831a8%Z)) (ltac:(oD' 0x831a8%Z)) (t + 40) C40.
stepfence (ltac:(oF' 0x831ac%Z)) (ltac:(oD' 0x831ac%Z)).
zbtk (ltac:(oF' 0x831b0%Z)) (ltac:(oD' 0x831b0%Z)).
zld (ltac:(oF' 0x831e8%Z)) (ltac:(oD' 0x831e8%Z)) (t + 8) C8.
zld (ltac:(oF' 0x831ec%Z)) (ltac:(oD' 0x831ec%Z)) (t + 16) C16.
zstep (ltac:(oF' 0x831f0%Z)) (ltac:(oD' 0x831f0%Z)). zstep (ltac:(oF' 0x831f4%Z)) (ltac:(oD' 0x831f4%Z)).
stepn (ltac:(oF' 0x831f8%Z)) (ltac:(oD' 0x831f8%Z)). rwH. rewrite art_zb_and by lia. first [rewrite art_land_full_r by lia | rewrite art_land_full_l by lia].
stepret (ltac:(oF' 0x831fc%Z)) (ltac:(oD' 0x831fc%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
End FPX.
