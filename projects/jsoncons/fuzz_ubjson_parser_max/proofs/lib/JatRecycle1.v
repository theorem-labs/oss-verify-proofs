(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac JatLeaf JatAllocG JatPoison JatSecAlloc ArtRuns ArtRunsMem JatFp JatCellEx JatImgCell JatSecRSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatRecycle1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle1.FPX1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatRecycle1.FPX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3le"; "3lt"]; ["4Forall"; "4nth"; "5Z"; "0HI"; "6bvmap"; "0M"; "0M'"; "7apart"; "7cell"; "7wr"; "8art_madvise_args"; "8art_shhi"; "8art_shlo"; "9msteps"; ":ret_ok"; ";art_agree"]; ["<SB"; "<art_layout"; "<kHighMemBeg"; "<kHighMemEnd"; ">art_blk_ok"; ">art_flush_mem"; "?art_gbb_mem"; "=art_flush_beg"; "=art_flush_end"; "=art_flush_frame"; "=art_gbb_scan"; "=art_pg_dn"; "@getr"; "@mkst"; "@regupd"; "Amem_grows"]; ["Bloaded_segments"; "CIn"; "Dadd"; "Ddiv"; "Dle"; "Dlt"; "Dmodulo"; "Dmul"; "Dof_nat"; "Dpow"; "Dsub"; "0X"; "0a"; "0beg"; "0ch"; "0chs"]; ["0cur"; "0en"; "0fx"; "0h"; "0j"; "0m"; "0mb"; "0mbeg"; "0ms"; "0msz"; "0n"; "0near"; "0parr"; "0r"; "0raw"; "0regs"]; ["0regs'"; "0rom"; "0sa"; "0sb"; "0sp"; "EBV"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0v"; "0x"; "0x18"; "0x8"; "0x9"]]).
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
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_m2s_lo_fn := (ltac2:(TCodec.tc2 tcn__JatRecycle1 "RI&Dy5'RGyR0%211%5241'5y8%611%311p061'B':&Q<r5(RE+1(8%33A21%6251r2%93A21&Nr3%211r7+:%<3J1:%?231&RF%12K7%C3K31'9&QDzr4%3221&QJ&Q0%221G%7251%9251&Q1r8%211'M&Q@&Q=vR2r:+_SPD%Q43Q@1Q2/01Q@r9%756521;&Q>&QB+QoooPP0&QCr6+8%3221%6251%Q22QL1%93?Q51+;%QC3R11QA%Q62R0:%=3421+<%QG3R51QE+QoonooO%Q;2R51%B3531+=%QL3R:1QJ%E3314%N5M1QDHQ2%Q13Q0H1p0Q31p0Q71p0QB1p0QJ1p0QN1pSJR91pTNRA1pU4R<1pQ<R=1pU0RC1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_m2s_lo_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_m2s_lo_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_m2s_lo_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_m2s_lo_fn) 3%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_m2s_lo_fn) 4%nat 0%nat).
Lemma art_m2s_lo_fn : ltac:(sec_stmt2 constr:(SEC_T_art_m2s_lo_fn) 5%nat 0%nat).
Proof using Type regs M rom raw a.
intros H1 Hret H10 Ha L.
unfold SB in *.
destruct L as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & _).
stepn (ltac:(oF' 0x78c14%Z)) (ltac:(oD' 0x78c14%Z)).
zld (ltac:(oF' 0x78c18%Z)) (ltac:(oD' 0x78c18%Z)) 0x132638 L1.
zld (ltac:(oF' 0x78c1c%Z)) (ltac:(oD' 0x78c1c%Z)) 0x13acf8 L2.
zstep (ltac:(oF' 0x78c20%Z)) (ltac:(oD' 0x78c20%Z)). zstep (ltac:(oF' 0x78c24%Z)) (ltac:(oD' 0x78c24%Z)). zstep (ltac:(oF' 0x78c28%Z)) (ltac:(oD' 0x78c28%Z)).
stepn (ltac:(oF' 0x78c2c%Z)) (ltac:(oD' 0x78c2c%Z)). rwH. zclosed 2147450879.
zbtk (ltac:(oF' 0x78c30%Z)) (ltac:(oD' 0x78c30%Z)).
stepn (ltac:(oF' 0x78c74%Z)) (ltac:(oD' 0x78c74%Z)). rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
zstep (ltac:(oF' 0x78c78%Z)) (ltac:(oD' 0x78c78%Z)).
stepret (ltac:(oF' 0x78c7c%Z)) (ltac:(oD' 0x78c7c%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_m2s_hi_fn := (ltac2:(TCodec.tc2 tcn__JatRecycle1 "S@&Dy5'RGyR0%211%5241'5y8%611%311p061'B':&Q<r5(RE+1(8%33A21%6251r2%93A21&Nr3%211r7+:%<3J1:%?231&RF%12K7%C3K31'9&QD&Q2r4%3221&Q3%5231%7231&Q1r8%211'M&Q@&Q=vR2r:+_SPD%Q23Q>1Q0/01Q>r9%756521;&Q>+5%Q83QF1Q6+SooooooooO%L2QF1%53;31&QB+QoooPP0&QCr6+8%3221%6251%Q52QO1%>39Q81+;%QF3R41QD%Q92R3:%B3421+<%QJ3R81QH+QoonooO%Q>2R81%G3531+=%QO3R=1QMz%QC2R=1%L3531+>%R43RB1R2+_oooooooO%QH2RB1%Q13531+?%R93RG1R7+_oooooooooooO%QM2RG1%Q63531+@%R>3RL1R<%Q9331>+A%RA3RO1R?+`PQoonooO%R52RO1%Q>3531%QG5QF1R;QAQK%QJ3QIQA1p0QL1p0R01p0R91p0RA1p0RE1pSJS01pTNS81pU4S31pQ<S41pU0S:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_m2s_hi_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_m2s_hi_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_m2s_hi_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_m2s_hi_fn) 3%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_m2s_hi_fn) 4%nat 0%nat).
Lemma art_m2s_hi_fn : ltac:(sec_stmt2 constr:(SEC_T_art_m2s_hi_fn) 5%nat 0%nat).
Proof using Type regs M rom raw a.
intros H1 Hret H10 Ha L.
unfold SB, kHighMemBeg, kHighMemEnd in *.
destruct L as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & _).
stepn (ltac:(oF' 0x78c14%Z)) (ltac:(oD' 0x78c14%Z)).
zld (ltac:(oF' 0x78c18%Z)) (ltac:(oD' 0x78c18%Z)) 0x132638 L1.
zld (ltac:(oF' 0x78c1c%Z)) (ltac:(oD' 0x78c1c%Z)) 0x13acf8 L2.
zstep (ltac:(oF' 0x78c20%Z)) (ltac:(oD' 0x78c20%Z)). zstep (ltac:(oF' 0x78c24%Z)) (ltac:(oD' 0x78c24%Z)). zstep (ltac:(oF' 0x78c28%Z)) (ltac:(oD' 0x78c28%Z)).
stepn (ltac:(oF' 0x78c2c%Z)) (ltac:(oD' 0x78c2c%Z)). rwH. zclosed 2147450879.
zbft (ltac:(oF' 0x78c30%Z)) (ltac:(oD' 0x78c30%Z)).
stepn (ltac:(oF' 0x78c34%Z)) (ltac:(oD' 0x78c34%Z)).
zld (ltac:(oF' 0x78c38%Z)) (ltac:(oD' 0x78c38%Z)) 0x132640 L3.
stepn (ltac:(oF' 0x78c3c%Z)) (ltac:(oD' 0x78c3c%Z)).
zld (ltac:(oF' 0x78c40%Z)) (ltac:(oD' 0x78c40%Z)) 0x132648 L5.
zld (ltac:(oF' 0x78c44%Z)) (ltac:(oD' 0x78c44%Z)) 0x13b9e8 L4.
zld (ltac:(oF' 0x78c48%Z)) (ltac:(oD' 0x78c48%Z)) 0x13b9f0 L6.
zstep (ltac:(oF' 0x78c4c%Z)) (ltac:(oD' 0x78c4c%Z)).
zbtk (ltac:(oF' 0x78c50%Z)) (ltac:(oD' 0x78c50%Z)).
stepn (ltac:(oF' 0x78c58%Z)) (ltac:(oD' 0x78c58%Z)).
zld (ltac:(oF' 0x78c5c%Z)) (ltac:(oD' 0x78c5c%Z)) 0x132650 L7.
zld (ltac:(oF' 0x78c60%Z)) (ltac:(oD' 0x78c60%Z)) 0x13b9e0 L8.
stepn (ltac:(oF' 0x78c64%Z)) (ltac:(oD' 0x78c64%Z)). rwH. zclosed 17592186044415.
zstep (ltac:(oF' 0x78c68%Z)) (ltac:(oD' 0x78c68%Z)).
zbft (ltac:(oF' 0x78c6c%Z)) (ltac:(oD' 0x78c6c%Z)).
zbft (ltac:(oF' 0x78c70%Z)) (ltac:(oD' 0x78c70%Z)).
stepn (ltac:(oF' 0x78c74%Z)) (ltac:(oD' 0x78c74%Z)). rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
zstep (ltac:(oF' 0x78c78%Z)) (ltac:(oD' 0x78c78%Z)).
stepret (ltac:(oF' 0x78c7c%Z)) (ltac:(oD' 0x78c7c%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
End FPX.
Definition art_pg_dn (x : Z) : Z := x - x mod 4096.
Definition art_flush_beg (mb : Z) : Z := art_pg_dn (SB + mb / 8 + 4095).
Definition art_flush_end (mb ms : Z) : Z := art_pg_dn (SB + (mb + ms) / 8).
Definition art_flush_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)).
Section FPX1. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_layout_flush_frame : ltac2:(TCodec.tc2 tcn__JatRecycle1 "Q9'RGyR0%211'5y8%511%311p051'B&Dy5%2219&QD&QB+VbTP0+Q0%3221r3%6221&QEr4&QI+2+R0%3221%6251&Q1r6%211&Q9r7r5%34251<%711p061p0:1p0B1pU0J1pTNQ41pU:O1pQ<Q11").
Proof.
intros M sp raw regs Hsp Hsp' L. unfold art_flush_frame.
repeat (apply art_layout_Wn; [lia|cbn; lia|unfold apart; cbn; lia|unfold apart; cbn; lia|]). exact L.
Qed.
#[using="Type"] Lemma art_flush_frame_cells : ltac2:(TCodec.tc2 tcn__JatRecycle1 "R6'RGyR0%211'5y8%511%311p051'B&Dy5%2219&QD+Q0r3%3221&QEr4&QI+2+R0%3221%6251&Q9r6r5%34219<'9&H&Q@r1&QJ+8%2291u8&RH%12Q3;%9587431+@%82?1&Q<(RE(8%23Q1;1%42K1%:2Q<1%B5A@7<1+H%A2H1+9%93Q818%;2Q21%A2QC1%I5HG5C1%G2NQ9+B%?3Q>1>%A2Q81%G2QI1%O5NM5I1%Q1271%Q22?1%Q32I1tSHQHQ51p0Q:1p0QB1pU0QG1pTNR11pU:QL1pQ<QN1").
Proof. intros M sp raw regs Hsp Hsp'. unfold art_flush_frame. repeat split; zcell. Qed.
#[using="Type"] Lemma art_flush_frame_other : ltac2:(TCodec.tc2 tcn__JatRecycle1 "QN'RGyR0%211'5y8%511%311p051'B&Dy5%2219'3&QD+Q0r6%3221&QEr7&QI+2+R0%3221%6251zr5%=221&QB&QH%114%32?1%>219&G&QJr:%221E%81E%542GC1&H&Q@r<r8%45321HK&Q9r=r;%34261<r9%:59217Np071p0=1p0D1p0J1p0N1p0Q61pUDQ?1pTFQ<1pSJQA1pU0Q?1pTNQI1pU:QD1pQ<QF1").
Proof. intros M sp raw regs a n v Hsp Hsp' Ha Hn A C. unfold art_flush_frame. unfold apart in A. repeat (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). exact C. Qed.
#[using="Type"] Lemma art_flush_frame_wr : ltac2:(TCodec.tc2 tcn__JatRecycle1 "Q0'RGyR0%211'5y8%511%311p051'B&Dy5%2219&I&Q@r6r2r1%544321&Q9r7r5r4%443821r3%<4;219p081pTFB1pSJC1pU0A1pTNK1pU:F1pQ<H1").
Proof. intros. unfold art_flush_frame. repeat apply wr_Wn. assumption. Qed.
Section SE.
Local Abbreviation SEC_T_art_flush_a_lo := (ltac2:(TCodec.tc2 tcn__JatRecycle1 "UJ&Dy5'RGyR0%211%5241'5y8%611%311p061'B':&Q<r7(RE+1(8%33A21%6251r4%93A21r8+2%93G17%<231&RF%12H7%@3H31r9+:%@3N1>%C231%E3M16r:+;%E3Q31C%H231%J3Q21;&QD&QB+VbTP0+Q0%3221%521N&QE&QI+R0%22I1%42K1&I&Q@r<&QJ%12I<%54431=z%B21Q3'9%D23I%D2JO&Q0%921Q>%H231%6251&Q1r?%211';'M&Q=vR2rB+_Rn8%QK3R71QI/01R7rAr@%8576321r1+bai4%R23R>1R0/01R>&Q9r>%2491C=%@5?7419%B3Q491%R;29QI&QCr=+8%3221%QE2Q01%R42RK1%RC3RK71%RC2AQL%QI27Q=%9217%QK2Q61%R:2S11%RI3S151%RI2GRD%RK3S31Q5%RK2IR@%R?2S6E%RN3S621%S91S:&QA(0+3%S03S>1RN+4%S23S@1S0%S33SAGS1+9%S53SC1S3+B%S73SE1S5+C%S93SG1S7+D%S;3SI1S9+E%S=3SK1S;+F%S?3SM1S=+G%SA3SO1S?+H%SC3T11SA+I%SE3T31SC+J%SG3T51SE+K%SI3T71SG(4%11O%N3Q031%O3Q161%Q03Q291%Q13Q3<1%Q23Q4?1%Q33Q5B1%Q43Q6E1%Q53Q7H1%Q63Q8K1%Q73Q9N1%Q83Q:Q11%Q93Q;Q41%Q:3Q<Q61%Q;3Q=Q91%Q=3Q>R:1r3r2%T?221rD%TA213%TC3TK31p071pTLQF1%S82QH1%S92QL1%S:2QO1%S;2R61%S<2R?1qU2U21%S42U31p0S61p0S:1p0SB1p0SE1p0SL1p0T21p0T91p0T?1p0TE1p0TM1pTBU81pT>U91pU:U:1pTNUB1pU4U=1pQ<U>1pU0UD1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_lo) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_lo) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_lo) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_lo) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_lo) 4%nat 0%nat).
Variable mb : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_lo) 5%nat 0%nat).
Variable ms : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_lo) 6%nat 0%nat).
Lemma art_flush_a_lo : ltac:(sec_stmt2 constr:(SEC_T_art_flush_a_lo) 7%nat 0%nat).
Proof using Type regs M rom raw sp mb ms.
intros H1 H2 H10 H11 Hsp Hsp' W Hms Hrng L.
pose proof (eq_refl : SB = 2147450880) as ESB. pose proof (eq_refl : kHighMemBeg = 0x10007fff8000) as EHB. pose proof (eq_refl : kHighMemEnd = 0x7fffffffffff) as EHE.
eexists. split.
{
zstep (ltac:(oF' 0x78bc8%Z)) (ltac:(oD' 0x78bc8%Z)).
zsd (ltac:(oF' 0x78bcc%Z)) (ltac:(oD' 0x78bcc%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x78bd0%Z)) (ltac:(oD' 0x78bd0%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x78bd4%Z)) (ltac:(oD' 0x78bd4%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x78bd8%Z)) (ltac:(oD' 0x78bd8%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zstep (ltac:(oF' 0x78bdc%Z)) (ltac:(oD' 0x78bdc%Z)). zstep (ltac:(oF' 0x78be0%Z)) (ltac:(oD' 0x78be0%Z)).
stepn (ltac:(oF' 0x78be4%Z)) (ltac:(oD' 0x78be4%Z)).
change (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) with (art_flush_frame M sp raw regs).
pose proof (art_layout_flush_frame M sp raw regs Hsp Hsp' L) as L'.
zcall (art_m2s_lo_fn _ _ _ (0x78be8 : word) mb).
zstep (ltac:(oF' 0x78be8%Z)) (ltac:(oD' 0x78be8%Z)). zstep (ltac:(oF' 0x78bec%Z)) (ltac:(oD' 0x78bec%Z)).
stepn (ltac:(oF' 0x78bf0%Z)) (ltac:(oD' 0x78bf0%Z)).
zcall (art_m2s_lo_fn _ _ _ (0x78bf4 : word) (ms + mb)).
zstep (ltac:(oF' 0x78bf4%Z)) (ltac:(oD' 0x78bf4%Z)). zstep (ltac:(oF' 0x78bf8%Z)) (ltac:(oD' 0x78bf8%Z)).
destruct (art_flush_frame_cells M sp raw regs ltac:(lia) Hsp') as (F1 & F8 & F9 & F18).
zld (ltac:(oF' 0x78bfc%Z)) (ltac:(oD' 0x78bfc%Z)) (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x78c00%Z)) (ltac:(oD' 0x78c00%Z)) (sp - 16) F8. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x78c04%Z)) (ltac:(oD' 0x78c04%Z)) (sp - 24) F9. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x78c08%Z)) (ltac:(oD' 0x78c08%Z)) (sp - 32) F18. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x78c0c%Z)) (ltac:(oD' 0x78c0c%Z)).
stepn (ltac:(oF' 0x78c10%Z)) (ltac:(oD' 0x78c10%Z)).
apply mst_refl. }
replace (mb + ms) with (ms + mb) by lia.
split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | assumption]|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_flush_a_hi := (ltac2:(TCodec.tc2 tcn__JatRecycle1 "UK&Dy5'RGyR0%211%5241'5y8%611%311p061'B':&Q<r7(RE+1(8%33A21%6251r4%93A21r8+2%93G17%<231&RF%12H7%@3H31r9+:%@3N1>%C231%E3M16r:+;%E3Q31C%H231%J3Q21;&QD&QB+VbTP0+Q0%3221%521N&QE&QI+R0%22I1%42K1&I&Q@r<&QJ%12I<%54431=z%B21Q3'9&Q2%E21J%E2KQ0&Q3%H221%6241&Q1r?%211';'M&Q=vR2rB+_Rn8%QK3R71QI/01R7rAr@%8576321r1+bai4%R23R>1R0/01R>&Q9r>%2491C=%@5?7419%B3Q491%R;29QI&Q0&QCr=+8%3221%QF251%R52RL1%RD3RL81%RD2BQM%QJ27Q>%9217%QL2;1%R;2S21%RJ3S251%RJ2HRE%RL3S41Q6%RL2JRA%R@2S7F%RO3S721%S:1S;&QA(0+3%S13S?1RO+4%S33SA1S1%S43SBGS2+9%S63SD1S4+B%S83SF1S6+C%S:3SH1S8+D%S<3SJ1S:+E%S>3SL1S<+F%S@3SN1S>+G%SB3T01S@+H%SD3T21SB+I%SF3T41SD+J%SH3T61SF+K%SJ3T81SH(4%11O%N3Q031%O3Q161%Q03Q291%Q13Q3<1%Q23Q4?1%Q33Q5B1%Q43Q6E1%Q53Q7H1%Q63Q8K1%Q73Q9N1%Q83Q:Q11%Q93Q;Q41%Q:3Q<Q61%Q;3Q=Q91%Q=3Q>R;1r3r2%T@221rD%TB213%TD3TL31p071pTLQF1%S92QH1%S:2QL1%S;2QO1%S<2R61%S=2R@1qU2U31%S52U41p0S71p0S;1p0SC1p0SF1p0SM1p0T31p0T:1p0T@1p0TF1p0TN1pTBU91pT>U:1pU:U;1pTNUC1pU4U>1pQ<U?1pU0UE1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_hi) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_hi) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_hi) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_hi) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_hi) 4%nat 0%nat).
Variable mb : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_hi) 5%nat 0%nat).
Variable ms : ltac:(sec_ty2 constr:(SEC_T_art_flush_a_hi) 6%nat 0%nat).
Lemma art_flush_a_hi : ltac:(sec_stmt2 constr:(SEC_T_art_flush_a_hi) 7%nat 0%nat).
Proof using Type regs M rom raw sp mb ms.
intros H1 H2 H10 H11 Hsp Hsp' W Hms Hrng L.
pose proof (eq_refl : SB = 2147450880) as ESB. pose proof (eq_refl : kHighMemBeg = 0x10007fff8000) as EHB. pose proof (eq_refl : kHighMemEnd = 0x7fffffffffff) as EHE.
eexists. split.
{
zstep (ltac:(oF' 0x78bc8%Z)) (ltac:(oD' 0x78bc8%Z)).
zsd (ltac:(oF' 0x78bcc%Z)) (ltac:(oD' 0x78bcc%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x78bd0%Z)) (ltac:(oD' 0x78bd0%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x78bd4%Z)) (ltac:(oD' 0x78bd4%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x78bd8%Z)) (ltac:(oD' 0x78bd8%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zstep (ltac:(oF' 0x78bdc%Z)) (ltac:(oD' 0x78bdc%Z)). zstep (ltac:(oF' 0x78be0%Z)) (ltac:(oD' 0x78be0%Z)).
stepn (ltac:(oF' 0x78be4%Z)) (ltac:(oD' 0x78be4%Z)).
change (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) with (art_flush_frame M sp raw regs).
pose proof (art_layout_flush_frame M sp raw regs Hsp Hsp' L) as L'.
zcall (art_m2s_hi_fn _ _ _ (0x78be8 : word) mb).
zstep (ltac:(oF' 0x78be8%Z)) (ltac:(oD' 0x78be8%Z)). zstep (ltac:(oF' 0x78bec%Z)) (ltac:(oD' 0x78bec%Z)).
stepn (ltac:(oF' 0x78bf0%Z)) (ltac:(oD' 0x78bf0%Z)).
zcall (art_m2s_hi_fn _ _ _ (0x78bf4 : word) (ms + mb)).
zstep (ltac:(oF' 0x78bf4%Z)) (ltac:(oD' 0x78bf4%Z)). zstep (ltac:(oF' 0x78bf8%Z)) (ltac:(oD' 0x78bf8%Z)).
destruct (art_flush_frame_cells M sp raw regs ltac:(lia) Hsp') as (F1 & F8 & F9 & F18).
zld (ltac:(oF' 0x78bfc%Z)) (ltac:(oD' 0x78bfc%Z)) (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x78c00%Z)) (ltac:(oD' 0x78c00%Z)) (sp - 16) F8. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x78c04%Z)) (ltac:(oD' 0x78c04%Z)) (sp - 24) F9. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x78c08%Z)) (ltac:(oD' 0x78c08%Z)) (sp - 32) F18. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x78c0c%Z)) (ltac:(oD' 0x78c0c%Z)).
stepn (ltac:(oF' 0x78c10%Z)) (ltac:(oD' 0x78c10%Z)).
apply mst_refl. }
replace (mb + ms) with (ms + mb) by lia.
split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | assumption]|]). destruct Hr.
Qed.
End SE.
Definition art_rel_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte := art_flush_frame M sp raw regs.
Section SE.
Local Abbreviation SEC_T_art_rel_head := (ltac2:(TCodec.tc2 tcn__JatRecycle1 "UE&Dy5'RGyR0%211%5241'5y8%611%311p061'B':&Q<r7(RE+1(8%33A21%6251r4%93A21r8+2%93G17%<231&RF%12H7%@3H31r9+:%@3N1>%C231%E3M16r:+;%E3Q31C%H231%J3Q21;&QD&QB+VbTP0+Q0%3221%521N&QE&QI+R0%22I1%42K1&I&Q@r<&QJ%12I<%54431=z%B21L+TP0%C2I1%?21<'9%G26L%B2M?%3221&Hr@+QVY`Hu8+QiYm0%55C4321rA%75E134>';'M&Q=vR2rD+bai4%R03R<1QN/01R<rCrB%8576321r1+bakL%R73RC1R5/01RC&Q9%148GB<%?5>6318%A3Q881%R?28QM&Q;r?+SoO%QH221%411%R82RO1%RG3RO71%RG2@R0r>%911%R=2S41%RL3S441%RL2ERA%QE2Q8R0%RA2S81%S03S831%S;1S<&QA(0+3%S23S@1S0+4%S43SB1S2+C%S63SD1S4+D%S83SF1S6+E%S:3SH1S8+F%S<3SJ1S:+G%S>3SL1S<+H%S@3SN1S>+I%SB3T01S@+J%SD3T21SB+K%SF3T41SD(4%11J%I3K31%J3L61%K3M91%L3N<1%M3O?1%N3Q0B1%O3Q1E1%Q03Q2H1%Q13Q3K1%Q23Q4N1%Q33Q5Q11%Q53Q6QO1r3r2%T9221rF%T;213%T=3TE31p071pTLQ>1%RO2Q@1%S02QE1%S12QK1%S22R41qU2TK1%RH2TL1p0RJ1p0RM1p0S41p0S91p0S=1p0S@1p0SG1p0SM1p0T41p0T:1p0T@1p0TH1pU8U31pU6U41pU:U51pTNU=1pU4U81pQ<U91pU0U?1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_rel_head) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rel_head) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_rel_head) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_rel_head) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_rel_head) 4%nat 0%nat).
Variable sa : ltac:(sec_ty2 constr:(SEC_T_art_rel_head) 5%nat 0%nat).
Variable sb : ltac:(sec_ty2 constr:(SEC_T_art_rel_head) 6%nat 0%nat).
Lemma art_rel_head : ltac:(sec_stmt2 constr:(SEC_T_art_rel_head) 7%nat 0%nat).
Proof using Type regs M rom raw sp sa sb.
intros H1 H2 H10 H11 Hsp Hsp' W Hsa Hsa' Hsb Cpc Cpg.
eexists. split.
{
zstep (ltac:(oF' 0x94724%Z)) (ltac:(oD' 0x94724%Z)).
zsd (ltac:(oF' 0x94728%Z)) (ltac:(oD' 0x94728%Z)) (sp - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x9472c%Z)) (ltac:(oD' 0x9472c%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x94730%Z)) (ltac:(oD' 0x94730%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x94734%Z)) (ltac:(oD' 0x94734%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zstep (ltac:(oF' 0x94738%Z)) (ltac:(oD' 0x94738%Z)).
stepn (ltac:(oF' 0x9473c%Z)) (ltac:(oD' 0x9473c%Z)).
match goal with |- msteps _ (mkst _ _ ?Y _) _ => assert (Cpc2 : cellA Y 0x132618 8 0x1ca7a0) by zcell; assert (Cpg2 : cellA Y 0x1ca7a0 8 4096) by zcell end.
zld (ltac:(oF' 0x94740%Z)) (ltac:(oD' 0x94740%Z)) 0x132618 Cpc2.
zld (ltac:(oF' 0x94744%Z)) (ltac:(oD' 0x94744%Z)) 0x1ca7a0 Cpg2.
zstep (ltac:(oF' 0x94748%Z)) (ltac:(oD' 0x94748%Z)).
zbtk (ltac:(oF' 0x9474c%Z)) (ltac:(oD' 0x9474c%Z)).
zstep (ltac:(oF' 0x9475c%Z)) (ltac:(oD' 0x9475c%Z)).
stepn (ltac:(oF' 0x94760%Z)) (ltac:(oD' 0x94760%Z)). rwH. zclosed 0.
zbft (ltac:(oF' 0x94764%Z)) (ltac:(oD' 0x94764%Z)).
zstep (ltac:(oF' 0x94768%Z)) (ltac:(oD' 0x94768%Z)).
stepn (ltac:(oF' 0x9476c%Z)) (ltac:(oD' 0x9476c%Z)). rwH. zclosed 18446744073709547520.
zstep (ltac:(oF' 0x94770%Z)) (ltac:(oD' 0x94770%Z)).
replace (sa + 4096 + -1) with (sa + 4095) by lia.
stepn (ltac:(oF' 0x94774%Z)) (ltac:(oD' 0x94774%Z)). rwH. rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
stepn (ltac:(oF' 0x94778%Z)) (ltac:(oD' 0x94778%Z)). rwH. rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
unfold art_flush_frame. apply mst_refl. }
unfold art_pg_dn.
split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | assumption]|]). destruct Hr.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_rel_madv := (ltac2:(TCodec.tc2 tcn__JatRecycle1 "TI&Dy5'RGyR0%211%5241'5y8%611%311p061'B':&Q<r:(RE+2(8%33A21%6251&RF&QJr6+Q0%3221%52F1%>3F71r;+:%>3L1<%A231%;2L9%D3L21r<+;%D3Q21B%G231%I3Q116&QDr9%22A1&QE&QI+R0%22L1%42O1z%921Q1%72EQ2%82F5'9%=25H%2213&H&Q@rDrA+8%Q5221u8&RHrB%22QK1%:598541rE+@%Q=251r?%?5>4291rFrC+H%QC221%D5C41>6rG%QF2DQD%G5F21A9rH+QVYcH+1%K5J32E1'M&Q=vR2rJ+bakL%R73RC1R5/01RCrI%756521<&Q>%R<3RJ<R:%2381B%R92RJH%432R<1%R@3RNQ6R>%R<2RMJ%73321+9%RD3S21RB%R@2S1Q7%;3421%RA2Q?Q6%RC2S41%>33R51+<%RK3S91RI+4%RH2S91%C3531+=%S03S>1RN%F3314+A%S33SA1S1+W9%S02SA1%K3531+B%S83SF1S6%S42SER0%O3421+a\k<%S<3SH1S:/01SH%Q;5Q:41Q5Q@%Q=3R8Q51p0Q?1p0QD1p0QH1p0QN1p0R41p0R@1p0RA1p0RB1p0RF1p0RH1p0RJ1p0RM1p0S31p0S71p0S=1p0SD1pUHT41pULT51pUJT61pT4T71pSLT81pU:T91pTNTA1pU4T<1pQ<T=1pU0TC1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_rel_madv) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rel_madv) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_rel_madv) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_rel_madv) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_rel_madv) 4%nat 0%nat).
Variable beg : ltac:(sec_ty2 constr:(SEC_T_art_rel_madv) 5%nat 0%nat).
Variable en : ltac:(sec_ty2 constr:(SEC_T_art_rel_madv) 6%nat 0%nat).
Variable x8 : ltac:(sec_ty2 constr:(SEC_T_art_rel_madv) 7%nat 0%nat).
Variable x9 : ltac:(sec_ty2 constr:(SEC_T_art_rel_madv) 8%nat 0%nat).
Variable x18 : ltac:(sec_ty2 constr:(SEC_T_art_rel_madv) 9%nat 0%nat).
Lemma art_rel_madv : ltac:(sec_stmt2 constr:(SEC_T_art_rel_madv) 10%nat 0%nat).
Proof using Type regs M rom raw sp beg en x8 x9 x18.
intros H2 H10 H11 Hsp Hsp' Hb Hbe He Hx8 Hx9 Hx18 F1 F8 F9 F18 Cgot.
zbft (ltac:(oF' 0x9477c%Z)) (ltac:(oD' 0x9477c%Z)).
zstep (ltac:(oF' 0x94780%Z)) (ltac:(oD' 0x94780%Z)). zstep (ltac:(oF' 0x94784%Z)) (ltac:(oD' 0x94784%Z)).
zld (ltac:(oF' 0x94788%Z)) (ltac:(oD' 0x94788%Z)) (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9478c%Z)) (ltac:(oD' 0x9478c%Z)) (sp - 16) F8.
zld (ltac:(oF' 0x94790%Z)) (ltac:(oD' 0x94790%Z)) (sp - 24) F9.
zld (ltac:(oF' 0x94794%Z)) (ltac:(oD' 0x94794%Z)) (sp - 32) F18.
zstep (ltac:(oF' 0x94798%Z)) (ltac:(oD' 0x94798%Z)).
stepn (ltac:(oF' 0x9479c%Z)) (ltac:(oD' 0x9479c%Z)).
stepn (ltac:(oF' 0x8b34c%Z)) (ltac:(oD' 0x8b34c%Z)).
zld (ltac:(oF' 0x8b350%Z)) (ltac:(oD' 0x8b350%Z)) 0x132678 Cgot.
zbft (ltac:(oF' 0x8b354%Z)) (ltac:(oD' 0x8b354%Z)).
zstep (ltac:(oF' 0x8b358%Z)) (ltac:(oD' 0x8b358%Z)).
zbtk (ltac:(oF' 0x8b35c%Z)) (ltac:(oD' 0x8b35c%Z)).
zstep (ltac:(oF' 0x8b368%Z)) (ltac:(oD' 0x8b368%Z)).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_rel_skip : ltac2:(TCodec.tc2 tcn__JatRecycle1 "T7&Dy5'RGyR0%211%5241'5y8%611%311p061'B':&Q<r:(RE+2(8%33A21%6251&RF&QJr6+Q0%3221%52F1%>3F71r;+:%>3L1<%A231%;2L9%D3L21r<+;%D3Q21B%G231%I3Q116&N%11I&QD%12BK&QE&QI+R0%22M1%42C1z%821Q2%92F@r=%9216'9%=26D%<2E9%3221&H&Q@rErB+8%Q8221u8&RHrC%22QN1%:598541rF+@%Q@251r@%?5>4291rGrD+H%QF221%D5C41>6rH%QI2DQG%G5F21A9'M&Q=vR2rJ+bakL%R63RB1R4/01RBrI%756521;&Q>+1%R<3RJ1R:%3391D%R92RJJ%532R<1%R@3RNQ3R>%R<2RMQ0%83321+9%RD3S21RB%R@2S1Q9%<3421+B%RH3S61RFrA%RE2S61%A3531%J5I1Q3DN%L3QCD1p0N1p0Q21p0Q81p0Q>1p0QJ1p0QK1p0QL1p0R11p0R41p0R61p0R91p0R?1p0RB1p0RE1p0RK1p0S21pUHSB1pULSC1pUJSD1pT4SE1pSLSF1pU:SG1pTNSO1pU4SJ1pQ<SK1pU0T11").
Proof.
intros regs M rom raw sp beg en x8 x9 x18 H2 H10 H11 Hret Hsp Hsp' He Hbe Hb Hx8 Hx9 Hx18 F1 F8 F9 F18.
zbtk (ltac:(oF' 0x9477c%Z)) (ltac:(oD' 0x9477c%Z)).
zld (ltac:(oF' 0x947a0%Z)) (ltac:(oD' 0x947a0%Z)) (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x947a4%Z)) (ltac:(oD' 0x947a4%Z)) (sp - 16) F8.
zld (ltac:(oF' 0x947a8%Z)) (ltac:(oD' 0x947a8%Z)) (sp - 24) F9.
zld (ltac:(oF' 0x947ac%Z)) (ltac:(oD' 0x947ac%Z)) (sp - 32) F18.
zstep (ltac:(oF' 0x947b0%Z)) (ltac:(oD' 0x947b0%Z)).
stepret (ltac:(oF' 0x947b4%Z)) (ltac:(oD' 0x947b4%Z)) raw ltac:(reflexivity).
zret.
Qed.
#[using="Type"] Lemma art_flush_post_fn : ltac2:(TCodec.tc2 tcn__JatRecycle1 "QE&Dy5'RGyR0%211%5241'5y8%611%311p061':&Q<r4(RE+1(8%33@21%6251r1%93@21&Nr2%211r6+:%<3I1:%?231&RFz%22K1%D3K41'M&Q@&Q=vR2r7+a\k@%H3Q31F/01Q3r5%75652A1&Q>%137A=%:591OD4%=3<41p0?1p0H1p0L1pTNQ=1pU4Q81pQ<Q91pU0Q?1").
Proof.
intros regs M rom raw H1 Hret H10.
stepn (ltac:(oF' 0x8b370%Z)) (ltac:(oD' 0x8b370%Z)). rwH. zclosed 0.
stepret (ltac:(oF' 0x8b374%Z)) (ltac:(oD' 0x8b374%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
#[using="Type"] Lemma art_flush_frame_ext : ltac2:(TCodec.tc2 tcn__JatRecycle1 "QC'RGyR0%211'5y8%511%311p051'B&Dy5%2219':&Q<r1(RE+8(8%33821%6251r2%8213%:3D31+9%93>17%<251r3%>213%@3J31+B%?3D1=%B251r4%D213%F3Q031&Q9r8r7r6%443217r5%645431%N3Q331p091p0@1p0G1pU2Q31pU0Q41pTNQ>1pU:Q91pQ<Q;1").
Proof. intros M sp raw regs regs' E8 E9 E18. unfold art_flush_frame. rewrite E8, E9, E18. reflexivity. Qed.
Definition art_blk_ok (mb ms : Z) : Prop := (0 <= mb /\ mb + ms <= SB - 1) \/ (kHighMemBeg <= mb /\ mb + ms <= kHighMemEnd).
Definition art_flush_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
art_flush_frame (art_flush_frame M sp raw regs) sp raw regs.
#[using="Type"] Lemma art_flush_a_run : ltac2:(TCodec.tc2 tcn__JatRecycle1 "UG&Dy5'RGyR0%211%5241'5y8%611%311p061'B':&Q<r7(RE+1(8%33A21%6251r4%93A21r8+2%93G17%<231&RF%12H7%@3H31r9+:%@3N1>%C231%E3M16r:+;%E3Q31C%H231%J3Q21;&QD&QB+VbTP0+Q0%3221%521N&QE&QI+R0%22I1%42K1&I&Q@r<&QJ%12I<%54431=z%B21Q3&Q4%12IN&Q1r?%211';'9'M&Q=vR2rB+_Rn8%QG3R31QE/01R3rAr@%8576321r1+bai4%QN3R:1QL/01R:&Q9r>%2491D=%@5?7419%B3Q091%R729QE&Q0&QCr=+8%3221%QB251%R12RH1%R@3RH81%R@2BQI%QF27Q:%9217%QH2;1%R72RN1%RF3RN51%RF2HRA%RH3S01Q7%RH2JR=%R<2S3F%RK3S321%S61S7&QA(0+3%RM3S;1RK+4%RO3S=1RM%S03S>GRN+9%S23S@1S0+B%S43SB1S2+C%S63SD1S4+D%S83SF1S6+E%S:3SH1S8+F%S<3SJ1S:+G%S>3SL1S<+H%S@3SN1S>+I%SB3T01S@+J%SD3T21SB+K%SF3T41SD(4%11O%N3Q031%O3Q161%Q03Q291%Q13Q3<1%Q23Q4?1%Q33Q5B1%Q43Q6E1%Q53Q7H1%Q63Q8K1%Q73Q9N1%Q83Q:Q11%Q93Q;Q41%Q:3Q<Q61%Q;3Q=Q91%Q=3Q>R;1r3r2%T<221rD%T>213%T@3TH31p071pTLQF1%RO2QH1%S02QL1%S12QO1%S22R61%S32R@1qU2TO1%S62U01p0S81p0S<1p0S?1p0SB1p0SI1p0SO1p0T61p0T<1p0TB1p0TJ1pTBU51pT>U61pU:U71pTNU?1pU4U:1pQ<U;1pU0UA1").
Proof.
intros regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms [B|B] L.
- apply art_flush_a_lo; assumption.
- apply art_flush_a_hi; assumption.
Qed.
#[using="Type"] Lemma art_blk_shadow_range : ltac2:(TCodec.tc2 tcn__JatRecycle1 "O'B&QDzr1%3221&Q4r3r2%3221'9&QCr4+8%3221%=2<1&QB%125:%7215%A251&QE&QI+2+Q<%3221%5271%@271%A2<1p0C1p0H1pTBM1pT>N1").
Proof.
intros mb ms Hms B. pose proof (eq_refl : SB = 2147450880) as ESB. pose proof (eq_refl : kHighMemBeg = 0x10007fff8000) as EHB. pose proof (eq_refl : kHighMemEnd = 0x7fffffffffff) as EHE.
assert (0 <= mb /\ mb + ms < 2 ^ 47) as [Hmb Hhi] by (destruct B; lia).
split; [apply Z.div_pos; lia|]. split; [apply Z.div_le_mono; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_flush_pre_run := (ltac2:(TCodec.tc2 tcn__JatRecycle1 "V3&Dy5'RGyR0%211%5241'5y8%611%311p061'B':&Q<r7(RE+1(8%33A21%6251r4%93A21r8+2%93G17%<231&RF%12H7%@3H31r9+:%@3N1>%C231%E3M16r:+;%E3Q31C%H231%J3Q21;&QD&QB+VbTP0+Q0%3221%521N&QE&QI+R0%22I1%42K1&I&Q@r<&QJ%12I<%54431=z%B21Q3&Q4%12IN&Q1r?%211&Hr@+QVY`Hu8+QiYm0%55A4321rA+TP0%85D2451rB+QVYcH%;5G218QJ&Q7%11?&Q8r>%22B1%Q3241';'9'M&Q=vR2rF+_Rn8%R93RE1R7/01RErErD%8576321r1+a\k<%R@3RL1R>/01RL&Q5rC%249K1=%@5?7419%B3QB91&J%L1Q2%K2Q3Q8%QD212%43=31%RN2>RI%S03S81:%S02@RE%RD2S;Q6%S33S;21%S>1S?&QA(0+3%S53SC1S3+4%S73SE1S5+8%S93SG1S7+9%S;3SI1S9+B%S=3SK1S;+C%S?3SM1S=+D%SA3SO1S?+E%SC3T11SA+F%SE3T31SC+G%SG3T51SE+H%SI3T71SG+I%SK3T91SI+J%SM3T;1SK+K%SO3T=1SM(4%11Q0%O3Q131%Q03Q261%Q13Q391%Q23Q4<1%Q33Q5?1%Q43Q6B1%Q53Q7E1%Q63Q8H1%Q73Q9K1%Q83Q:N1%Q93Q;Q11%Q:3Q<Q41%Q;3Q=Q71%Q<3Q>Q:1%Q>3Q?R21r3r2%TE221rH%TG213%TI3U131p071pTLQG1%RF2QI1%RG2QM1%RH2R01%RI2R61qU2U71%RL2U81p0RN1p0S51p0S91p0S=1p0SD1p0SH1p0SK1p0SN1p0T51p0T;1p0TB1p0TH1p0TN1p0U61pTBUA1pT>UB1pU:UC1pTNUK1pU4UF1pQ<UG1pU0UM1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_flush_pre_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_flush_pre_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_flush_pre_run) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_flush_pre_run) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_flush_pre_run) 4%nat 0%nat).
Variable mb : ltac:(sec_ty2 constr:(SEC_T_art_flush_pre_run) 5%nat 0%nat).
Variable ms : ltac:(sec_ty2 constr:(SEC_T_art_flush_pre_run) 6%nat 0%nat).
Lemma art_flush_pre_run : ltac:(sec_stmt2 constr:(SEC_T_art_flush_pre_run) 7%nat 0%nat).
Proof using Type regs M rom raw sp mb ms.
intros H1 H2 H10 H11 Hsp Hsp' W Hms B L Cpc Cpg Cgot Hbe.
destruct (art_blk_shadow_range mb ms Hms B) as (D1 & D2 & D3). pose proof (eq_refl : SB = 2147450880) as ESB.
destruct (art_flush_a_run regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms B L) as (r1 & RUN1 & A10 & A11 & A1 & A2 & AK).
pose proof (art_flush_frame_wr M sp raw regs _ _ W) as W1.
pose proof (art_flush_frame_other M sp raw regs 0x132618 8%nat 0x1ca7a0 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cpc) as Cpc1.
pose proof (art_flush_frame_other M sp raw regs 0x1ca7a0 8%nat 4096 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cpg) as Cpg1.
pose proof (art_flush_frame_other M sp raw regs 0x132678 8%nat 1 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cgot) as Cgot1.
remember (art_flush_frame M sp raw regs) as M1 eqn:EM1.
destruct (art_rel_head r1 M1 rom raw sp (SB + mb / 8) (SB + (mb + ms) / 8) A1 A2 A10 A11 Hsp Hsp' W1 ltac:(lia) ltac:(lia) ltac:(lia) Cpc1 Cpg1)
as (r2 & RUN2 & B10 & B11 & B2 & BK).
rewrite (art_flush_frame_ext M1 sp raw regs r1 (AK 8%bv ltac:(cbn; tauto)) (AK 9%bv ltac:(cbn; tauto)) (AK 18%bv ltac:(cbn; tauto))) in RUN2.
destruct (art_flush_frame_cells M1 sp raw regs ltac:(lia) Hsp') as (F1 & F8 & F9 & F18).
pose proof (art_flush_frame_other M1 sp raw regs 0x132678 8%nat 1 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cgot1) as Cgot2.
remember (art_flush_frame M1 sp raw regs) as M2 eqn:EM2.
unfold art_flush_beg, art_flush_end in *.
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R8. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R9. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as R18.
change (bv_modulus 64) with (2 ^ 64) in *.
assert (P1 : 0 <= art_pg_dn (SB + mb / 8 + 4095)) by (unfold art_pg_dn; pose proof (Z.mod_pos_bound (SB + mb / 8 + 4095) 4096 ltac:(lia)); lia).
assert (P2 : art_pg_dn (SB + (mb + ms) / 8) < 2 ^ 64) by (unfold art_pg_dn; pose proof (Z.mod_pos_bound (SB + (mb + ms) / 8) 4096 ltac:(lia)); lia).
pose proof (art_rel_madv r2 M2 rom raw sp _ _ _ _ _ B2 B10 B11 ltac:(lia) Hsp' P1 Hbe P2 R8 R9 R18 F1 F8 F9 F18 Cgot2) as RUN3.
assert (EM : M2 = art_flush_mem M sp raw regs) by (subst M2 M1; reflexivity). rewrite EM in RUN3, RUN2.
eexists. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3|].
split; [unfold art_madvise_args; repeat split; gres; first [reflexivity | exact B10]|].
split; [gres; reflexivity|]. split; [gres; reflexivity|].
intros r Hr. rewrite <- (AK r Hr). cbn [In] in Hr.
destruct Hr as [<-|Hr]; [gres; apply BK; cbn; tauto|]. destruct Hr as [<-|Hr]; [gres; apply BK; cbn; tauto|].
destruct Hr as [<-|Hr]; [gres; rewrite Z_to_bv_bv_unsigned; symmetry; apply AK; cbn; tauto|].
destruct Hr as [<-|Hr]; [gres; rewrite Z_to_bv_bv_unsigned; symmetry; apply AK; cbn; tauto|].
destruct Hr as [<-|Hr]; [gres; rewrite Z_to_bv_bv_unsigned; symmetry; apply AK; cbn; tauto|].
repeat (destruct Hr as [<-|Hr]; [gres; apply BK; cbn; tauto|]). destruct Hr.
Qed.
End SE.
#[using="Type"] Lemma art_flush_skip_run : ltac2:(TCodec.tc2 tcn__JatRecycle1 "UI&Dy5'RGyR0%211%5241'5y8%611%311p061'B':&Q<r7(RE+1(8%33A21%6251r4%93A21&Nr5%211r9+2%<3J1:%?231&RF%12K7%C3K31r:+:%C3Q11A%F231%H3Q016r;+;%H3Q61F%K231%M3Q51;&QD&QB+VbTP0+Q0%3221r8%6221&QE&QI+R0%22J1%42L1&I&Q@r=&QJ%12J=%54431>z%C21Q4&Q4%12JO&Q1r@%211&HrA+QVY`Hu8+QiYm0%55A4321rB+TP0%85D2451&Q8r?r>%3221&Q7%114%Q8231';'9'M&Q=vR2rF+_Rn8%R;3RG1R9/01RGrErD%8576321r1rC&Q5%146I2:%=5<4316%?3Q=61%RH26R:%R92S3M%RK3S321%S61S7&QA(0+3%RM3S;1RK+4%RO3S=1RM+8%S13S?1RO+9%S33SA1S1+B%S53SC1S3+C%S73SE1S5+D%S93SG1S7+E%S;3SI1S9+F%S=3SK1S;+G%S?3SM1S=+H%SA3SO1S?+I%SC3T11SA+J%SE3T31SC+K%SG3T51SE(4%11Q0%O3Q131%Q03Q261%Q13Q391%Q23Q4<1%Q33Q5?1%Q43Q6B1%Q53Q7E1%Q63Q8H1%Q73Q9K1%Q83Q:N1%Q93Q;Q11%Q:3Q<Q41%Q;3Q=Q71%Q<3Q>Q:1%Q>3Q?QH1r3r2%T=221rH%T?213%TA3TI31p071pTLQG1%R<2QI1%R=2QM1qU2TM1%R@2TN1p0RB1p0RJ1p0RN1p0S51p0S91p0S<1p0S?1p0SF1p0SL1p0T41p0T:1p0T@1p0TH1p0TL1pTBU71pT>U81pU:U91pTNUA1pU4U<1pQ<U=1pU0UC1").
Proof.
intros regs M rom raw sp mb ms H1 Hret H2 H10 H11 Hsp Hsp' W Hms B L Cpc Cpg Hbe.
destruct (art_blk_shadow_range mb ms Hms B) as (D1 & D2 & D3). pose proof (eq_refl : SB = 2147450880) as ESB.
destruct (art_flush_a_run regs M rom raw sp mb ms H1 H2 H10 H11 Hsp Hsp' W Hms B L) as (r1 & RUN1 & A10 & A11 & A1 & A2 & AK).
pose proof (art_flush_frame_wr M sp raw regs _ _ W) as W1.
pose proof (art_flush_frame_other M sp raw regs 0x132618 8%nat 0x1ca7a0 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cpc) as Cpc1.
pose proof (art_flush_frame_other M sp raw regs 0x1ca7a0 8%nat 4096 ltac:(lia) Hsp' ltac:(lia) ltac:(cbn; lia) ltac:(unfold apart; cbn; lia) Cpg) as Cpg1.
remember (art_flush_frame M sp raw regs) as M1 eqn:EM1.
destruct (art_rel_head r1 M1 rom raw sp (SB + mb / 8) (SB + (mb + ms) / 8) A1 A2 A10 A11 Hsp Hsp' W1 ltac:(lia) ltac:(lia) ltac:(lia) Cpc1 Cpg1)
as (r2 & RUN2 & B10 & B11 & B2 & BK).
rewrite (art_flush_frame_ext M1 sp raw regs r1 (AK 8%bv ltac:(cbn; tauto)) (AK 9%bv ltac:(cbn; tauto)) (AK 18%bv ltac:(cbn; tauto))) in RUN2.
destruct (art_flush_frame_cells M1 sp raw regs ltac:(lia) Hsp') as (F1 & F8 & F9 & F18).
remember (art_flush_frame M1 sp raw regs) as M2 eqn:EM2.
unfold art_flush_beg, art_flush_end in *.
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R8. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R9. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as R18.
change (bv_modulus 64) with (2 ^ 64) in *.
assert (P1 : art_pg_dn (SB + mb / 8 + 4095) < 2 ^ 64) by (unfold art_pg_dn; pose proof (Z.mod_pos_bound (SB + mb / 8 + 4095) 4096 ltac:(lia)); lia).
assert (P2 : 0 <= art_pg_dn (SB + (mb + ms) / 8)) by (unfold art_pg_dn; pose proof (Z.mod_pos_bound (SB + (mb + ms) / 8) 4096 ltac:(lia)); lia).
pose proof (art_rel_skip r2 M2 rom raw sp _ _ _ _ _ B2 B10 B11 Hret ltac:(lia) Hsp' P2 Hbe P1 R8 R9 R18 F1 F8 F9 F18) as RUN3.
assert (EM : M2 = art_flush_mem M sp raw regs) by (subst M2 M1; reflexivity). rewrite EM in RUN3, RUN2.
eexists. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3|].
split; [gres; reflexivity|].
intros r Hr. rewrite <- (AK r Hr). cbn [In] in Hr.
destruct Hr as [<-|Hr]; [gres; apply BK; cbn; tauto|]. destruct Hr as [<-|Hr]; [gres; apply BK; cbn; tauto|].
destruct Hr as [<-|Hr]; [gres; rewrite Z_to_bv_bv_unsigned; symmetry; apply AK; cbn; tauto|].
destruct Hr as [<-|Hr]; [gres; rewrite Z_to_bv_bv_unsigned; symmetry; apply AK; cbn; tauto|].
destruct Hr as [<-|Hr]; [gres; rewrite Z_to_bv_bv_unsigned; symmetry; apply AK; cbn; tauto|].
repeat (destruct Hr as [<-|Hr]; [gres; apply BK; cbn; tauto|]). destruct Hr.
Qed.
#[using="Type"] Lemma art_flush_mem_agree : ltac2:(TCodec.tc2 tcn__JatRecycle1 "Q='RGyR0%211'5y8%511%311p051'B&Dy5%2219&QD+Q0r3%3221&QEr4&QI+2+R0%3221%6251&O(0'7%12BB(6&QJr5%221A%44GG1B(4%117%:3831r6&Q5%1428DG%?3431p0A1p0I1pU0N1pTNQ81pU:Q31pQ<Q51").
Proof.
intros M sp raw regs Hsp Hsp'. unfold art_flush_mem, art_flush_frame.
eapply art_agree_sub; [zagree|]. zsub.
Qed.
#[using="Type"] Lemma art_flush_mem_grows : ltac2:(TCodec.tc2 tcn__JatRecycle1 "H'RGyR0%211'5y8%511%311p051'B&Dy5%2219&Q?r4&Q5r3r2r1%445321%7261pU091pTNC1pU:>1pQ<@1").
Proof. intros. unfold art_flush_mem, art_flush_frame. zgrows. Qed.
End FPX1.
Lemma art_pg_dn_spec : ltac2:(TCodec.tc2 tcn__JatRecycle1 "G'B&QDzr1%3221'9':&QF&Q;r2%211+TP0%5221%73=1;%=245&QE&QB%1276%3291%>251%?271p0A1pUFF1").
Proof.
intros x Hx. unfold art_pg_dn. pose proof (Z.div_mod x 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as B.
split; [|lia]. replace (x - x mod 4096) with (x / 4096 * 4096) by lia. apply Z_mod_mult.
Qed.
Section SE.
Local Abbreviation SEC_T_art_flush_range := (ltac2:(TCodec.tc2 tcn__JatRecycle1 "R4'B':&QFr2+TP0%3221z%63721&QDr4%2241&Q7r6%211&Q8r7%2214'9r1%A21?%C3D1>&QJ%124C%E21C%G3H1B&QB&Q0&QCr8+8%3221%6251%H21M%825B%7215%:291%L2B1%:2F8%=281%Q63Q751&L%11=%Q221Q7&K%12@M%Q52K1+RPP0%Q721Q0&QEr3%221Q?p041%Q3271%Q42;1%Q52?1%Q62C1%Q72H1%Q82Q11%Q92Q61%Q:2QD1tT4QLQ<1tSLQMQ@1p0QD1p0QE1p0QI1p0QJ1pTBR21pT>R31")) (only parsing).
Variable mb : ltac:(sec_ty2 constr:(SEC_T_art_flush_range) 0%nat 0%nat).
Variable ms : ltac:(sec_ty2 constr:(SEC_T_art_flush_range) 1%nat 0%nat).
Lemma art_flush_range : ltac:(sec_stmt2 constr:(SEC_T_art_flush_range) 2%nat 0%nat).
Proof.
intros Hmb Hms Hmb0 Hms0 beg en.
subst beg en. unfold art_flush_beg, art_flush_end.
pose proof (eq_refl : SB = 2147450880) as ESB.
assert (Er : mb = 4096 * (mb / 4096)) by (pose proof (Z.div_mod mb 4096 ltac:(lia)); lia).
assert (Em : ms = 4096 * (ms / 4096)) by (pose proof (Z.div_mod ms 4096 ltac:(lia)); lia).
set (kr := mb / 4096) in *. set (km := ms / 4096) in *.
assert (D1 : mb / 8 = 512 * kr). { rewrite Er. replace (4096 * kr) with (512 * kr * 8) by lia. apply Z.div_mul. lia. }
assert (D2 : ms / 8 = 512 * km). { rewrite Em. replace (4096 * km) with (512 * km * 8) by lia. apply Z.div_mul. lia. }
assert (D3 : (mb + ms) / 8 = 512 * kr + 512 * km). { rewrite Er, Em. replace (4096 * kr + 4096 * km) with ((512 * kr + 512 * km) * 8) by lia. apply Z.div_mul. lia. }
rewrite D3, D1, D2.
destruct (art_pg_dn_spec (SB + 512 * kr + 4095) ltac:(lia)) as (P1 & P2). destruct (art_pg_dn_spec (SB + (512 * kr + 512 * km)) ltac:(lia)) as (P3 & P4).
set (B := art_pg_dn (SB + 512 * kr + 4095)) in *. set (E := art_pg_dn (SB + (512 * kr + 512 * km))) in *.
assert (PB : B = 4096 * (B / 4096)) by (pose proof (Z.div_mod B 4096 ltac:(lia)); lia).
assert (PE : E = 4096 * (E / 4096)) by (pose proof (Z.div_mod E 4096 ltac:(lia)); lia).
split; [exact P1|]. split; [exact P3|].
split. { rewrite PB, PE. replace (4096 * (E / 4096) - 4096 * (B / 4096)) with ((E / 4096 - B / 4096) * 4096) by lia. apply Z_mod_mult. }
assert (LB : SB + 512 * kr <= B).
{ destruct (Z_lt_le_dec B (SB + 512 * kr)) as [L|G]; [|exact G]. exfalso.
assert (4096 * (B / 4096) + 4096 <= SB + 512 * kr + 4095) by lia. lia. }
split; [exact LB|]. split; [lia|]. split; [reflexivity|].
unfold art_shlo, art_shhi. rewrite D1, D3.
pose proof (Z.div_mod (512 * kr + 2147450880) 4096 ltac:(lia)) as Q1. pose proof (Z.mod_pos_bound (512 * kr + 2147450880) 4096 ltac:(lia)) as Q2.
pose proof (Z.div_mod (512 * kr + 512 * km + 2147450880 + 4095) 4096 ltac:(lia)) as Q3. pose proof (Z.mod_pos_bound (512 * kr + 512 * km + 2147450880 + 4095) 4096 ltac:(lia)) as Q4.
set (X := (512 * kr + 2147450880) / 4096) in *. set (Y := (512 * kr + 512 * km + 2147450880 + 4095) / 4096) in *.
split; [lia|]. split; [lia|].
intros H64. lia.
Qed.
End SE.
Fixpoint art_gbb_scan (m near : Z) (chs : list Z) : Z :=
match chs with [] => near | ch :: r => art_gbb_scan m (if (ch <=? m) && (near <? ch) then ch else near) r end.
Lemma art_gbb_scan_range : ltac2:(TCodec.tc2 tcn__JatRecycle1 "K'2'B%211'9&QDzr1%3221r2%5231%7231'@qSN;5r4%33=21&Q:r3r5%33521%?2>1%@227%B221p081p0=1pTHG1pT<H1pT0H1").
Proof.
induction chs as [|ch r IH]; intros m near Hn F; cbn [art_gbb_scan]; [exact Hn|].
inversion F as [|? ? F1 F2]; subst. apply IH; [|exact F2].
destruct (Z.leb_spec ch m); destruct (Z.ltb_spec near ch); cbn [andb]; lia.
Qed.
Lemma art_gbb_scan_is : ltac2:(TCodec.tc2 tcn__JatRecycle1 "Q4'2'B%211'=&QAr2r4%33621':r1%23915%8241&QDr3%2218r8%<3?71%52<2%6253p021p041pSND1&Q:r7r5%3321:r6%C3J21p071p0?1p0@1p0D1pTHO1pT8Q01pT<Q11pT0Q11").
Proof.
induction chs as [|ch r IH]; intros m h near Hin Hm Hn Hmax; cbn [art_gbb_scan].
- destruct Hin as [[]|E]. exact E.
- apply IH; [| exact Hm | | intros c Hc; apply Hmax; right; exact Hc].
+ destruct Hin as [[E|Hin]|E].
* subst ch. right. replace (h <=? m) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
destruct (Z.ltb_spec near h); lia.
* left. exact Hin.
* right. subst near. pose proof (Hmax ch ltac:(left; reflexivity)) as Hc.
destruct (Z.leb_spec ch m); cbn [andb]; [|reflexivity]. destruct (Z.ltb_spec h ch); [lia|reflexivity].
+ pose proof (Hmax ch ltac:(left; reflexivity)) as Hc.
destruct (Z.leb_spec ch m); destruct (Z.ltb_spec near ch); cbn [andb]; lia.
Qed.
Section FPX2. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_gbb_loop : ltac2:(TCodec.tc2 tcn__JatRecycle1 "U@'2'B%211&Dy5'RGyR0%211%5241'5y8%611%311p061':&Q<r7(RE+<(8%33@21%6251&RFr4%22B1%;3B41r8+>%;3H19%>231%@3G16r9+;%@3M1>%C231%E3L1;r:+=%E3Q21C%H231%J3Q11@&QB&QG+8&QH&1r<%22Q>1%411%7261%92H1%Q53QBQ31'>u1r=%:2QF1%4231&QDz%221G&QE&QI+2+R0%3221%52M1'9%:29Q4%;2Q5Q0%3221r;%;217'3&?r1rC%O2R;1%4231&Ar2rD%34R@21G%I2H1%G22C%B221&H&Q@rBr@%Q=1:%Q@2Q?1%QB231u8%857621<%L2:1p0B1pT:H1';'M&Q=vR2+Z`_4%RE3S01RC/01S0rA%655N2B1+Z``@%RJ3S51RH/01S5%:59Q31F5%<3H51%S02Q5R9&Q:r>%231QLQ2%RM2S=1%S63S=51%S@1SA&<+5%S73SD1S5%S;34Q?1%411%S=36Q<S7%611r3%S@391RH%911+?%S@3SM1S>%SD3=S;1%=11r5+@%SE3T21SC%SI3B31%B11r6+A%SJ3T71SH%SN3G31%G11%SO2SDSNrJ%T121T0%T33T:31p051p0;1p0A1p0F1p0J1p0M1pTLQ31%RG2Q51%RH2Q<1qU2TC1%QK2TD1p0QM1p0RG1p0RJ1p0RO1p0S61p0S:1p0S@1p0SL1p0T21p0T81p0T>1pTHU71pT<U81pT4U91pT2U:1pU4TO1pQ<U01pU0U61pT0U=1").
Proof.
induction chs as [|ch chs IH]; intros regs M rom cur en m near H12 H14 H11 H13 Een Hlen Hcur Hen Hnear Hm Cws; cbn [length] in *. lia.
destruct (Cws O ltac:(lia)) as [Rch Cch]. cbn [nth] in Rch, Cch. replace (cur + 8 * Z.of_nat 0) with cur in Cch by lia.
set (near' := if (ch <=? m) && (near <? ch) then ch else near).
assert (Hnear' : 0 <= near' <= m) by (subst near'; destruct (Z.leb_spec ch m); destruct (Z.ltb_spec near ch); cbn [andb]; lia).
assert (STEP : exists regs1, msteps ASEGS (mkst regs (0x541e4 : word) M rom) (mkst regs1 (0x541e0 : word) M rom)
/\ getr regs1 12 = Z_to_bv 64 (cur + 8) /\ getr regs1 13 = Z_to_bv 64 near' /\ getr regs1 14 = Z_to_bv 64 en /\ getr regs1 11 = Z_to_bv 64 m
/\ (forall r : reg, r <> 5%bv -> r <> 12%bv -> r <> 13%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs1 r = getr regs r)).
{ destruct (Z.leb_spec ch m) as [Lm|Gm].
- destruct (Z.ltb_spec near ch) as [Ln|Gn]; subst near'; cbn [andb].
+
eexists. split.
{ zld (ltac:(oF' 0x541e4%Z)) (ltac:(oD' 0x541e4%Z)) cur Cch. zstep (ltac:(oF' 0x541e8%Z)) (ltac:(oD' 0x541e8%Z)). zstep (ltac:(oF' 0x541ec%Z)) (ltac:(oD' 0x541ec%Z)). zstep (ltac:(oF' 0x541f0%Z)) (ltac:(oD' 0x541f0%Z)).
zbtk (ltac:(oF' 0x541f4%Z)) (ltac:(oD' 0x541f4%Z)). zbft (ltac:(oF' 0x54204%Z)) (ltac:(oD' 0x54204%Z)). zstep (ltac:(oF' 0x54208%Z)) (ltac:(oD' 0x54208%Z)). stepn (ltac:(oF' 0x5420c%Z)) (ltac:(oD' 0x5420c%Z)). zstep (ltac:(oF' 0x541dc%Z)) (ltac:(oD' 0x541dc%Z)). apply mst_refl. }
repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve.
+
eexists. split.
{ zld (ltac:(oF' 0x541e4%Z)) (ltac:(oD' 0x541e4%Z)) cur Cch. zstep (ltac:(oF' 0x541e8%Z)) (ltac:(oD' 0x541e8%Z)). zstep (ltac:(oF' 0x541ec%Z)) (ltac:(oD' 0x541ec%Z)). zstep (ltac:(oF' 0x541f0%Z)) (ltac:(oD' 0x541f0%Z)).
zbft (ltac:(oF' 0x541f4%Z)) (ltac:(oD' 0x541f4%Z)). zstep (ltac:(oF' 0x541f8%Z)) (ltac:(oD' 0x541f8%Z)). zbft (ltac:(oF' 0x541fc%Z)) (ltac:(oD' 0x541fc%Z)). stepn (ltac:(oF' 0x54200%Z)) (ltac:(oD' 0x54200%Z)). zstep (ltac:(oF' 0x54208%Z)) (ltac:(oD' 0x54208%Z)). stepn (ltac:(oF' 0x5420c%Z)) (ltac:(oD' 0x5420c%Z)). zstep (ltac:(oF' 0x541dc%Z)) (ltac:(oD' 0x541dc%Z)). apply mst_refl. }
repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve.
-
subst near'. cbn [andb].
eexists. split.
{ zld (ltac:(oF' 0x541e4%Z)) (ltac:(oD' 0x541e4%Z)) cur Cch. zstep (ltac:(oF' 0x541e8%Z)) (ltac:(oD' 0x541e8%Z)). zstep (ltac:(oF' 0x541ec%Z)) (ltac:(oD' 0x541ec%Z)). zstep (ltac:(oF' 0x541f0%Z)) (ltac:(oD' 0x541f0%Z)).
replace (Z_to_bv 64 (m - ch)) with (Z_to_bv 64 (2 ^ 64 + m - ch)) by (apply art_zb_eq; replace (2 ^ 64 + m - ch) with (m - ch + 1 * 2 ^ 64) by lia; apply Z_mod_plus_full).
zbft (ltac:(oF' 0x541f4%Z)) (ltac:(oD' 0x541f4%Z)). zstep (ltac:(oF' 0x541f8%Z)) (ltac:(oD' 0x541f8%Z)). zbtk (ltac:(oF' 0x541fc%Z)) (ltac:(oD' 0x541fc%Z)). zstep (ltac:(oF' 0x541dc%Z)) (ltac:(oD' 0x541dc%Z)). apply mst_refl. }
repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve. }
destruct STEP as (regs1 & RUN1 & P12 & P13 & P14 & P11 & K1).
destruct chs as [|ch2 chs2].
-
cbn [length] in *. eexists. split; [|split].
+ eapply msteps_trans; [exact RUN1|]. zbtk (ltac:(oF' 0x541e0%Z)) (ltac:(oD' 0x541e0%Z)). apply mst_refl.
+ cbn [art_gbb_scan]. exact P13.
+ exact K1.
- cbn [length] in *.
assert (RUNb : msteps ASEGS (mkst regs1 (0x541e0 : word) M rom) (mkst regs1 (0x541e4 : word) M rom)).
{ zbft (ltac:(oF' 0x541e0%Z)) (ltac:(oD' 0x541e0%Z)). apply mst_refl. }
destruct (IH regs1 M rom (cur + 8) en m near' P12 P14 P11 P13 ltac:(cbn [length]; lia) ltac:(cbn [length]; lia) ltac:(lia) Hen Hnear' Hm
ltac:(intros j Hj; destruct (Cws (S j) ltac:(cbn [length] in *; lia)) as [R C]; split; [exact R|];
replace (cur + 8 + 8 * Z.of_nat j) with (cur + 8 * Z.of_nat (S j)) by lia; exact C))
as (regs' & RUN2 & Q13 & K2).
exists regs'. split; [|split].
+ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNb|]. exact RUN2.
+ exact Q13.
+ intros r N5 N12 N13 N15 N16 N17. rewrite K2 by assumption. apply K1; assumption.
Qed.
Definition art_gbb_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
Wn 1 (Wn 4 (art_flush_frame M sp raw regs) (0x1376d8 + 616) 1) (0x1376d8 + 616) 0.
Ltac gkeep K rnew i V := let E := fresh "E" in assert (E : getr rnew i = V) by (rewrite K by reg_neq_tac; gres; rwH; reflexivity).
Section SE.
Local Abbreviation SEC_T_art_gbb_run := (ltac2:(TCodec.tc2 tcn__JatRecycle1 "XM'2'B%211&Dy5'RGyR0%211%5241'5y8%611%311p061':&Q<r;(RE+1(8%33@21%6251r8%93@21&Nr9%211r=+2%<3I1:%?231&RF%12J7%C3J31r>+:%C3Q01A%F231+QVmfH%82Q11%J3Q131r?+;%J3Q71H%M231%O3Q61=&QD+VbTP0%221Q0r<&QJ+Q0%22I1%7241&QE&QI+R0%22M1%42H1&I&Q@rB%<2E;%44321<'>u1&1rE%22R31%5241&QHrF%62R71%311+D%D2Q?1%F231%O2NQ4&QBr@&QG+8rH%A2RB1%>11%5241%8271%Q921J'9z%Q<21M%Q52NQ2%4221&H+c8%A2QI1u4%45Q5?218rI+QH%F2QN1u8rK%Q52S61%Q211%<5Q=7541rJ%M2R5JrD%@5QA3281+TP0%B5QC9R9:1'3&?r1rO%QB2SC1%4231&Ar2rQ0%34SH21Q0%R<2Q11%R522R2%Q4221rN%QH17%Q?2Q>1%QB2Q>1%Q45R541L8%Q:261p0>1pT:D1&Q:%13QDQ=C%SI3T6R01rG%RK2RJ1+@%QM2QI1%RN21Q6&QF%12Q<Q0%T13T>1QFrQ1%QD5RE1Q7Q<Q?rQ2%R52Q=R2%QG5RH21Q?QB%S72QLQ?rL%S92QA1%R0231rM%R<24QD%S5221%R>236%S72Q51%S@2R55%RA2Q<Q2%S:21S7';'M&Q=vR2rQ:+Z`[H%TF3U11TD/01U1rQ9rQ8%8576321rQ7&Q6rQ6%24613:%=5<QN416%?3SE61%U32R0T>%S52Q1R5%TE2U>1%U73U>31%U72R4TI%TH2UA9%U:3UA21%UD1UE&QA(0+3%U<3UI1U:+4%U>3UK1U<%U?3ULS?U=+9%UA3UN1U?+B%UC3V01UA+C%UE3V21UC%UF3V3SMUD+E%UH3V51UF+F%UJ3V71UH+G%UL3V91UJ+H%UN3V;1UL+I%V03V=1UN+J%V23V?1V0+K%V43VA1V2(4%11N%M3O31%N3Q061%O3Q191%Q03Q2<1%Q13Q3?1%Q23Q4B1%Q33Q5E1%Q43Q6H1%Q53Q7J1%Q63Q8M1%Q73Q9Q01%Q83Q:Q31%Q93Q;Q51%Q:3Q<Q81%Q<3Q=SD1r3%VI21SArQ<%VK21SC%VM3W431p061pTLQD1%TF2QF1%TG2QJ1%TH2QO1qU2W91%RA2W:1p0RC1p0RF1p0RH1p0RK1p0RO1p0S41p0S81p0S;1p0S?1p0SC1p0SF1p0SJ1p0T@1p0TC1p0TH1p0U11p0U71p0U=1p0UH1p0UJ1p0V21p0V91p0V?1p0VE1p0VK1p0VO1p0W51p0W=1p0WE1p0WI1pTDX@1pT@XA1pT8XB1pTJXC1pT<XD1pQ8XE1pU:XF1pTNXA1pU4X<1pQ<X=1pU0XC1pT0XJ1")) (only parsing).
Variable chs : ltac:(sec_ty2 constr:(SEC_T_art_gbb_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_gbb_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_gbb_run) 2%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_gbb_run) 3%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_gbb_run) 4%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_gbb_run) 5%nat 0%nat).
Variable HI : ltac:(sec_ty2 constr:(SEC_T_art_gbb_run) 6%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_gbb_run) 7%nat 0%nat).
Variable parr : ltac:(sec_ty2 constr:(SEC_T_art_gbb_run) 8%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SEC_T_art_gbb_run) 9%nat 0%nat).
Variable mbeg : ltac:(sec_ty2 constr:(SEC_T_art_gbb_run) 10%nat 0%nat).
Variable msz : ltac:(sec_ty2 constr:(SEC_T_art_gbb_run) 11%nat 0%nat).
Lemma art_gbb_run : ltac:(sec_stmt2 constr:(SEC_T_art_gbb_run) 12%nat 0%nat).
Proof using Type chs regs M rom raw sp HI m parr h mbeg msz.
intros H1 Hret H2 H10 H11 HHI Hsp Hsp' W Hn Hn' Hparr Hparr' Hm Clk Cn Cparr Cpg Cws Eh Hh Hh' Hh4 Cmb Cms Hmb Hhm Hmm Hms Hme.
assert (Hhr : 0 <= h <= m) by (rewrite Eh; apply art_gbb_scan_range; [lia|]; apply Forall_forall; intros x Hx; destruct (In_nth _ _ 0 Hx) as (j & Hj & <-); apply (Cws j Hj)).
pose proof (art_img_wr M (0x1376d8 + 616) 4 ltac:(lia) ltac:(lia) ltac:(lia)) as Wlk.
eassert (RUN1 : msteps ASEGS (mkst regs (0x54178 : word) M rom) _).
{
zstep (ltac:(oF' 0x54178%Z)) (ltac:(oD' 0x54178%Z)).
zsd (ltac:(oF' 0x5417c%Z)) (ltac:(oD' 0x5417c%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x54180%Z)) (ltac:(oD' 0x54180%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x54184%Z)) (ltac:(oD' 0x54184%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x54188%Z)) (ltac:(oD' 0x54188%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zstep (ltac:(oF' 0x5418c%Z)) (ltac:(oD' 0x5418c%Z)). zstep (ltac:(oF' 0x54190%Z)) (ltac:(oD' 0x54190%Z)).
stepn (ltac:(oF' 0x54194%Z)) (ltac:(oD' 0x54194%Z)). rwH. zclosed (0x1376d8 + 616).
zstep (ltac:(oF' 0x54198%Z)) (ltac:(oD' 0x54198%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x1376d8 + 616) 4 0) by zcell; assert (Wlk' : wokA X (0x1376d8 + 616) 4) by zwok end.
zcas6 (ltac:(oF' 0x5419c%Z)) (ltac:(oD' 0x5419c%Z)) (ltac:(oF' 0x541a0%Z)) (ltac:(oD' 0x541a0%Z)) (ltac:(oF' 0x541a4%Z)) (ltac:(oD' 0x541a4%Z)) (ltac:(oF' 0x541a8%Z)) (ltac:(oD' 0x541a8%Z)) (ltac:(oF' 0x541ac%Z)) (ltac:(oD' 0x541ac%Z)) (ltac:(oF' 0x541b0%Z)) (ltac:(oD' 0x541b0%Z)) (0x1376d8 + 616) 0 1 1 1 Clk' Wlk'.
zbft (ltac:(oF' 0x541b4%Z)) (ltac:(oD' 0x541b4%Z)).
stepn (ltac:(oF' 0x541b8%Z)) (ltac:(oD' 0x541b8%Z)). rwH. zclosed 0.
zbft (ltac:(oF' 0x541bc%Z)) (ltac:(oD' 0x541bc%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cn' : cellA X (0x1376d8 + 56) 8 (Z.of_nat (length chs))) by zcell; assert (Cparr' : cellA X (0x1376d8 + 8) 8 parr) by zcell end.
zld (ltac:(oF' 0x541c0%Z)) (ltac:(oD' 0x541c0%Z)) (0x1376d8 + 56) Cn'.
zbft (ltac:(oF' 0x541c4%Z)) (ltac:(oD' 0x541c4%Z)).
zstep (ltac:(oF' 0x541c8%Z)) (ltac:(oD' 0x541c8%Z)).
zld (ltac:(oF' 0x541cc%Z)) (ltac:(oD' 0x541cc%Z)) (0x1376d8 + 8) Cparr'.
zstep (ltac:(oF' 0x541d0%Z)) (ltac:(oD' 0x541d0%Z)). zstep (ltac:(oF' 0x541d4%Z)) (ltac:(oD' 0x541d4%Z)).
stepn (ltac:(oF' 0x541d8%Z)) (ltac:(oD' 0x541d8%Z)).
apply mst_refl. }
match type of RUN1 with msteps _ _ (mkst ?R1 _ ?X1 _) =>
assert (Cws1 : forall j, (j < length chs)%nat -> 0 <= nth j chs 0 < 2 ^ 64 /\ cellA X1 (parr + 8 * Z.of_nat j) 8 (nth j chs 0))
by (intros j Hj; destruct (Cws j Hj) as [Rj Cj]; split; [exact Rj|]; pose proof (proj1 (Nat2Z.inj_lt _ _) Hj); zcell);
assert (Cmb1 : cellA X1 h 8 mbeg) by zcell; assert (Cms1 : cellA X1 (h + 8) 8 msz) by zcell; assert (Cpg1 : cellA X1 0x1376d8 8 4096) by zcell;
assert (F1 : cellA X1 (sp - 8) 8 (U raw)) by zcell; assert (F8 : cellA X1 (sp - 16) 8 (U (getr regs 8))) by zcell;
assert (F9 : cellA X1 (sp - 24) 8 (U (getr regs 9))) by zcell; assert (F18 : cellA X1 (sp - 32) 8 (U (getr regs 18))) by zcell;
assert (Wlk1 : wokA X1 (0x1376d8 + 616) 1) by zwok;
destruct (art_gbb_loop chs R1 X1 rom parr (parr + Z.of_nat (length chs) * 2 ^ 3) m 0 ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; rwH; reflexivity) ltac:(gres; reflexivity)
ltac:(lia) Hn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Cws1) as (r2 & RUN2 & Q13 & K2);
gkeep K2 r2 (2%bv : reg) (Z_to_bv 64 (sp + -32)); gkeep K2 r2 (8%bv : reg) (Z_to_bv 64 (0x1376d8 + 616)); gkeep K2 r2 (10%bv : reg) (Z_to_bv 64 0x1376d8);
gkeep K2 r2 (11%bv : reg) (Z_to_bv 64 m)
end.
rewrite <- Eh in Q13.
match type of RUN2 with msteps _ _ ?S2 => eassert (RUN3 : msteps ASEGS S2 _) end.
{
zbft (ltac:(oF' 0x54210%Z)) (ltac:(oD' 0x54210%Z)).
zld (ltac:(oF' 0x54214%Z)) (ltac:(oD' 0x54214%Z)) h Cmb1.
zbft (ltac:(oF' 0x54218%Z)) (ltac:(oD' 0x54218%Z)).
zld (ltac:(oF' 0x5421c%Z)) (ltac:(oD' 0x5421c%Z)) (h + 8) Cms1.
zstep (ltac:(oF' 0x54220%Z)) (ltac:(oD' 0x54220%Z)).
zbft (ltac:(oF' 0x54224%Z)) (ltac:(oD' 0x54224%Z)). zbft (ltac:(oF' 0x54228%Z)) (ltac:(oD' 0x54228%Z)). zbft (ltac:(oF' 0x5422c%Z)) (ltac:(oD' 0x5422c%Z)).
zld (ltac:(oF' 0x54230%Z)) (ltac:(oD' 0x54230%Z)) 0x1376d8 Cpg1.
zstep (ltac:(oF' 0x54234%Z)) (ltac:(oD' 0x54234%Z)).
stepn (ltac:(oF' 0x54238%Z)) (ltac:(oD' 0x54238%Z)). rwH. rewrite art_zb_and by lia.
replace (Z.land 4095 h) with 0 by (change 4095 with (Z.ones 12); rewrite Z.land_comm, Z.land_ones by lia; change (2 ^ 12) with 4096; lia).
zbft (ltac:(oF' 0x5423c%Z)) (ltac:(oD' 0x5423c%Z)).
zstep (ltac:(oF' 0x54240%Z)) (ltac:(oD' 0x54240%Z)).
stepn (ltac:(oF' 0x54244%Z)) (ltac:(oD' 0x54244%Z)).
stepfence (ltac:(oF' 0x5426c%Z)) (ltac:(oD' 0x5426c%Z)).
zsb (ltac:(oF' 0x54270%Z)) (ltac:(oD' 0x54270%Z)) (0x1376d8 + 616) 0 ltac:(exact Wlk1).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
assert (G9 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (G18 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell end.
zld (ltac:(oF' 0x54274%Z)) (ltac:(oD' 0x54274%Z)) (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x54278%Z)) (ltac:(oD' 0x54278%Z)) (sp - 16) G8. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x5427c%Z)) (ltac:(oD' 0x5427c%Z)) (sp - 24) G9. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x54280%Z)) (ltac:(oD' 0x54280%Z)) (sp - 32) G18. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x54284%Z)) (ltac:(oD' 0x54284%Z)).
stepret (ltac:(oF' 0x54288%Z)) (ltac:(oD' 0x54288%Z)) raw ltac:(reflexivity).
apply mst_refl. }
eexists. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3|].
split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|].
intros r Hr. cbn [In] in Hr.
destruct Hr as [<-|Hr]; [gres; rewrite K2 by reg_neq_tac; gres; reflexivity|]. destruct Hr as [<-|Hr]; [gres; rewrite K2 by reg_neq_tac; gres; reflexivity|].
destruct Hr as [<-|Hr]; [gres; reflexivity|]. destruct Hr as [<-|Hr]; [gres; reflexivity|]. destruct Hr as [<-|Hr]; [gres; reflexivity|].
repeat (destruct Hr as [<-|Hr]; [gres; rewrite K2 by reg_neq_tac; gres; reflexivity|]). destruct Hr.
Qed.
End SE.
#[using="Type"] Lemma art_gbb_mem_facts : ltac2:(TCodec.tc2 tcn__JatRecycle1 "R3'RGyR0%211'5y8%511%311p051'B&Dy5%2219&QD&QB+VbTP0+Q0%3221r3%6221&QEr4&QI+2+R0%3221%6251&Q6r6r5%34219<'9&Q?r7r1%3221&O(0'7%12NN(6&QJ%12>J%34Q2Q21K+QVmfH+c8%Q0221+4%84Q7Q721(4%11;%>3<31%?3=91%A31DC&H&Q@u4z%453H<21%L261%M2I1tQ>QEO1p0Q41p0Q<1pU0QD1pTNQN1pU:QI1pQ<QK1").
Proof.
intros M sp raw regs Hsp Hsp'. cbv zeta. unfold art_gbb_mem, art_flush_frame. split; [zgrows|]. split.
- eapply art_agree_sub; [zagree|]. zsub.
- apply art_lock_word_release; [lia|lia|]. apply cell_Wn_hit; [lia|cbn; lia].
Qed.
End FPX2.
