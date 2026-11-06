(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac JbtDepotA JbtSecAlloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtMmapFixed () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtMmapFixed.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2not"; "3Z"; "0F"; "4bvmap"; "0M"; "5Wn"; "5cell"; "5wr"; "6msteps"; "7ret_ok"; "8art_mmapfixed_mem"; "8art_rar_map_mem"]; ["9getr"; "9mkst"; "9regupd"; ":mem_grows"; ";loaded_segments"; "<add"; "<land"; "<le"; "<lt"; "<modulo"; "<pow"; "<sub"; "0addr"; "0fb"; "0fx"; "0name"]; ["0q"; "0raw"; "0regs"; "0rg"; "0rom"; "0s"; "0size"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0tol"; "0x"; "0x1"; "0x18"; "0x19"]; ["0x20"; "0x8"; "0x9"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma mf_roundup_id : ltac2:(TCodec.tc2 tcn__JbtMmapFixed "D'5&Gzr1%3221'3&Ir2+TP0%3221%53:18&Er3+SoO%3221%9217%;3@13p071p0>1pRJC1").
Proof.
intros x Hx Hm. pose proof (Z.div_mod x 4096 ltac:(lia)) as E. rewrite Hm in E.
symmetry. apply (Z.mod_unique_pos (x + 4095) 4096 (x / 4096) 4095); lia.
Qed.
Section FPX. Context {fx : PropExec.FPState}.
Definition art_mmapfixed_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size tol name : Z) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
(s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18))) (s - 40) (U (getr rg 19))) (s - 48) (U (getr rg 20)))
(s - 96) 50)
(s - 104) 0x8d39c) (s - 112) size) (s - 120) tol) (s - 128) addr) (s - 136) name) (s - 144) 0x1cc4e0) (s - 152) (U (getr rg 21)).
Section SE.
Local Abbreviation SEC_T_art_mmapfixed_pre_fn := (ltac2:(TCodec.tc2 tcn__JbtMmapFixed "W1&7y5'Q9yR0%211%5241'0y8%611%311p061'5'3&@r;(Q7+1(1%33A21%6251r8%93A21r<+2%93G17%<231&Q8%12H7%@3H31r=+:%@3N1>%C231%E3M16r>+;%E3Q31C%H231%J3Q21;r?+<%J3Q81H%M231%O3Q71@r@+=%O3Q=1M%Q2231%Q43Q<1E&G+Vb\P0&K+[@%22H1%5241&H&J+Q?%22Q31%42I1'2z%=21L%3214&I+TP0%22K1%QG3QH16%C27M%>2N;%:221%72K6%QL3QM1;%H2<M+R0%C2QD1%E2Q01%A241%G2AQ2%C213+RPP0%Q021Q5&ErA+`0%3221%O21Q4%Q62J4+X0%Q2261%N231&FrB%221R=%RB3RC1Q1&;&DrLrI%Q@21Q?%54431Q@&:rM+QV`l0u8+QiaW0%55:4321rN%75<134Q;rO+QV`l@rG%;5@3281rQ0rH+X4%Q2221u1%A5F5217'<&AvNrQ2+adh<%S=3SI1S;/01SIrQ1%756521>&B+admH%S82SO1%339SA1+S0%RB2J1%S<2T31%734S?1+8%SJ3T81SH%S@2T7Q9%;3421+9%SN3T<1SLrK%SE2T<1%@3531%SG2T>Q;%B32SC1%C31S?9+3%SK2TB1%F33S=1+QB%SN2TE1%I33S;1+>%T<3TJ1T:+_oooooooooooO%T32TJ1%N3531+?%TA3TO1T?%T72TNS4%Q23421+A%TE3U31TC+VN%T<2U31%Q73531+B%TJ3U81TH%Q:331I+C%TM3U;1TKrJ%TD2U;1%Q?3531+D%U23U@1U0%TH2U?R9%QC3421+E%U63UD1U4%U92QL1%QG3421+a]_H%U:3UF1U8/01UF&>%18QNRAR?R2RFRKQ>?%R55R4631R<%R73RNQO1p0R91p0R@1p0RE1p0RH1p0RO1p0S61p0S;1p0S@1p0SF1p0SI1p0SL1p0T21p0T51p0T91p0T>1p0TC1p0TI1p0U01p0U61p0U<1p0UB1p0UH1p0V01pQLV;1p>V<1pR0V=1pRHV>1pR>V?1pQJV@1pR<VA1pR4VI1pR:VD1pBVE1pR6VK1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_pre_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_pre_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_pre_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_pre_fn) 3%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_pre_fn) 4%nat 0%nat).
Variable addr : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_pre_fn) 5%nat 0%nat).
Variable size : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_pre_fn) 6%nat 0%nat).
Variable tol : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_pre_fn) 7%nat 0%nat).
Variable name : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_pre_fn) 8%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_pre_fn) 9%nat 0%nat).
Variable fb : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_pre_fn) 10%nat 0%nat).
Lemma art_mmapfixed_pre_fn : ltac:(sec_stmt2 constr:(SEC_T_art_mmapfixed_pre_fn) 11%nat 0%nat).
Proof using Type regs M rom raw s addr size tol name F fb.
intros H1 H2 H10 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Htol Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
unfold art_mmapfixed_mem.
zstep (ltac:(oF' 0x8d30c%Z)) (ltac:(oD' 0x8d30c%Z)).
zsd (ltac:(oF' 0x8d310%Z)) (ltac:(oD' 0x8d310%Z)) (s - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x8d314%Z)) (ltac:(oD' 0x8d314%Z)) (s - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x8d318%Z)) (ltac:(oD' 0x8d318%Z)) (s - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x8d31c%Z)) (ltac:(oD' 0x8d31c%Z)) (s - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x8d320%Z)) (ltac:(oD' 0x8d320%Z)) (s - 40) (U (getr regs 19)) ltac:(rewok W).
zsd (ltac:(oF' 0x8d324%Z)) (ltac:(oD' 0x8d324%Z)) (s - 48) (U (getr regs 20)) ltac:(rewok W).
zstep (ltac:(oF' 0x8d328%Z)) (ltac:(oD' 0x8d328%Z)). zstep (ltac:(oF' 0x8d32c%Z)) (ltac:(oD' 0x8d32c%Z)). zstep (ltac:(oF' 0x8d330%Z)) (ltac:(oD' 0x8d330%Z)).
zstep (ltac:(oF' 0x8d334%Z)) (ltac:(oD' 0x8d334%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg28' : cellA X 0x134380 8 0x1cc4e0) by zcell; assert (Cpc' : cellA X 0x1cc4e0 8 4096) by zcell end.
zld (ltac:(oF' 0x8d338%Z)) (ltac:(oD' 0x8d338%Z)) 0x134380 Cg28'. zld (ltac:(oF' 0x8d33c%Z)) (ltac:(oD' 0x8d33c%Z)) 0x1cc4e0 Cpc'.
zstep (ltac:(oF' 0x8d340%Z)) (ltac:(oD' 0x8d340%Z)).
zbtk (ltac:(oF' 0x8d344%Z)) (ltac:(oD' 0x8d344%Z)).
zstep (ltac:(oF' 0x8d354%Z)) (ltac:(oD' 0x8d354%Z)). zstep (ltac:(oF' 0x8d358%Z)) (ltac:(oD' 0x8d358%Z)).
zbft (ltac:(oF' 0x8d35c%Z)) (ltac:(oD' 0x8d35c%Z)).
zstep (ltac:(oF' 0x8d360%Z)) (ltac:(oD' 0x8d360%Z)). zstep (ltac:(oF' 0x8d364%Z)) (ltac:(oD' 0x8d364%Z)). zstep (ltac:(oF' 0x8d368%Z)) (ltac:(oD' 0x8d368%Z)).
pose proof (mf_roundup_id size ltac:(lia) Hszl) as RU.
stepn (ltac:(oF' 0x8d36c%Z)) (ltac:(oD' 0x8d36c%Z)). rwH.
replace (size + 4096 + -1) with (size + 4095) by lia.
rewrite art_zb_and by lia. change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
rewrite RU. replace (size + 4095 - 4095) with size by lia.
zbtk (ltac:(oF' 0x8d370%Z)) (ltac:(oD' 0x8d370%Z)).
stepn (ltac:(oF' 0x8d380%Z)) (ltac:(oD' 0x8d380%Z)). rwH. rewrite art_zb_and by lia.
change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
rewrite Hal, Z.sub_0_r.
zstep (ltac:(oF' 0x8d384%Z)) (ltac:(oD' 0x8d384%Z)).
zsw (ltac:(oF' 0x8d388%Z)) (ltac:(oD' 0x8d388%Z)) (s - 96) 50 ltac:(rewok W).
zstep (ltac:(oF' 0x8d38c%Z)) (ltac:(oD' 0x8d38c%Z)). zstep (ltac:(oF' 0x8d390%Z)) (ltac:(oD' 0x8d390%Z)). zstep (ltac:(oF' 0x8d394%Z)) (ltac:(oD' 0x8d394%Z)).
stepn (ltac:(oF' 0x8d398%Z)) (ltac:(oD' 0x8d398%Z)).
zstep (ltac:(oF' 0x8d9a0%Z)) (ltac:(oD' 0x8d9a0%Z)).
zsd (ltac:(oF' 0x8d9a4%Z)) (ltac:(oD' 0x8d9a4%Z)) (s - 104) 0x8d39c ltac:(rewok W).
zsd (ltac:(oF' 0x8d9a8%Z)) (ltac:(oD' 0x8d9a8%Z)) (s - 112) size ltac:(rewok W).
zsd (ltac:(oF' 0x8d9ac%Z)) (ltac:(oD' 0x8d9ac%Z)) (s - 120) tol ltac:(rewok W).
zsd (ltac:(oF' 0x8d9b0%Z)) (ltac:(oD' 0x8d9b0%Z)) (s - 128) addr ltac:(rewok W).
zsd (ltac:(oF' 0x8d9b4%Z)) (ltac:(oD' 0x8d9b4%Z)) (s - 136) name ltac:(rewok W).
zsd (ltac:(oF' 0x8d9b8%Z)) (ltac:(oD' 0x8d9b8%Z)) (s - 144) 0x1cc4e0 ltac:(rewok W).
zsd (ltac:(oF' 0x8d9bc%Z)) (ltac:(oD' 0x8d9bc%Z)) (s - 152) (U (getr regs 21)) ltac:(rewok W).
zstep (ltac:(oF' 0x8d9c0%Z)) (ltac:(oD' 0x8d9c0%Z)).
zstep (ltac:(oF' 0x8d9c4%Z)) (ltac:(oD' 0x8d9c4%Z)).
zbft (ltac:(oF' 0x8d9c8%Z)) (ltac:(oD' 0x8d9c8%Z)).
zstep (ltac:(oF' 0x8d9cc%Z)) (ltac:(oD' 0x8d9cc%Z)).
stepn (ltac:(oF' 0x8d9d0%Z)) (ltac:(oD' 0x8d9d0%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38c : cellA X 0x134390 8 F) by zcell; assert (Cflc : cellA X (F + 260) 1 fb) by zcell end.
zld (ltac:(oF' 0x8d9d4%Z)) (ltac:(oD' 0x8d9d4%Z)) 0x134390 C38c.
zlbu (ltac:(oF' 0x8d9d8%Z)) (ltac:(oD' 0x8d9d8%Z)) (F + 260) Cflc.
stepn (ltac:(oF' 0x8d9dc%Z)) (ltac:(oD' 0x8d9dc%Z)). rwH. rewrite art_zb_andi by lia. rewrite Hfb1.
zbtk (ltac:(oF' 0x8d9e0%Z)) (ltac:(oD' 0x8d9e0%Z)).
stepn (ltac:(oF' 0x8daf0%Z)) (ltac:(oD' 0x8daf0%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (R1 : cellA X (s - 104) 8 0x8d39c) by zcell; assert (R2 : cellA X (s - 112) 8 size) by zcell;
assert (R3 : cellA X (s - 120) 8 tol) by zcell; assert (R4 : cellA X (s - 128) 8 addr) by zcell;
assert (R5 : cellA X (s - 136) 8 name) by zcell; assert (R6 : cellA X (s - 144) 8 0x1cc4e0) by zcell;
assert (R7 : cellA X (s - 152) 8 (U (getr regs 21))) by zcell; assert (R8 : cellA X (s - 96) 4 50) by zcell end.
zld (ltac:(oF' 0x8daf4%Z)) (ltac:(oD' 0x8daf4%Z)) (s - 104) R1. zld (ltac:(oF' 0x8daf8%Z)) (ltac:(oD' 0x8daf8%Z)) (s - 112) R2. zld (ltac:(oF' 0x8dafc%Z)) (ltac:(oD' 0x8dafc%Z)) (s - 120) R3. zld (ltac:(oF' 0x8db00%Z)) (ltac:(oD' 0x8db00%Z)) (s - 128) R4.
zld (ltac:(oF' 0x8db04%Z)) (ltac:(oD' 0x8db04%Z)) (s - 136) R5. zld (ltac:(oF' 0x8db08%Z)) (ltac:(oD' 0x8db08%Z)) (s - 144) R6. zld (ltac:(oF' 0x8db0c%Z)) (ltac:(oD' 0x8db0c%Z)) (s - 152) R7. rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x8db10%Z)) (ltac:(oD' 0x8db10%Z)).
stepret (ltac:(oF' 0x8db14%Z)) (ltac:(oD' 0x8db14%Z)) (Z_to_bv 64 0x8d39c : word) ltac:(rwH; reflexivity).
zlw (ltac:(oF' 0x8d39c%Z)) (ltac:(oD' 0x8d39c%Z)) (s - 96) R8.
zstep (ltac:(oF' 0x8d3a0%Z)) (ltac:(oD' 0x8d3a0%Z)). zstep (ltac:(oF' 0x8d3a4%Z)) (ltac:(oD' 0x8d3a4%Z)). zstep (ltac:(oF' 0x8d3a8%Z)) (ltac:(oD' 0x8d3a8%Z)). zstep (ltac:(oF' 0x8d3ac%Z)) (ltac:(oD' 0x8d3ac%Z)). zstep (ltac:(oF' 0x8d3b0%Z)) (ltac:(oD' 0x8d3b0%Z)).
stepn (ltac:(oF' 0x8d3b4%Z)) (ltac:(oD' 0x8d3b4%Z)).
zstep (ltac:(oF' 0x8b5f4%Z)) (ltac:(oD' 0x8b5f4%Z)).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_mmapfixed_mem_agree : ltac2:(TCodec.tc2 tcn__JbtMmapFixed "QL'Q9yR0%211'0y8%511%311p051'5&7y5%2219&G+Vb\P0&Kr7+[@%3221%6251&Hr8&J+2+Q?%3221%6251&4'2r:%?21=&Q:r1%22O1%E241%?226%8221%:11'3&>r<r;r9r6r5r2%7965A4IN321%712%:3Q921p0<1pRJQ?1p0I1p0Q11pR0Q<1pRHQ=1pR>Q>1pQJQ?1pR8Q=1pR4QG1pR<QB1pBQD1").
Proof.
intros M s raw rg addr size tol name Hs Hs' x Y. unfold art_mmapfixed_mem.
do 14 (rewrite Wn_outside; [ | lia | cbn; lia | cbn; lia ]). reflexivity.
Qed.
#[using="Type"] Lemma art_mmapfixed_mem_grows : ltac2:(TCodec.tc2 tcn__JbtMmapFixed "Q0'Q9yR0%211'0y8%511%311p051'5&7y5%2219&Cr8&>r7r6r5r4r3r2r1%8897654321%;2:1pR0@1pRHA1pR>B1pQJC1pR8A1pR4K1pR<F1pBH1").
Proof.
intros. unfold art_mmapfixed_mem. do 14 (eapply mem_grows_trans; [ | apply Wn_grows ]). apply mem_grows_refl.
Qed.
#[using="Type"] Lemma art_mmapfixed_mem_cells : ltac2:(TCodec.tc2 tcn__JbtMmapFixed "RO'Q9yR0%211'0y8%511%311p051'5&7y5%2219&G+Vb\P0&Kr7+[@%3221%6251&Hr8&J+2+Q?%3221%6251'2&:&D&>r:r9r6r5r4r3%7865@E4321+8%H271u8&Q:%12Q8E%?5>6431+@%N2=1&@(Q7(1%23Q6;1%42Q21%:2QA1%H5G?7<1+H%Q72F1+9%93Q=18%;2Q91%A2QH1%O5NF5C1+Q0%Q>2M1+B%@3QD1?%B2Q@1%H2QO1%Q65Q5M5J1+Q8%QE2Q41+C%G3QK1F%I2QG1%O2R61%Q=5Q<Q45Q11+Q@%QL2Q;1+D%N3R21M%Q02QN1%Q62R=1%QD5QCQ;5Q81%QF281%QG2@1%QH2H1%QI2Q01%QJ2Q:1p0QL1p0R41pR0R?1pRHR@1pR>RA1pQJRB1pR8R@1pR4RJ1pR<RE1pBRG1").
Proof.
intros M s raw rg addr size tol name Hs Hs'. unfold art_mmapfixed_mem. repeat split; zcell.
Qed.
Definition art_map_frame (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 M (s - 8) (U raw)) (s - 16) (U (getr rg 8))) (s - 24) (U (getr rg 9))) (s - 32) (U (getr rg 18)).
Definition art_rar_map_mem (M : word -> option byte) (s : Z) (raw : word) (rg : bvmap 5 word) (addr size name : Z) : word -> option byte :=
art_mmapfixed_mem (art_map_frame M s raw rg) (s - 32) (0x95570 : bv 64)%bv (regupd (regupd rg 8 (Z_to_bv 64 size)) 9 (Z_to_bv 64 addr)) addr size 1 name.
Section SE.
Local Abbreviation SEC_T_art_rar_map_pre_fn := (ltac2:(TCodec.tc2 tcn__JbtMmapFixed "VG&7y5'Q9yR0%211%5241'0y8%611%311p061'5'3&@r:(Q7+1(1%33A21%6251r7%93A21r;+2%93G17%<231&Q8%12H7%@3H31r<+;%@3N1>%C231%E3M16r=+<%E3Q31C%H231%J3Q21;r>+=%J3Q81H%M231%O3Q71@&G+Vb\P0&K+\@%22J1%5241&H&J+Q?%22N1%42I1'2z%=21L%3214&I+TP0%22K1%QB3QC16%C27M%>2N;%:221%72K6%QG3QH1;%B2<M+R0%C2Q?1%E2Q01%A241+RPP0%N21Q3&Er?+`0%3221%M21Q2%Q42H4+X0%Q0261%L231&Fr@%221R6%R;3R<1O&;&DrIrF%Q>21Q=%54431Q>&:rJ+QV`l0u8+QiaW0%55:4321rK%75<134Q9rL+QV`l@rE%;5@3281rM+X4%Q12A1u1%@5E4216'<&AvNrO+beZ4%S53SA1S3/01SArN%756521=&B+admH%S02SG1%339S91+T0%R?2I1%S42SK1%734S71+8%SB3T01S@%S82SOQ8%;3421+9%SF3T41SD%S<2T3SF%?3421+:%SJ3T81SH%S@2T7Q;%C3421%D31S=:+3%SD2T;1%G33S;1+QB%SG2T>1%J33S91+>%T53TC1T3+_oooooooooooO%SL2TC1%O3531+?%T:3TH1T8%T02TGS2%Q33421+A%T>3TL1T<+VN%T52TL1%Q83531+B%TC3U11TA%Q;331I+C%TF3U41TDrH%T=2U41%Q@3531+D%TK3U91TI%TA2U8R9%QD3421+E%TO3U=1TM%U22QM1%QH3421+a]_H%U33U?1U1/01U?&?%17QORAR?R3RFRK?%R65R5631R<%R83RNR01p0R:1p0R@1p0RE1p0RH1p0RO1p0S61p0S;1p0S@1p0SF1p0SI1p0SO1p0T21p0T61p0T;1p0T@1p0TF1p0TM1p0U31p0U91p0U?1p0UG1pQLV21p>V31pR0V41pR>V51pQJV61pR<V71pR4V?1pR:V:1pBV;1pR6VA1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_rar_map_pre_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_rar_map_pre_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_rar_map_pre_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_rar_map_pre_fn) 3%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_art_rar_map_pre_fn) 4%nat 0%nat).
Variable addr : ltac:(sec_ty2 constr:(SEC_T_art_rar_map_pre_fn) 5%nat 0%nat).
Variable size : ltac:(sec_ty2 constr:(SEC_T_art_rar_map_pre_fn) 6%nat 0%nat).
Variable name : ltac:(sec_ty2 constr:(SEC_T_art_rar_map_pre_fn) 7%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_art_rar_map_pre_fn) 8%nat 0%nat).
Variable fb : ltac:(sec_ty2 constr:(SEC_T_art_rar_map_pre_fn) 9%nat 0%nat).
Lemma art_rar_map_pre_fn : ltac:(sec_stmt2 constr:(SEC_T_art_rar_map_pre_fn) 10%nat 0%nat).
Proof using Type regs M rom raw s addr size name F fb.
intros H1 H2 H11 H12 H13 Hs Hs' Ha Hal Hsz Hszl Hnm HF HF' Hfb Hfb1 W Cg28 Cpc Cg38 Cfl.
unfold art_rar_map_mem, art_map_frame.
zstep (ltac:(oF' 0x95544%Z)) (ltac:(oD' 0x95544%Z)).
zsd (ltac:(oF' 0x95548%Z)) (ltac:(oD' 0x95548%Z)) (s - 8) (U raw) ltac:(rewok W).
zsd (ltac:(oF' 0x9554c%Z)) (ltac:(oD' 0x9554c%Z)) (s - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x95550%Z)) (ltac:(oD' 0x95550%Z)) (s - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x95554%Z)) (ltac:(oD' 0x95554%Z)) (s - 32) (U (getr regs 18)) ltac:(rewok W).
zstep (ltac:(oF' 0x95558%Z)) (ltac:(oD' 0x95558%Z)). zstep (ltac:(oF' 0x9555c%Z)) (ltac:(oD' 0x9555c%Z)).
zstep (ltac:(oF' 0x95560%Z)) (ltac:(oD' 0x95560%Z)). zstep (ltac:(oF' 0x95564%Z)) (ltac:(oD' 0x95564%Z)). zstep (ltac:(oF' 0x95568%Z)) (ltac:(oD' 0x95568%Z)).
stepn (ltac:(oF' 0x9556c%Z)) (ltac:(oD' 0x9556c%Z)).
zstep (ltac:(oF' 0x8d484%Z)) (ltac:(oD' 0x8d484%Z)). zstep (ltac:(oF' 0x8d488%Z)) (ltac:(oD' 0x8d488%Z)).
stepn (ltac:(oF' 0x8d48c%Z)) (ltac:(oD' 0x8d48c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (GX : mem_grows M X) by (do 4 (eapply mem_grows_trans; [ | apply Wn_grows ]); apply mem_grows_refl);
assert (WX : wrA X (s - 32 - 368) 368) by (eapply wr_grows; [exact GX | eapply wr_sub; [exact W|lia|lia]]);
assert (Cg28' : cellA X 0x134380 8 0x1cc4e0) by zcell; assert (Cpc' : cellA X 0x1cc4e0 8 4096) by zcell;
assert (Cg38' : cellA X 0x134390 8 F) by zcell; assert (Cfl' : cellA X (F + 260) 1 fb) by zcell end.
zcall (art_mmapfixed_pre_fn _ _ rom (0x95570 : bv 64)%bv (s - 32) addr size 1 name F fb).
unfold art_mmapfixed_mem. gres.
zret.
Qed.
End SE.
#[using="Type"] Lemma art_rar_map_mem_agree : ltac2:(TCodec.tc2 tcn__JbtMmapFixed "QJ'Q9yR0%211'0y8%511%311p051'5&7y5%2219&G+Vb\P0&Kr6+\@%3221%6251&Hr7&J+2+Q?%3221%6251&4'2r9%?21=&Q:r1%22O1%E241%?226%8221%:11'3&?r;r:r8r5r2%6854@3HM21%612%93Q821p0;1pRJQ>1p0H1p0Q01pR0Q;1pR>Q<1pQJQ=1pR8Q;1pR4QE1pR<Q@1pBQB1").
Proof.
intros M s raw rg addr size name Hs Hs' x Y. unfold art_rar_map_mem. rewrite art_mmapfixed_mem_agree by lia.
unfold art_map_frame. do 4 (rewrite Wn_outside; [ | lia | cbn; lia | cbn; lia ]). reflexivity.
Qed.
#[using="Type"] Lemma art_rar_map_mem_grows : ltac2:(TCodec.tc2 tcn__JbtMmapFixed "N'Q9yR0%211'0y8%511%311p051'5&7y5%2219&Cr7&?r6r5r4r3r2r1%778654321%:291pR0?1pR>@1pQJA1pR8?1pR4I1pR<D1pBF1").
Proof.
intros. unfold art_rar_map_mem. eapply mem_grows_trans; [ | apply art_mmapfixed_mem_grows ].
unfold art_map_frame. do 4 (eapply mem_grows_trans; [ | apply Wn_grows ]). apply mem_grows_refl.
Qed.
Section SE.
Variables (M : word -> option byte).
Variables (s : Z).
Variables (raw : word).
Variables (rg : bvmap 5 word).
Variables (addr size name : Z).
Lemma art_rar_map_mem_cells : 0x693000 <= s - 400 -> s < 2 ^ 47 -> 0 <= addr < 2 ^ 64 -> 0 <= size < 2 ^ 64 ->
cellA (art_rar_map_mem M s raw rg addr size name) (s - 8) 8 (U raw) /\
cellA (art_rar_map_mem M s raw rg addr size name) (s - 16) 8 (U (getr rg 8)) /\
cellA (art_rar_map_mem M s raw rg addr size name) (s - 24) 8 (U (getr rg 9)) /\
cellA (art_rar_map_mem M s raw rg addr size name) (s - 32) 8 (U (getr rg 18)) /\
cellA (art_rar_map_mem M s raw rg addr size name) (s - 40) 8 (U (0x95570 : bv 64)%bv) /\
cellA (art_rar_map_mem M s raw rg addr size name) (s - 48) 8 size /\
cellA (art_rar_map_mem M s raw rg addr size name) (s - 56) 8 addr /\
cellA (art_rar_map_mem M s raw rg addr size name) (s - 64) 8 (U (getr rg 18)) /\
cellA (art_rar_map_mem M s raw rg addr size name) (s - 72) 8 (U (getr rg 19)) /\
cellA (art_rar_map_mem M s raw rg addr size name) (s - 80) 8 (U (getr rg 20)).
Proof using Type M s raw rg addr size name.
intros Hs Hs' Ha Hsz.
unfold art_rar_map_mem, art_mmapfixed_mem, art_map_frame. gres.
rewrite ?art_u_lit by lia. repeat split.
- zcell.
- zcell.
- zcell.
- zcell.
- replace (s - 40) with (s - 32 - 8) by lia; zcell.
- replace (s - 48) with (s - 32 - 16) by lia; zcell.
- replace (s - 56) with (s - 32 - 24) by lia; zcell.
- replace (s - 64) with (s - 32 - 32) by lia; zcell.
- replace (s - 72) with (s - 32 - 40) by lia; zcell.
- replace (s - 80) with (s - 32 - 48) by lia; zcell.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_mmapfixed_post_fn := (ltac2:(TCodec.tc2 tcn__JbtMmapFixed "V<&7y5'Q9yR0%211%5241'0y8%611%311p061'5'3&@r=(Q7+1(1%33A21%6251&Q8+admH%22C1%;3C41r>+2%;3I19%>231&Kr5+S0%3221%<2M1%E3M61r?+8%E3Q31C%H231%B2Q39%K3Q321r@+:%K3Q91I%N231%Q03Q816&=%11F&G+Vb\P0r9+[@%G221%5241&Hr:&J+Q?%22Q01%5241'2z%>217%3214+R0%92Q71+SoO%Q6221%>2=1%9271+RPP0%G21@&Er;+`0%3221%F21K&;&DrG%QC2Q=M%44321N&:rH%QG2Q;Q@u8&Q:rF%22RD1%75;6541rIrA+@%R0221%<5@4196rJrB+H%R5221%A5E41>;rKrC+Q0%R:221%F5J41C@rLrD+Q8%R?221%K5O41HErMrE+Q@%RD221%Q05Q441MJrN+QV`l@%Q35Q721Q0@rO+T@%Q@2>1%Q75Q;31Q4QL'<&AvNrQ1+a]_L%S?3SK1S=/01SKrQ0%756521<&B%137SAA%S@2T1QB%332S;1%431S2I+9%SI3T71SG%7331Q1%SF2T7QD%932S11+;%SN3T<1SL%SJ2T;RB%=3421+<%T23T@1T0+_ooooooooolP0%SO2T@1%B3531+=%T73TE1T5+_ooooooooolP1%T42TE1%G3531+B%T<3TJ1T:%J331QI+C%T?3TM1T=%M331R1+D%TB3U01T@%Q0331R9&9u4+QD%T:2RD1+_oooooneZeZe:%544Q821%Q?5Q>7QG1QD%QA3RMQ91p0QC1p0QH1p0QL1p0R21p0R81p0R>1p0RD1p0RJ1p0S31p0S91p0S?1p0SB1p0SI1p0SN1p0T51p0T<1p0T?1p0TE1p0TL1p0U71p>UD1pR2UE1pR>UF1pR<UG1pS2UO1pS0V01pRNV11pS6V21pS4V31pRLV41pR:UO1pBV01pR6V61")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_post_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_post_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_post_fn) 2%nat 0%nat).
Variable x1 : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_post_fn) 3%nat 0%nat).
Variable x8 : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_post_fn) 4%nat 0%nat).
Variable x9 : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_post_fn) 5%nat 0%nat).
Variable x18 : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_post_fn) 6%nat 0%nat).
Variable x19 : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_post_fn) 7%nat 0%nat).
Variable x20 : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_post_fn) 8%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_post_fn) 9%nat 0%nat).
Variable size : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_post_fn) 10%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_post_fn) 11%nat 0%nat).
Variable F : ltac:(sec_ty2 constr:(SEC_T_art_mmapfixed_post_fn) 12%nat 0%nat).
Lemma art_mmapfixed_post_fn : ltac:(sec_stmt2 constr:(SEC_T_art_mmapfixed_post_fn) 13%nat 0%nat).
Proof using Type regs M rom x1 x8 x9 x18 x19 x20 s size q F.
intros H1 H2 H8 H10 Hret Hs Hs' Hsz Hq HF HF' W L1 L2 L3 L4 L5 L6 C38 C144.
stepret (ltac:(oF' 0x8b5fc%Z)) (ltac:(oD' 0x8b5fc%Z)) (Z_to_bv 64 0x8d3b8 : word) ltac:(rwH; reflexivity).
zstep (ltac:(oF' 0x8d3b8%Z)) (ltac:(oD' 0x8d3b8%Z)).
zstep (ltac:(oF' 0x8d3bc%Z)) (ltac:(oD' 0x8d3bc%Z)).
stepn (ltac:(oF' 0x8d3c0%Z)) (ltac:(oD' 0x8d3c0%Z)).
zstep (ltac:(oF' 0x8b5d4%Z)) (ltac:(oD' 0x8b5d4%Z)). zstep (ltac:(oF' 0x8b5d8%Z)) (ltac:(oD' 0x8b5d8%Z)).
zbtk (ltac:(oF' 0x8b5dc%Z)) (ltac:(oD' 0x8b5dc%Z)).
zstep (ltac:(oF' 0x8b5ec%Z)) (ltac:(oD' 0x8b5ec%Z)).
stepret (ltac:(oF' 0x8b5f0%Z)) (ltac:(oD' 0x8b5f0%Z)) (Z_to_bv 64 0x8d3c4 : word) ltac:(rwH; reflexivity).
zstep (ltac:(oF' 0x8d3c4%Z)) (ltac:(oD' 0x8d3c4%Z)). zstep (ltac:(oF' 0x8d3c8%Z)) (ltac:(oD' 0x8d3c8%Z)).
zsw (ltac:(oF' 0x8d3cc%Z)) (ltac:(oD' 0x8d3cc%Z)) (s - 52) 18446744072277895850 ltac:(rewok W).
zstep (ltac:(oF' 0x8d3d0%Z)) (ltac:(oD' 0x8d3d0%Z)). zstep (ltac:(oF' 0x8d3d4%Z)) (ltac:(oD' 0x8d3d4%Z)).
stepn (ltac:(oF' 0x8d3d8%Z)) (ltac:(oD' 0x8d3d8%Z)).
zstep (ltac:(oF' 0x8b5d4%Z)) (ltac:(oD' 0x8b5d4%Z)). zstep (ltac:(oF' 0x8b5d8%Z)) (ltac:(oD' 0x8b5d8%Z)).
zbtk (ltac:(oF' 0x8b5dc%Z)) (ltac:(oD' 0x8b5dc%Z)).
zstep (ltac:(oF' 0x8b5ec%Z)) (ltac:(oD' 0x8b5ec%Z)).
stepret (ltac:(oF' 0x8b5f0%Z)) (ltac:(oD' 0x8b5f0%Z)) (Z_to_bv 64 0x8d3dc : word) ltac:(rwH; reflexivity).
zbft (ltac:(oF' 0x8d3dc%Z)) (ltac:(oD' 0x8d3dc%Z)).
zstep (ltac:(oF' 0x8d3e0%Z)) (ltac:(oD' 0x8d3e0%Z)).
stepn (ltac:(oF' 0x8d3e4%Z)) (ltac:(oD' 0x8d3e4%Z)).
zstep (ltac:(oF' 0x874bc%Z)) (ltac:(oD' 0x874bc%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38' : cellA X 0x134390 8 F) by zcell; assert (C144' : cellA X (F + 144) 8 0) by zcell end.
zld (ltac:(oF' 0x874c0%Z)) (ltac:(oD' 0x874c0%Z)) 0x134390 C38'. zld (ltac:(oF' 0x874c4%Z)) (ltac:(oD' 0x874c4%Z)) (F + 144) C144'.
zbtk (ltac:(oF' 0x874c8%Z)) (ltac:(oD' 0x874c8%Z)).
stepret (ltac:(oF' 0x874e4%Z)) (ltac:(oD' 0x874e4%Z)) (Z_to_bv 64 0x8d3e8 : word) ltac:(rwH; reflexivity).
zstep (ltac:(oF' 0x8d3e8%Z)) (ltac:(oD' 0x8d3e8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (R1 : cellA X (s - 8) 8 (U x1)) by zcell; assert (R2 : cellA X (s - 16) 8 (U x8)) by zcell; assert (R3 : cellA X (s - 24) 8 (U x9)) by zcell;
assert (R4 : cellA X (s - 32) 8 (U x18)) by zcell; assert (R5 : cellA X (s - 40) 8 (U x19)) by zcell; assert (R6 : cellA X (s - 48) 8 (U x20)) by zcell end.
zld (ltac:(oF' 0x8d3ec%Z)) (ltac:(oD' 0x8d3ec%Z)) (s - 8) R1; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x8d3f0%Z)) (ltac:(oD' 0x8d3f0%Z)) (s - 16) R2; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x8d3f4%Z)) (ltac:(oD' 0x8d3f4%Z)) (s - 24) R3; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x8d3f8%Z)) (ltac:(oD' 0x8d3f8%Z)) (s - 32) R4; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x8d3fc%Z)) (ltac:(oD' 0x8d3fc%Z)) (s - 40) R5; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x8d400%Z)) (ltac:(oD' 0x8d400%Z)) (s - 48) R6; rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x8d404%Z)) (ltac:(oD' 0x8d404%Z)).
stepret (ltac:(oF' 0x8d408%Z)) (ltac:(oD' 0x8d408%Z)) x1 ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_rar_map_post_fn : ltac2:(TCodec.tc2 tcn__JbtMmapFixed "W<&7y5'Q9yR0%211%5241'0y8%611%311p061'5'3&@r>(Q7+1(1%33A21%6251&Q8+admH%22C1%;3C41r?+2%;3I19%>231&Kr6+T0%3221%<2M1%E3M61r@+8%E3Q31C%H231%B2Q39%K3Q321rA+:%K3Q91I%N231r5%I2Q:1%Q23Q:31&=%11H&G+Vb\P0r:+\@%I221%5241&Hr;&J+Q?%22Q21%5241'2z%>217%3214+R0%92Q91%<2;1%7251%>27=+SoO%Q;251%A2@1%<241+RPP0%J21C&Er<+`0%3221%I21N&;&DrI%QH2Q<Q0%44321Q1&:rJrB%QM21QFu8&Q:rH%22RJ1%85<7541rKrC+@%R6221%=5A4196rLrD+H%R;221%B5F41>;rMrE+Q0%R@221%G5K41C@rNrF+Q8%RE221+be[@%S43S@1S2/01S@%J2SB1%Q05Q485L1rOrG+Q@%RN221%Q55Q941Q1<rQ0+QH%S22Q21%Q95Q=31Q5@rQ1%S52Q>R0%Q72SON%Q=5QA32Q91rQ2+R8%S:2Q?1%QA5QE31Q=5rQ3+R@%S>2Q;1%QE5QI31QA9rQ4+QV`l@%QH5QL21QDQBrQ5+T@%R52QN1%QL5R031QHRD'<&AvNrQ7+a]_L%T93TE1T7/01TErQ6%756521<&B%137T;A%T:2TKQ@%332T51%431SLH+9%TC3U11TA%7331O%T@2U1R5%932SK1+;%TH3U61TF%TD2U5S:%=3421+<%TL3U:1TJ+_ooooooooolP0%TI2U:1%B3531+=%U13U?1TO+_ooooooooolP1%TN2U?1%G3531+B%U63UD1U4%J331QF+C%U93UG1U7%M331QM+D%U<3UJ1U:%Q0331R5&9u4+RD%U42RB1+_oooooneZeZe:%544Q821%Q?5Q>7QG1QD%QA3SBQ91p0QC1p0QH1p0QL1p0R11p0R61p0R;1p0R@1p0RF1p0S01p0S61p0S<1p0SB1p0SL1p0T21p0T81p0T;1p0TA1p0TF1p0TK1p0U21p0U91p0U<1p0UD1p0UK1p0V61p>VC1pR2VD1pQJVE1pR>VF1pR<VG1pS2VO1pS0W01pRNW11pS6W21pS4W31pRLW41pR:VO1pBW01pR6W61").
Proof.
intros regs M rom x1 x8 x9 x18 x19 x20 s size addr q F H1 H2 H8 H10 Hret Hs Hs' Hsz Ha Hq HF HF' W L1 L2 L3 L4 K1 K8 K9 K18 K19 K20 C38 C144.
pose proof (art_mmapfixed_post_fn regs M rom (0x95570 : bv 64)%bv (Z_to_bv 64 size) (Z_to_bv 64 addr) x18 x19 x20 (s - 32) size q F
H1 ltac:(rewrite H2; f_equal; lia) H8 H10 ltac:(unfold ret_ok; bveq) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(eapply wr_sub; [exact W|lia|lia])
ltac:(replace (s - 32 - 8) with (s - 40) by lia; exact K1)
ltac:(replace (s - 32 - 16) with (s - 48) by lia; rewrite art_u_lit by lia; exact K8)
ltac:(replace (s - 32 - 24) with (s - 56) by lia; rewrite art_u_lit by lia; exact K9)
ltac:(replace (s - 32 - 32) with (s - 64) by lia; exact K18)
ltac:(replace (s - 32 - 40) with (s - 72) by lia; exact K19)
ltac:(replace (s - 32 - 48) with (s - 80) by lia; exact K20) C38 C144) as RUN1.
eapply msteps_trans; [exact RUN1|]. rnorm; norm_pc.
replace (s - 32 - 52) with (s - 84) by lia.
zbft (ltac:(oF' 0x95570%Z)) (ltac:(oD' 0x95570%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (R1 : cellA X (s - 8) 8 (U x1)) by zcell; assert (R2 : cellA X (s - 16) 8 (U x8)) by zcell;
assert (R3 : cellA X (s - 24) 8 (U x9)) by zcell; assert (R4 : cellA X (s - 32) 8 (U x18)) by zcell end.
zld (ltac:(oF' 0x95574%Z)) (ltac:(oD' 0x95574%Z)) (s - 8) R1; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x95578%Z)) (ltac:(oD' 0x95578%Z)) (s - 16) R2; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x9557c%Z)) (ltac:(oD' 0x9557c%Z)) (s - 24) R3; rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x95580%Z)) (ltac:(oD' 0x95580%Z)) (s - 32) R4; rewrite Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x95584%Z)) (ltac:(oD' 0x95584%Z)).
stepret (ltac:(oF' 0x95588%Z)) (ltac:(oD' 0x95588%Z)) x1 ltac:(rwH; reflexivity).
zret.
Qed.
End FPX.
