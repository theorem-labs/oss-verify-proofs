(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.GcFlush06.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import muslA.Jb0SumsMemset_code muslA.Jb0SumsMemset.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JbtPoison JbtPoisonRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtPoison2G () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison2G.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoisonRun."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "4bvmap"; "0M"; "5Wf"; "5apart"; "5wr"; "6msteps"; "7ret_ok"; "8SB"; "8art_layout"]; ["8art_poison_frame"; "8kHighMemBeg"; "8kHighMemEnd"; "9art_poison_hi_okG"; "9art_poison_lo_okG"; ":art_poison_kept"; ";getr"; ";mkst"; ";regupd"; "<loaded_segments"; "=add"; "=div"; "=le"; "=lt"; "=modulo"; "=pow"]; ["=sub"; "=to_nat"; "0fx"; "0n"; "0p"; "0r"; "0raw"; "0regs"; "0regs'"; "0rom"; "0sp"; ">BV"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0v"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_poison_hi0_fnG := (ltac2:(TCodec.tc2 tcn__JbtPoison2G "W9&7y5'Q=yR0%211%5241'0y8%611%311p061'6'3&Fr8(Q;+1(1%33A21%6251r5%93A21r9+2%93G17%<231&Q<%12H7%@3H31r:+:%@3N1>%C231%E3M16r;+;%E3Q31C%H231%J3Q21;r<+<%J3Q81H%M231%O3Q71@&L+R0%221H&M&O%12J4%32E1&;&Ir>&Q0%12E:%54431;&:%42C=+QV`QH+Q`P0%443@21r=%921B+Qii[8+X0%943E21&?rA%211&A%K21B&Jr?%221E&B%421QL%Q1231&Nr@+8%3221z%R73R821%Q822@%=2?5rCrB%@221%Q=241rD%Q?21@'2%QA2;7%Q?28M%3221%RD3RE6>&KrF%221C+_oooooooooooO%QF221p061'<&GvQ2rL+_YU@%RM3S91RK/01S9rKrJ%8576321&HrI%239S11rH%RK2SB1%533RN1+5%S93SG1S7&>%I2Q?Q:%QC221%S22SI1%<3751+6%S@3SN1S>+QTjo8%S72SN1%A3531+7%SE3T31SC%S;2T2QJ%E3421%SH3T6QGSF%SK2N1%H3321+9%SL3T:1SJ%SO2Q21%L3421rG%Q>21QO%R82G1%SG2T>1%Q135SC1rE%SJ2TA1%Q433SA1%SL2TCQC%Q632S>1+=%T:3TH1T8%T02TG;%Q:3421+>%T>3TL1T<%T42TKR<%Q>3421+?%TB3U01T@%T82TOQ8%QB3421+@%TF3U41TD%S@2SETF%T=2U41%QG3531+A%TK3U91TI%QJ331=+B%TN3U<1TL%U12R41%QN3421+C%U23U@1U0%U52R81%R23421+D%U63UD1U4%U92R<1%R63421+E%U:3UH1U8%U=2R@1%R:3421+L%U>3UL1U<%R=331QI%U@3ULQOU>/01UL&@&Q>%12V0RA%22V1QL%32V2QI%42V3H%52V4E%62V5B%72V6?%99RLRF7654321%S35S2=;1RL%S53THRL1p0S71p0S?1p0SD1p0SG1p0SM1p0SO1p0T01p0T71p0T>1p0TA1p0TE1p0TK1p0U11p0U81p0U=1p0UA1p0UG1p0UM1p0V31p0V;1pS0VF1pR8VG1pR:VH1pRFVI1pR>W11pRDVL1pBVM1pR@W31")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_fnG) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_fnG) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_fnG) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_fnG) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_fnG) 4%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_fnG) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_fnG) 6%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_fnG) 7%nat 0%nat).
Lemma art_poison_hi0_fnG : ltac:(sec_stmt2 constr:(SEC_T_art_poison_hi0_fnG) 8%nat 0%nat).
Proof using Type regs M rom raw sp p n v.
intros H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr.
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
Section SE.
Local Abbreviation SEC_T_art_poison_hi0_runG := (ltac2:(TCodec.tc2 tcn__JbtPoison2G "W<&7y5'Q=yR0%211%5241'0y8%611%311p061'6'3&Fr8(Q;+1(1%33A21%6251r5%93A21&=r6%211r:+2%<3J1:%?231&Q<%12K7%C3K31r;+:%C3Q11A%F231%H3Q016r<+;%H3Q61F%K231%M3Q51;r=+<%M3Q;1K%Q0231%Q23Q:1@&L+R0%221H&M&O%12J4%32E1&;&Ir?&Q0%12E:%54431;&:%42C=+QV`QH+Q`P0%443@21r>%921B+Qii[8+X0%943E21&?rB%211&A%K21B&Jr@%221E&B%421QO%Q1231&NrA+8%3221z%R:3R;21%Q822@%=2?5rDrC%@221%Q=241rE%Q?21@'2%QA2;7%Q?28M%3221%RG3RH6>&KrG%221C+_oooooooooooO%QF221p061rL&>rH%921J%Q3231%QI4QH519'4'<&GvQ2rO+_YU@%S73SC1S5/01SCrNrM%8576321r1&9&@rK&Q>%12SMF%SB3T0Q>S@%SE2>1%42T01+9%SF3T41SD%SI2B1%82T41+B%SJ3T81SH%SM2F1%<2T81+C%SN3T<1SL%T12J1%@2T<1+D%T23T@1T0%T52N1%D2T@1+E%T63TD1T4%T92Q21%H2TD1%K9Q0JHEA=951rJ%QF21R7%R@2Q@1&Q1rI%QJ21R;%311%Q44851QD%Q?5Q>Q6QG1Q8%QA3S;Q81%TF2Q8T1%T72U19%TI3U121%TI2Q;TD%TK3U31QM%TK2Q=T=%T<2U6Q;%TN3U621%TN2Q@Q:%U03U81Q:%U02QBQ8%U23U:1Q8%U22QDQ6%U43U<1Q6%U42QFQ4%U63U>1Q4%U62QHQ2%U83U@1Q2%U82QJQ0%U:3UB1Q0%UE1UF&E%11QNr3r2%U?221rQ1%UA213%UC3UK31p071pR<:1%S32<1%S42?1%S52B1%S62E1%S72H1%S82K1%S92N1%S:2Q21%S;2Q51%S<2Q91qRBV71%RM2V81p0RO1p0S61p0S>1p0SC1p0SF1p0SL1p0SN1p0SO1p0T61p0T=1p0T@1p0TD1p0TJ1p0U01p0U71p0U<1p0U@1p0UF1p0UL1p0V21p0V:1p0V>1pS0VI1pR8VJ1pR:VK1pRFVL1pR>W41pRDVO1pBW01pR@W61")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_runG) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_runG) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_runG) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_runG) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_runG) 4%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_runG) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_runG) 6%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_art_poison_hi0_runG) 7%nat 0%nat).
Theorem art_poison_hi0_runG : ltac:(sec_stmt2 constr:(SEC_T_art_poison_hi0_runG) 8%nat 0%nat).
Proof using Type regs M rom raw sp p n v.
intros H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr Wsh.
pose proof (art_poison_hi0_fnG regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr) as RUN1.
unfold kHighMemBeg, kHighMemEnd, SB in *.
match type of RUN1 with msteps _ _ (mkst ?R1 _ ?M1 _) =>
assert (OK : store_ok ASEGS M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z.to_nat (n / 8)) = true)
by (unfold art_poison_frame; apply wr_wok with (a := 2147450880 + p / 8) (n := n / 8); [|lia|lia]; repeat apply wr_Wn; exact Wsh);
destruct (memset_summary M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z_to_bv 64 v) raw (n / 8) rom
ltac:(lia) ltac:(rewrite art_u_lit by lia; lia) OK Hret R1
ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity))
as (r2 & RUN2 & P10 & AG)
end.
exists r2. split.
{ eapply msteps_trans; [exact RUN1|]. unfold Wf. rewrite cbyte_cbz in RUN2. unfold cbz in RUN2. rewrite art_u_lit in RUN2 by lia.
replace (v mod 256) with v in RUN2 by (symmetry; apply Z.mod_small; lia).
replace (Z_to_bv 64 ms_base) with (0x126be8 : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
cbn [ms_clob In] in K.
zsplit;
try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
rewrite K by (intuition congruence). kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_poison_lo_fnG := (ltac2:(TCodec.tc2 tcn__JbtPoison2G "V=&7y5'Q=yR0%211%5241'0y8%611%311p061'6'3&Fr8(Q;+1(1%33A21%6251r5%93A21r9+2%93G17%<231&Q<%12H7%@3H31r:+:%@3N1>%C231%E3M16r;+;%E3Q31C%H231%J3Q21;r<+<%J3Q81H%M231%O3Q71@&L+R0%221H&M&O%12J4%32E1&;&Ir>&Q0%12E:%54431;&:%42C=+QV`QH+Q`P0%443@21r=%921B+Qii[8+X0%943E21&?rA%211+8%K21B&Jr?%2214&>%Q0221r@%6215%Q3214&N%12=;z%R73R821rB%Q9231'2%Q823F%2231rC%R>3R?18&KrE%221G+_oooooooooooO%Q@221p061'<&GvQ2rK+_YU@%RG3S31RE/01S3rJrI%8576321&HrH%239RK1rG%RE2S<1%533RH1+6%S33SA1S1+QTjo8%RJ2SA1%:3531%S73SEQ@S5%S:2C1%=3321+9%S;3SI1S9%S>2G1%A3421rF%Q321QH%QG2QD1%S62SM1%F35S21rD%S92T01%I33S01%S;2T2Q8%K32RM1+=%SI3T71SG%S?2T6;%O3421+>%SM3T;1SK%RG2R2SM%SD2T;1%Q43531+?%T23T@1T0%SH2T?R0%Q83421+B%T63TD1T4%T92QB1%Q<3421+C%T:3TH1T8%T=2QF1%Q@3421+D%T>3TL1T<%TA2QJ1%QD3421+E%TB3U01T@%TE2QN1%QH3421%TE3U1QATC/01U1&@&Q>%12U5QL%22U6QB%32U7Q?%42U8E%52U9B%62U:?%72U;<%99R7R17654321%R>5R==;1R7%R@3SMR71p0RB1p0RK1p0RO1p0S21p0S31p0S81p0S<1p0SB1p0SE1p0SI1p0SO1p0T51p0T<1p0TA1p0TE1p0TK1p0U11p0U71p0U?1pS0UJ1pR8UK1pR:UL1pRFUM1pR>V51pRDV01pBV11pR@V71")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_fnG) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_fnG) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_fnG) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_fnG) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_fnG) 4%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_fnG) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_fnG) 6%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_fnG) 7%nat 0%nat).
Lemma art_poison_lo_fnG : ltac:(sec_stmt2 constr:(SEC_T_art_poison_lo_fnG) 8%nat 0%nat).
Proof using Type regs M rom raw sp p n v.
intros H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr.
unfold kHighMemBeg, kHighMemEnd, SB in *.
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
zbtk (ltac:(oF' 0x7a508%Z)) (ltac:(oD' 0x7a508%Z)).
stepn (ltac:(oF' 0x7a6e0%Z)) (ltac:(oD' 0x7a6e0%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
zbft (ltac:(oF' 0x7a6e4%Z)) (ltac:(oD' 0x7a6e4%Z)).
zstep (ltac:(oF' 0x7a6e8%Z)) (ltac:(oD' 0x7a6e8%Z)). zstep (ltac:(oF' 0x7a6ec%Z)) (ltac:(oD' 0x7a6ec%Z)).
zbtk (ltac:(oF' 0x7a6f0%Z)) (ltac:(oD' 0x7a6f0%Z)).
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
unfold Mf, art_poison_frame. subst v. zret.
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
zbtk (ltac:(oF' 0x7a508%Z)) (ltac:(oD' 0x7a508%Z)).
stepn (ltac:(oF' 0x7a6e0%Z)) (ltac:(oD' 0x7a6e0%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
zbft (ltac:(oF' 0x7a6e4%Z)) (ltac:(oD' 0x7a6e4%Z)).
zstep (ltac:(oF' 0x7a6e8%Z)) (ltac:(oD' 0x7a6e8%Z)). zstep (ltac:(oF' 0x7a6ec%Z)) (ltac:(oD' 0x7a6ec%Z)).
zbtk (ltac:(oF' 0x7a6f0%Z)) (ltac:(oD' 0x7a6f0%Z)).
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
unfold Mf, art_poison_frame. zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_poison_lo_runG := (ltac2:(TCodec.tc2 tcn__JbtPoison2G "W4&7y5'Q=yR0%211%5241'0y8%611%311p061'6'3&Fr8(Q;+1(1%33A21%6251r5%93A21&=r6%211r:+2%<3J1:%?231&Q<%12K7%C3K31r;+:%C3Q11A%F231%H3Q016r<+;%H3Q61F%K231%M3Q51;r=+<%M3Q;1K%Q0231%Q23Q:1@&L+R0%221H&M&O%12J4%32E1&;&Ir?&Q0%12E:%54431;&:%42C=+QV`QH+Q`P0%443@21r>%921B+Qii[8+X0%943E21&?rB%211+8%K21B&Jr@%2214&>%Q0221rA%6215%Q3214&N%12=;z%R:3R;21rC%Q9231'2%Q823F%2231rD%RA3RB18&KrF%221G+_oooooooooooO%Q@221p061rKrG%821M%L2I1%QB4QA418'4'<&GvQ2rN+_YU@%S03S<1RN/01S<rMrL%8576321r1&9&@rJ&Q>%12SFE%S;3SIQAS9%S>2>1%42SI1+9%S?3SM1S=%SB2B1%82SM1+B%SC3T11SA%SF2F1%<2T11+C%SG3T51SE%SJ2J1%@2T51+D%SK3T91SI%SN2N1%D2T91+E%SO3T=1SM%T22Q21%H2T=1%K9Q0JHEA=951rI%QE21R:%R92R61&Q1rH%QI21R>%311%Q44851QD%Q?5Q>Q6QF1Q8%QA3S4Q81%T?2Q8SJ%T02TJ9%TB3TJ21%TB2Q;T=%TD3TL1QL%TD2Q=T6%T52TOQ;%TG3TO21%TG2Q@Q:%TI3U11Q:%TI2QBQ8%TK3U31Q8%TK2QDQ6%TM3U51Q6%TM2QFQ4%TO3U71Q4%TO2QHQ2%U13U91Q2%U12QJQ0%U33U;1Q0%U>1U?&E%11QNr3r2%U8221rQ0%U:213%U<3UD31p071pR<:1%S22<1%S32?1%S42B1%S52E1%S62H1%S72K1%S82N1%S92Q21%S:2Q51%S;2Q91qRBV01%RM2V11p0RO1p0S51p0S>1p0SB1p0SE1p0SF1p0SK1p0SO1p0T51p0T81p0T<1p0TB1p0TH1p0TO1p0U41p0U81p0U>1p0UD1p0UJ1p0V21p0V61pS0VA1pR8VB1pR:VC1pRFVD1pR>VL1pRDVG1pBVH1pR@VN1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_runG) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_runG) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_runG) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_runG) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_runG) 4%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_runG) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_runG) 6%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_art_poison_lo_runG) 7%nat 0%nat).
Theorem art_poison_lo_runG : ltac:(sec_stmt2 constr:(SEC_T_art_poison_lo_runG) 8%nat 0%nat).
Proof using Type regs M rom raw sp p n v.
intros H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr Wsh.
pose proof (art_poison_lo_fnG regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr) as RUN1.
unfold kHighMemBeg, kHighMemEnd, SB in *.
match type of RUN1 with msteps _ _ (mkst ?R1 _ ?M1 _) =>
assert (OK : store_ok ASEGS M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z.to_nat (n / 8)) = true)
by (unfold art_poison_frame; apply wr_wok with (a := 2147450880 + p / 8) (n := n / 8); [|lia|lia]; repeat apply wr_Wn; exact Wsh);
destruct (memset_summary M1 (Z_to_bv 64 (2147450880 + p / 8)) (Z_to_bv 64 v) raw (n / 8) rom
ltac:(lia) ltac:(rewrite art_u_lit by lia; lia) OK Hret R1
ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity) ltac:(gres; reflexivity))
as (r2 & RUN2 & P10 & AG)
end.
exists r2. split.
{ eapply msteps_trans; [exact RUN1|]. unfold Wf. rewrite cbyte_cbz in RUN2. unfold cbz in RUN2. rewrite art_u_lit in RUN2 by lia.
replace (v mod 256) with v in RUN2 by (symmetry; apply Z.mod_small; lia).
replace (Z_to_bv 64 ms_base) with (0x126be8 : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
cbn [ms_clob In] in K.
zsplit;
try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
rewrite K by (intuition congruence). kept_solve.
Qed.
End SE.
Definition art_poison_lo_okG (p n : Z) : Prop := 8 <= p /\ p + 8 <= SB /\ p + n <= SB.
Definition art_poison_hi_okG (p n : Z) : Prop := kHighMemBeg <= p /\ kHighMemBeg + 8 <= p + n /\ p <= kHighMemEnd /\ p + n <= kHighMemEnd + 1.
#[using="Type"] Theorem art_poison_runG : ltac2:(TCodec.tc2 tcn__JbtPoison2G "W1&7y5'Q=yR0%211%5241'0y8%611%311p061'6'3&Fr8(Q;+1(1%33A21%6251r5%93A21&=r6%211r:+2%<3J1:%?231&Q<%12K7%C3K31r;+:%C3Q11A%F231%H3Q016r<+;%H3Q61F%K231%M3Q51;r=+<%M3Q;1K%Q0231%Q23Q:1@&L+R0%221H&M&O%12J4%32E1&;&Ir?&Q0%12E:%54431;&:%42C=+QV`QH+Q`P0%443@21r>%921B+Qii[8+X0%943E21&?rB%211'5&D%12C:&C%12E<%5231&Nr@+8%3221z%R83R921rA%Q7231'2%Q623D%2231%R>3R?C7&KrD%221<+_oooooooooooO%Q=221p061rI&J&>rE%:21D%4231%QA4Q@61:'4'<&GvQ2rL+_YU@%RO3S;1RM/01S;rKrJ%8576321r1&9&@rH&Q>%12SEG%S:3SHQ8S8%S=2>1%42SH1+9%S>3SL1S<%SA2B1%82SL1+B%SB3T01S@%SE2F1%<2T01+C%SF3T41SD%SI2J1%@2T41+D%SJ3T81SH%SM2N1%D2T81+E%SN3T<1SL%T12Q21%H2T<1%K9Q0JHEA=951rG%QG21R1%QA2Q@1&Q1rF%QK21R5%311%Q44851QD%Q?5Q>Q6QH1Q8%QA3S3Q81%T>2Q8SI%SO2TI9%TA3TI21%TA2Q;T<%TC3TK1QN%TC2Q=T5%T42TNQ;%TF3TN21%TF2Q@Q:%TH3U01Q:%TH2QBQ8%TJ3U21Q8%TJ2QDQ6%TL3U41Q6%TL2QFQ4%TN3U61Q4%TN2QHQ2%U03U81Q2%U02QJQ0%U23U:1Q0%U=1U>&E%11QNr3r2%U7221rN%U9213%U;3UC31p071pR<:1%S32<1%S42?1%S52B1%S62E1%S72H1%S82K1%S92N1%S:2Q21%S;2Q51%S<2Q91qRBUO1%RM2V01p0RO1p0S71p0S?1p0SC1p0SF1p0SG1p0SN1p0T51p0T91p0T?1p0TE1p0TL1p0U11p0U51p0U;1p0UA1p0UG1p0UO1p0V31pS0V>1pR8V?1pR:V@1pRFVA1pR>VI1pRDVD1pBVE1pR@VK1").
Proof.
intros regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L [Hl|Hh] Hp8 Hn8 Hn Hv Hthr Wsh.
- destruct Hl as (Ha & Hb & Hc). exact (art_poison_lo_runG regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Ha Hb Hc Hp8 Hn8 Hn Hv Hthr Wsh).
- destruct Hh as (Ha & Hb & Hc & Hd). exact (art_poison_hi0_runG regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Ha Hd Hp8 Hn8 Hn Hb Hc Hv Hthr Wsh).
Qed.
End FPX.
