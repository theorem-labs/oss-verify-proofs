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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JatPoison JatPoisonRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatPoison3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison3.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoisonRun."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "4bvmap"; "0M"; "5Wf"; "5apart"; "5wr"; "6msteps"; "7ret_ok"; "8SB"; "8art_layout"]; ["8art_poison_frame"; "8kHighMemBeg"; "8kHighMemEnd"; "9art_poison_hi_ok"; "9art_poison_lo_ok"; ":art_poison_kept"; ";getr"; ";mkst"; ";regupd"; "<loaded_segments"; "=add"; "=div"; "=le"; "=lt"; "=modulo"; "=pow"]; ["=sub"; "=to_nat"; "0fx"; "0n"; "0p"; "0r"; "0raw"; "0regs"; "0regs'"; "0rom"; "0sp"; ">BV"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0v"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_poison3_hi0_fn := (ltac2:(TCodec.tc2 tcn__JatPoison3 "W:&7y5'Q=yR0%211%5241'0y8%611%311p061'6'3&Fr8(Q;+1(1%33A21%6251r5%93A21r9+2%93G17%<231&Q<%12H7%@3H31r:+:%@3N1>%C231%E3M16r;+;%E3Q31C%H231%J3Q21;r<+<%J3Q81H%M231%O3Q71@&L+R0%221H&M&O%12J4%32E1&;&Ir>&Q0%12E:%54431;&:%42C=+QVXR0+Q`P0%443@21r=%921B+QibQ8+X0%943E21&?rA%211&A%K21B&Jr?%221E&B%421QL%Q1231&Nr@+8%3221z%R73R821%Q822@%=2?5rCrB%@221%Q=241rD%Q?21@'2%QA2;7%Q?28M%3221%RD3RE6>&KrF%221C+QM%QE2R>1%QG231p071'<&GvQ2rL+_X_0%RN3S:1RL/01S:rKrJ%8576321&HrI%239S21rH%RL2SC1%533RO1+5%S:3SH1S8&>%J2Q@Q;%QD221%S32SJ1%<3751+6%SA3SO1S?+QTc]@%S82SO1%A3531+7%SF3T41SD%S<2T3QK%E3421%SI3T7QHSG%SL2N1%H3321+9%SM3T;1SK%T02Q21%L3421rG%Q?21R0%R92G1%SH2T?1%Q135SD1rE%SK2TB1%Q433SB1%SM2TDQD%Q632S?1+=%T;3TI1T9%T12TH;%Q:3421+>%T?3TM1T=%T52TLR=%Q>3421+?%TC3U11TA%T92U0Q8%QB3421+@%TG3U51TE%SA2SFTG%T>2U51%QG3531+A%TL3U:1TJ%QJ331=+B%TO3U=1TM%U22R41%QN3421+C%U33UA1U1%U62R81%R23421+D%U73UE1U5%U:2R<1%R63421+E%U;3UI1U9%U>2R@1%R:3421+L%U?3UM1U=%R=331QI%UA3UMQOU?/01UM&@&Q>%12V1RA%22V2QL%32V3QI%42V4H%52V5E%62V6B%72V7?%99RLRF7654321%S35S2=;1RL%S53TIRL1p0S71p0S@1p0SE1p0SH1p0SN1p0T01p0T11p0T81p0T?1p0TB1p0TF1p0TL1p0U21p0U91p0U>1p0UB1p0UH1p0UN1p0V41p0V<1pS0VG1pR8VH1pR:VI1pRFVJ1pR>W21pRDVM1pBVN1pR@W41")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_fn) 4%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_fn) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_fn) 6%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_fn) 7%nat 0%nat).
Lemma art_poison3_hi0_fn : ltac:(sec_stmt2 constr:(SEC_T_art_poison3_hi0_fn) 8%nat 0%nat).
Proof using Type regs M rom raw sp p n v.
intros H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr.
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
Section SE.
Local Abbreviation SEC_T_art_poison3_hi0_run := (ltac2:(TCodec.tc2 tcn__JatPoison3 "W=&7y5'Q=yR0%211%5241'0y8%611%311p061'6'3&Fr8(Q;+1(1%33A21%6251r5%93A21&=r6%211r:+2%<3J1:%?231&Q<%12K7%C3K31r;+:%C3Q11A%F231%H3Q016r<+;%H3Q61F%K231%M3Q51;r=+<%M3Q;1K%Q0231%Q23Q:1@&L+R0%221H&M&O%12J4%32E1&;&Ir?&Q0%12E:%54431;&:%42C=+QVXR0+Q`P0%443@21r>%921B+QibQ8+X0%943E21&?rB%211&A%K21B&Jr@%221E&B%421QO%Q1231&NrA+8%3221z%R:3R;21%Q822@%=2?5rDrC%@221%Q=241rE%Q?21@'2%QA2;7%Q?28M%3221%RG3RH6>&KrG%221C+QM%QE2R>1%QG231p071rL&>rH%:21K%Q4231%QJ4QI51:'4'<&GvQ2rO+_X_0%S83SD1S6/01SDrNrM%8576321r1&9&@rK&Q>%12SNF%SC3T1Q?SA%SF2>1%42T11+9%SG3T51SE%SJ2B1%82T51+B%SK3T91SI%SN2F1%<2T91+C%SO3T=1SM%T22J1%@2T=1+D%T33TA1T1%T62N1%D2TA1+E%T73TE1T5%T:2Q21%H2TE1%K9Q0JHEA=951rJ%QG21R8%RA2Q@1&Q1rI%QK21R<%311%Q44851QD%Q?5Q>Q6QG1Q8%QA3S<Q81%TG2Q8T2%T82U29%TJ3U221%TJ2Q;TE%TL3U41QM%TL2Q=T>%T=2U7Q;%TO3U721%TO2Q@Q:%U13U91Q:%U12QBQ8%U33U;1Q8%U32QDQ6%U53U=1Q6%U52QFQ4%U73U?1Q4%U72QHQ2%U93UA1Q2%U92QJQ0%U;3UC1Q0%UF1UG&E%11QNr3r2%U@221rQ1%UB213%UD3UL31p071pR<:1%S42<1%S52?1%S62B1%S72E1%S82H1%S92K1%S:2N1%S;2Q21%S<2Q51%S=2Q91qRBV81%RM2V91p0RO1p0S61p0S?1p0SD1p0SG1p0SM1p0SO1p0T01p0T71p0T>1p0TA1p0TE1p0TK1p0U11p0U81p0U=1p0UA1p0UG1p0UM1p0V31p0V;1p0V?1pS0VJ1pR8VK1pR:VL1pRFVM1pR>W51pRDW01pBW11pR@W71")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_run) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_run) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_run) 4%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_run) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_run) 6%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_art_poison3_hi0_run) 7%nat 0%nat).
Theorem art_poison3_hi0_run : ltac:(sec_stmt2 constr:(SEC_T_art_poison3_hi0_run) 8%nat 0%nat).
Proof using Type regs M rom raw sp p n v.
intros H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr Wsh.
pose proof (art_poison3_hi0_fn regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo Hhi Hp8 Hn8 Hn HnB HpE Hv Hthr) as RUN1.
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
replace (Z_to_bv 64 ms_base) with (0x124db0 : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
cbn [ms_clob In] in K.
zsplit;
try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
rewrite K by (intuition congruence). kept_solve.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_poison3_lo_fn := (ltac2:(TCodec.tc2 tcn__JatPoison3 "V>&7y5'Q=yR0%211%5241'0y8%611%311p061'6'3&Fr8(Q;+1(1%33A21%6251r5%93A21r9+2%93G17%<231&Q<%12H7%@3H31r:+:%@3N1>%C231%E3M16r;+;%E3Q31C%H231%J3Q21;r<+<%J3Q81H%M231%O3Q71@&L+R0%221H&M&O%12J4%32E1&;&Ir>&Q0%12E:%54431;&:%42C=+QVXR0+Q`P0%443@21r=%921B+QibQ8+X0%943E21&?rA%211+8%K21B&Jr?%2214&>%Q0221r@%6215%Q3214&N%12=;z%R73R821rB%Q9231'2%Q823F%2231rC%R>3R?18&KrE%221G+QM%Q?2R81%QA231p071'<&GvQ2rK+_X_0%RH3S41RF/01S4rJrI%8576321&HrH%239RL1rG%RF2S=1%533RI1+6%S43SB1S2+QTc]@%RK2SB1%:3531%S83SFQAS6%S;2C1%=3321+9%S<3SJ1S:%S?2G1%A3421rF%Q421QI%QH2QE1%S72SN1%F35S31rD%S:2T11%I33S11%S<2T3Q9%K32RN1+=%SJ3T81SH%S@2T7;%O3421+>%SN3T<1SL%RH2R3SN%SE2T<1%Q43531+?%T33TA1T1%SI2T@R1%Q83421+B%T73TE1T5%T:2QB1%Q<3421+C%T;3TI1T9%T>2QF1%Q@3421+D%T?3TM1T=%TB2QJ1%QD3421+E%TC3U11TA%TF2QN1%QH3421%TF3U2QATD/01U2&@&Q>%12U6QL%22U7QB%32U8Q?%42U9E%52U:B%62U;?%72U<<%99R7R17654321%R>5R==;1R7%R@3SNR71p0RB1p0RL1p0S01p0S31p0S41p0S91p0S=1p0SC1p0SF1p0SJ1p0T01p0T61p0T=1p0TB1p0TF1p0TL1p0U21p0U81p0U@1pS0UK1pR8UL1pR:UM1pRFUN1pR>V61pRDV11pBV21pR@V81")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_fn) 4%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_fn) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_fn) 6%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_fn) 7%nat 0%nat).
Lemma art_poison3_lo_fn : ltac:(sec_stmt2 constr:(SEC_T_art_poison3_lo_fn) 8%nat 0%nat).
Proof using Type regs M rom raw sp p n v.
intros H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr.
unfold kHighMemBeg, kHighMemEnd, SB in *.
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
zbtk (ltac:(oF' 0x7a238%Z)) (ltac:(oD' 0x7a238%Z)).
stepn (ltac:(oF' 0x7a410%Z)) (ltac:(oD' 0x7a410%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
zbft (ltac:(oF' 0x7a414%Z)) (ltac:(oD' 0x7a414%Z)).
zstep (ltac:(oF' 0x7a418%Z)) (ltac:(oD' 0x7a418%Z)). zstep (ltac:(oF' 0x7a41c%Z)) (ltac:(oD' 0x7a41c%Z)).
zbtk (ltac:(oF' 0x7a420%Z)) (ltac:(oD' 0x7a420%Z)).
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
unfold Mf, art_poison_frame. subst v. zret.
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
zbtk (ltac:(oF' 0x7a238%Z)) (ltac:(oD' 0x7a238%Z)).
stepn (ltac:(oF' 0x7a410%Z)) (ltac:(oD' 0x7a410%Z)). rwH. rewrite art_zb_andi by lia. replace (Z.land n 7) with 0 by (rewrite Z.land_ones with (n:=3); [|lia]; change (2^3) with 8; lia).
zbft (ltac:(oF' 0x7a414%Z)) (ltac:(oD' 0x7a414%Z)).
zstep (ltac:(oF' 0x7a418%Z)) (ltac:(oD' 0x7a418%Z)). zstep (ltac:(oF' 0x7a41c%Z)) (ltac:(oD' 0x7a41c%Z)).
zbtk (ltac:(oF' 0x7a420%Z)) (ltac:(oD' 0x7a420%Z)).
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
unfold Mf, art_poison_frame. zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_poison3_lo_run := (ltac2:(TCodec.tc2 tcn__JatPoison3 "W5&7y5'Q=yR0%211%5241'0y8%611%311p061'6'3&Fr8(Q;+1(1%33A21%6251r5%93A21&=r6%211r:+2%<3J1:%?231&Q<%12K7%C3K31r;+:%C3Q11A%F231%H3Q016r<+;%H3Q61F%K231%M3Q51;r=+<%M3Q;1K%Q0231%Q23Q:1@&L+R0%221H&M&O%12J4%32E1&;&Ir?&Q0%12E:%54431;&:%42C=+QVXR0+Q`P0%443@21r>%921B+QibQ8+X0%943E21&?rB%211+8%K21B&Jr@%2214&>%Q0221rA%6215%Q3214&N%12=;z%R:3R;21rC%Q9231'2%Q823F%2231rD%RA3RB18&KrF%221G+QM%Q?2R81%QA231p071rKrG%921N%M2J1%QC4QB419'4'<&GvQ2rN+_X_0%S13S=1RO/01S=rMrL%8576321r1&9&@rJ&Q>%12SGE%S<3SJQBS:%S?2>1%42SJ1+9%S@3SN1S>%SC2B1%82SN1+B%SD3T21SB%SG2F1%<2T21+C%SH3T61SF%SK2J1%@2T61+D%SL3T:1SJ%SO2N1%D2T:1+E%T03T>1SN%T32Q21%H2T>1%K9Q0JHEA=951rI%QF21R;%R:2R71&Q1rH%QJ21R?%311%Q44851QD%Q?5Q>Q6QF1Q8%QA3S5Q81%T@2Q8SK%T12TK9%TC3TK21%TC2Q;T>%TE3TM1QL%TE2Q=T7%T62U0Q;%TH3U021%TH2Q@Q:%TJ3U21Q:%TJ2QBQ8%TL3U41Q8%TL2QDQ6%TN3U61Q6%TN2QFQ4%U03U81Q4%U02QHQ2%U23U:1Q2%U22QJQ0%U43U<1Q0%U?1U@&E%11QNr3r2%U9221rQ0%U;213%U=3UE31p071pR<:1%S32<1%S42?1%S52B1%S62E1%S72H1%S82K1%S92N1%S:2Q21%S;2Q51%S<2Q91qRBV11%RM2V21p0RO1p0S51p0S?1p0SC1p0SF1p0SG1p0SL1p0T01p0T61p0T91p0T=1p0TC1p0TI1p0U01p0U51p0U91p0U?1p0UE1p0UK1p0V31p0V71pS0VB1pR8VC1pR:VD1pRFVE1pR>VM1pRDVH1pBVI1pR@VO1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_run) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_run) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_run) 4%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_run) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_run) 6%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SEC_T_art_poison3_lo_run) 7%nat 0%nat).
Theorem art_poison3_lo_run : ltac:(sec_stmt2 constr:(SEC_T_art_poison3_lo_run) 8%nat 0%nat).
Proof using Type regs M rom raw sp p n v.
intros H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr Wsh.
pose proof (art_poison3_lo_fn regs M rom raw sp p n v H1 H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Hlo HpE Hhi Hp8 Hn8 Hn Hv Hthr) as RUN1.
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
replace (Z_to_bv 64 ms_base) with (0x124db0 : bv 64)%bv in RUN2 by (apply bv_eq; vm_compute; reflexivity). exact RUN2. }
assert (K : forall r : reg, ~ In r ms_clob -> getr r2 r = getr _ r) by exact AG.
cbn [ms_clob In] in K.
zsplit;
try (rewrite K by (intuition discriminate); gres; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]).
intros r Hr. unfold art_poison_kept in Hr. destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?).
rewrite K by (intuition congruence). kept_solve.
Qed.
End SE.
Definition art_poison_lo_ok (p n : Z) : Prop := 8 <= p /\ p + 8 <= SB /\ p + n <= SB.
Definition art_poison_hi_ok (p n : Z) : Prop := kHighMemBeg <= p /\ kHighMemBeg + 8 <= p + n /\ p <= kHighMemEnd /\ p + n <= kHighMemEnd + 1.
#[using="Type"] Theorem art_poison3_run : ltac2:(TCodec.tc2 tcn__JatPoison3 "W2&7y5'Q=yR0%211%5241'0y8%611%311p061'6'3&Fr8(Q;+1(1%33A21%6251r5%93A21&=r6%211r:+2%<3J1:%?231&Q<%12K7%C3K31r;+:%C3Q11A%F231%H3Q016r<+;%H3Q61F%K231%M3Q51;r=+<%M3Q;1K%Q0231%Q23Q:1@&L+R0%221H&M&O%12J4%32E1&;&Ir?&Q0%12E:%54431;&:%42C=+QVXR0+Q`P0%443@21r>%921B+QibQ8+X0%943E21&?rB%211'5&D%12C:&C%12E<%5231&Nr@+8%3221z%R83R921rA%Q7231'2%Q623D%2231%R>3R?C7&KrD%221<+QM%Q<2R51%Q>231p071rI&J&>rE%;21E%4231%QB4QA61;'4'<&GvQ2rL+_X_0%S03S<1RN/01S<rKrJ%8576321r1&9&@rH&Q>%12SFG%S;3SIQ9S9%S>2>1%42SI1+9%S?3SM1S=%SB2B1%82SM1+B%SC3T11SA%SF2F1%<2T11+C%SG3T51SE%SJ2J1%@2T51+D%SK3T91SI%SN2N1%D2T91+E%SO3T=1SM%T22Q21%H2T=1%K9Q0JHEA=951rG%QH21R2%QA2Q@1&Q1rF%QL21R6%311%Q44851QD%Q?5Q>Q6QH1Q8%QA3S4Q81%T?2Q8SJ%T02TJ9%TB3TJ21%TB2Q;T=%TD3TL1QN%TD2Q=T6%T52TOQ;%TG3TO21%TG2Q@Q:%TI3U11Q:%TI2QBQ8%TK3U31Q8%TK2QDQ6%TM3U51Q6%TM2QFQ4%TO3U71Q4%TO2QHQ2%U13U91Q2%U12QJQ0%U33U;1Q0%U>1U?&E%11QNr3r2%U8221rN%U:213%U<3UD31p071pR<:1%S42<1%S52?1%S62B1%S72E1%S82H1%S92K1%S:2N1%S;2Q21%S<2Q51%S=2Q91qRBV01%RM2V11p0RO1p0S71p0S@1p0SD1p0SG1p0SH1p0SO1p0T61p0T:1p0T@1p0TF1p0TM1p0U21p0U61p0U<1p0UB1p0UH1p0V01p0V41pS0V?1pR8V@1pR:VA1pRFVB1pR>VJ1pRDVE1pBVF1pR@VL1").
Proof.
intros regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L [Hl|Hh] Hp8 Hn8 Hn Hv Hthr Wsh.
- destruct Hl as (Ha & Hb & Hc). exact (art_poison3_lo_run regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Ha Hb Hc Hp8 Hn8 Hn Hv Hthr Wsh).
- destruct Hh as (Ha & Hb & Hc & Hd). exact (art_poison3_hi0_run regs M rom raw sp p n v H1 Hret H2 H10 H11 H12 Hsp Hsp' W A1 A2 L Ha Hd Hp8 Hn8 Hn Hb Hc Hv Hthr Wsh).
Qed.
End FPX.
