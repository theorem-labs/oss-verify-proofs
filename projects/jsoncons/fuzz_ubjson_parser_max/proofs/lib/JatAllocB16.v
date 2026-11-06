(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JatAllocB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatAllocB16 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocB16."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "3Z"; "4bvmap"; "0M"; "5apart"; "5cell"; "5wr"; "6msteps"; "7art_alloc_memB_16"; "7art_hdr_b1_16"; "8getr"; "8mkst"; "8regupd"]; ["9loaded_segments"; ":add"; ":div"; ":le"; ":lt"; ":max"; ":modulo"; ":mul"; ":pow"; ":sub"; "0ab"; "0ctx"; "0fx"; "0n"; "0ob"; "0regs"]; ["0rom"; "0rs"; "0rz"; "0sp"; ";BV"; ";Z_to_bv"; ";bv"; "0stk"; "0szt"; "0t"; "0trp"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_hdr_b1_16 (ob : Z) : Z := Z.lor (Z.land (art_hdr_b1a ob) 143) 32.
Lemma art_hdr_b1_16_range : ltac2:(TCodec.tc2 tcn__JatAllocB16 "B'4'2&Czr1%3221&D+X0%2241%8241&<r2%211%;2:1%8227%>221p071pQNA1").
Proof. intros ob Hob. unfold art_hdr_b1_16. pose proof (art_hdr_b1a_range ob Hob). apply lor_lt_256; [|lia]. pose proof (land_le_l (art_hdr_b1a ob) 143 ltac:(lia) ltac:(lia)). lia. Qed.
Definition art_alloc_memB_16 (M : word -> option byte) (ab rz n ob : Z) : word -> option byte :=
Wn 1 (Wn 4 (Wn 2 (Wn 1 M (ab + rz - 15) (art_hdr_b1a ob)) (ab + rz - 14) (n / 2 ^ 32)) (ab + rz - 12) n) (ab + rz - 15) (art_hdr_b1_16 ob).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_alloc_b_16_fn := (ltac2:(TCodec.tc2 tcn__JatAllocB16 "YF&5y5'Q6yR0%211%5241'0y8%611%311p061'4'3&=r>(Q4+2(1%33A21%6251&Q5r;%22C1%;3C41r?+:%;3I19%>231%@3H16r@+9%@3N1>%C231%E3M1;rA+C%E3Q31C%H231&A+@%22C1r:%4221%G2Q81%Q03Q871rB+D%Q03Q>1N%Q3231%Q53Q=1KrC+E%Q53QC1Q3%Q8231%Q22QCQ8%Q;3QC21rD+G%Q;3QI1Q9%Q>231r<%Q92QJ1%QB3QJ31rE+I%QB3R01Q@%QE231+?%Q@2R11%QI3R131rF+J%QI3R71QG%QL231r=%QG2R81%R03R831rG+K%R03R>1QN%R3231+1%QN2R?1%R73R?31&Cz%221G&D+T0%QC2C1&H+R0%22R<1%6241+TP0%;21I+RPP0%QK2D1+Q?%92RC1%=231&FrH%221R0%RL3RM1C'2%F2I4+Q8%B2RL1%F271%5241&G&B&ErI+8%3221%R?21QB%621R?%821R@%S<3S=B1%Q52RBC+RP0%Q72E1%C231%H2;RF%SB3SC1Q9rK%RJ21RIrJ%RL221%Q?21Q3%Q@2Q63%Q>25Q9%QB2Q87rL%S221Q:%QB21Q=%QF2Q<3rM%S621Q>%QF21QA%QJ2QI3+X0%QI251%Q8231%QK27QF%Q:251&9&@rQ:&IrQ7rQ4%SD221%421SD%84761SE&8rQ;rQ8rQ5%SK221%;21ROu1rQ1%85@7321rQ<%T12AT0u8+Q0%=5E4321rQ=%?5G1<4CrQ>%T82>QKu4%C5K321RKrQ?%E5M1C:IrQ@rQ9%T?21R2%I5Q131>M&7%TB2;J%Q221TB%341TC9S2%TE2:E%Q521TE%641TFQ7R:%TH2;C%Q821TH%TJ2Q:R=+4%;43TK21rQA%TN21G%Q>21TN%?41TOKTO':&>vLrQF+ZWd4%UM3V91UK/01V9rQErQD%8576321&?%V33VAT1V1+ZWl@%V53VA1V3/01VA%53<41%V32VDR1%732UN1+;%V;3VI1V9%V72VHQ7%;3421+<%V?3VM1V=%V;2VLT:%?3421+>%VC3W11VArQB%UN21QA%UO21UN%V021QE%VC2W41%G3861+B%VK3W91VI%VG2W88%K3421%V72:QL%VJ2W;1%N33V01%RI23V9%VM2W>1%Q133UN1+H%W53WC1W3%Q4331F%V@29QC%W32WD1%Q733UG1+cUc<%W;3WG1W9/01WG&;%15Q?JR<QJRO%QF5QE631Q?%QH3S:Q?1p0QJ1p0QO1p0R51p0R91p0R>1p0RC1p0RF1p0RK1p0RN1p0S41p0S>1p0SH1p0SI1p0SL1p0T11p0T51p0T71p0T;1p0T=1p0T?1p0TA1p0TG1p0TJ1p0TO1p0U:1p0UA1p0UF1p0UL1p0UO1p0V71p0V;1p0VC1p0VK1p0W31p0W;1p0WB1p0WH1p0X41p0X:1p0X@1pRBXM1pRFXN1pQNXO1pQHY01pRDY11pR@Y21pR6Y31pR4Y41pQLY51pQFY61pR8Y71pR2Y91p>Y:1pR0Y@1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_16_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_16_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_16_fn) 2%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_16_fn) 3%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_16_fn) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_alloc_b_16_fn) 5%nat 0%nat).
Lemma art_alloc_b_16_fn : ltac:(sec_stmt2 constr:(SEC_T_art_alloc_b_16_fn) 6%nat 0%nat).
Proof using Type regs M rom sp ab n.
intros rs rz stk t ctx ob trp szt H2 H10 H9 H19 H20 H21 H23 H25 H26 H27 Hsp Hsp' Hab Hab' Hab16 Hn Hrs Hrz Hrz16 Hprim
Hstk Hstk' Ht Ht' Hctx Hctx' Hob Htrp Hszt W Cob C16 Cctx Ctid Ctrp Cszt A1 A2 A3 A4.
assert (Hrsn : n <= rs /\ rs <= n + 23) by (subst rs; split; [|]; lia).
pose proof (art_hdr_b1a_range ob Hob) as Rb1a. pose proof (art_hdr_b1_16_range ob Hob) as Rb1.
zstep (ltac:(oF' 0x51e84%Z)) (ltac:(oD' 0x51e84%Z)).
zbft (ltac:(oF' 0x51e88%Z)) (ltac:(oD' 0x51e88%Z)).
zstep (ltac:(oF' 0x51e8c%Z)) (ltac:(oD' 0x51e8c%Z)).
stepn (ltac:(oF' 0x51e90%Z)) (ltac:(oD' 0x51e90%Z)). rwH. rewrite art_zb_and by lia. change 15 with (Z.ones 4) at 1. rewrite Z.land_ones by lia. change (2 ^ 4) with 16.
replace ((ab + rz) mod 16) with 0 by lia.
zstep (ltac:(oF' 0x51e94%Z)) (ltac:(oD' 0x51e94%Z)).
zbtk (ltac:(oF' 0x51e98%Z)) (ltac:(oD' 0x51e98%Z)).
zstep (ltac:(oF' 0x51ea4%Z)) (ltac:(oD' 0x51ea4%Z)).
zbft (ltac:(oF' 0x51ea8%Z)) (ltac:(oD' 0x51ea8%Z)).
zlbu (ltac:(oF' 0x51eac%Z)) (ltac:(oD' 0x51eac%Z)) (ab + rz - 15) Cob.
stepn (ltac:(oF' 0x51eb0%Z)) (ltac:(oD' 0x51eb0%Z)). rwH. rewrite art_zb_andi by lia. change (Z.land 1 3) with 1.
stepn (ltac:(oF' 0x51eb4%Z)) (ltac:(oD' 0x51eb4%Z)). rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612.
pose proof (land_le_l ob 18446744073709551612 ltac:(lia) ltac:(lia)) as Lb.
stepn (ltac:(oF' 0x51eb8%Z)) (ltac:(oD' 0x51eb8%Z)). rwH. unfold v_or. rewrite !art_u_lit by lia.
change (Z.lor (Z.land ob 18446744073709551612) 1) with (art_hdr_b1a ob).
stepn (ltac:(oF' 0x51ebc%Z)) (ltac:(oD' 0x51ebc%Z)). rwH. rewrite art_zb_srli by lia.
stepn (ltac:(oF' 0x51ec0%Z)) (ltac:(oD' 0x51ec0%Z)). rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small n (2 ^ 48)) by lia.
zsb (ltac:(oF' 0x51ec4%Z)) (ltac:(oD' 0x51ec4%Z)) (ab + rz - 15) (art_hdr_b1a ob) ltac:(rewok W).
zsh (ltac:(oF' 0x51ec8%Z)) (ltac:(oD' 0x51ec8%Z)) (ab + rz - 14) (n / 2 ^ 32) ltac:(rewok W).
zsw (ltac:(oF' 0x51ecc%Z)) (ltac:(oD' 0x51ecc%Z)) (ab + rz - 12) n ltac:(rewok W).
zbft (ltac:(oF' 0x51ed0%Z)) (ltac:(oD' 0x51ed0%Z)).
zstep (ltac:(oF' 0x51ed4%Z)) (ltac:(oD' 0x51ed4%Z)).
stepn (ltac:(oF' 0x51ed8%Z)) (ltac:(oD' 0x51ed8%Z)). rwH. rewrite art_zb_andi by lia.
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (sp + 16) 8 32) by (unfold apart in *; recell C16) end.
zld (ltac:(oF' 0x51edc%Z)) (ltac:(oD' 0x51edc%Z)) (sp + 16) C16'.
pose proof (land_le_l (art_hdr_b1a ob) 143 ltac:(lia) ltac:(lia)) as Lb2.
stepn (ltac:(oF' 0x51ee0%Z)) (ltac:(oD' 0x51ee0%Z)). rwH. unfold v_or. rewrite !art_u_lit by lia.
change (Z.lor (Z.land (art_hdr_b1a ob) 143) 32) with (art_hdr_b1_16 ob).
zsb (ltac:(oF' 0x51ee4%Z)) (ltac:(oD' 0x51ee4%Z)) (ab + rz - 16 + 1) (art_hdr_b1_16 ob) ltac:(rewok W).
zbft (ltac:(oF' 0x51ee8%Z)) (ltac:(oD' 0x51ee8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (Cctx' : cellA X t 8 ctx) by (unfold apart in *; recell Cctx);
assert (Ctid' : cellA X (ctx + 8) 4 0) by (unfold apart in *; recell Ctid);
assert (Ctrp' : cellA X stk 8 trp) by (unfold apart in *; recell Ctrp);
assert (Cszt' : cellA X (stk + 8) 8 szt) by (unfold apart in *; recell Cszt) end.
zld (ltac:(oF' 0x51eec%Z)) (ltac:(oD' 0x51eec%Z)) t Cctx'.
zlw (ltac:(oF' 0x51ef0%Z)) (ltac:(oD' 0x51ef0%Z)) (ctx + 8) Ctid'.
zstep (ltac:(oF' 0x51ef4%Z)) (ltac:(oD' 0x51ef4%Z)).
stepn (ltac:(oF' 0x51ef8%Z)) (ltac:(oD' 0x51ef8%Z)).
zld (ltac:(oF' 0x51f84%Z)) (ltac:(oD' 0x51f84%Z)) stk Ctrp'.
zld (ltac:(oF' 0x51f88%Z)) (ltac:(oD' 0x51f88%Z)) (stk + 8) Cszt'.
stepn (ltac:(oF' 0x51f8c%Z)) (ltac:(oD' 0x51f8c%Z)).
unfold art_alloc_memB_16. zret.
Qed.
End SE.
End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
