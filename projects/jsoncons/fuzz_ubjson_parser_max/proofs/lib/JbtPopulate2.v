(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import JbtPopulate1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtPopulate2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPopulate2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "3Z"; "4bvmap"; "0M"; "5apart"; "5cell"; "5wr"; "6msteps"; "7ret_ok"; "8art_tsd"; "9art_efas_c_mem"; "9art_efas_frame"; ":getr"]; [":mkst"; ":regupd"; ";loaded_segments"; "<add"; "<le"; "<lt"; "<mul"; "<pow"; "<sub"; "0ctx"; "0fx"; "0g18"; "0g19"; "0g8"; "0g9"; "0ia"]; ["0key"; "0len"; "0m1"; "0m2"; "0mfa"; "0nm"; "0p"; "0q"; "0r"; "0raw"; "0rb"; "0regs"; "0rom"; "0rr"; "0sp"; "=BV"]; ["=Z_to_bv"; "=bv"; "=bv_unsigned"; "0t"; "0total"; "0tp"; "0tsd"]]).
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
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".
Definition art_efas_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)).
Definition art_efas_c_mem (M : word -> option byte) (sp t r m1 m2 len nm : Z) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 48 - 8) 347880) (sp - 48 - 24) 533556) (t + 2872) (m1 + 1)) (t + 2880) (m2 + len)) (r + 24) nm.
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_efas_warm_fn := (ltac2:(TCodec.tc2 tcn__JbtPopulate2 "U0&5y5'QAyR0%211%5241'0y8%611%311p061'4'3&?r8(Q?+1(1%33A21%6251r5%93A21&;r6%211r:+2%<3J1:%?231&Q@%12K7%C3K31r;+;%C3Q11A%F231%H3Q016r<+=%H3Q61F%K231%M3Q51;&D+Q@r9%3221&E&G+R0%22G1%42I1&C+Vb\P0%221:%<21F%=23G+T0%62D1+Q?%<2Q11%>231z%D21I&F+4r=%3221%I21N%F23C&7&HrA%221Mr@%542O1B&9&BrErB%921Q4%54431Q5&8rF+H%Q1261u8%55:421=':&@vJrH+Zca8%R=3RI1R;/01RIrG%756521=&A%137R?DrD%R62S01%433R91+8%RG3S51RE%RJ2=1%83421+9%RK3S91RI%RN2A1%<3421+:%RO3S=1RM%RB2S<RO%@3421%A31R:2+>%S43SB1S2%RG2SAQ=%E3421+?%S83SF1S6%R92RNRN%QJ2Q;1%RM2SG1%K3641+B%S>3SL1S<%SA2Q41%O3421+C%SB3T01S@%SE2Q81%Q33421&>%14Q7Q3QHQ;%Q>5Q=3QI1QD%Q@3QKQ81p0QB1p0QI1p0R01p0R71p0R91p0R?1p0RB1p0RH1p0RJ1p0RO1p0S51p0S:1p0S@1p0SF1p0SN1p0T21pR:T=1pS:T>1pRBT?1pRNT@1pRDTH1pRJTC1p>TD1pRHTJ1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_efas_warm_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_efas_warm_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_efas_warm_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_efas_warm_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_efas_warm_fn) 4%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_efas_warm_fn) 5%nat 0%nat).
Variable total : ltac:(sec_ty2 constr:(SEC_T_art_efas_warm_fn) 6%nat 0%nat).
Variable mfa : ltac:(sec_ty2 constr:(SEC_T_art_efas_warm_fn) 7%nat 0%nat).
Lemma art_efas_warm_fn : ltac:(sec_stmt2 constr:(SEC_T_art_efas_warm_fn) 8%nat 0%nat).
Proof using Type regs M rom raw sp r total mfa.
intros H1 Hret H2 H11 H13 Hsp Hsp' IMG Hr Hr' Htot Hmfa Hmfa' A W Cmfa.
zstep (ltac:(oF' 0x54e28%Z)) (ltac:(oD' 0x54e28%Z)).
zsd (ltac:(oF' 0x54e2c%Z)) (ltac:(oD' 0x54e2c%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x54e30%Z)) (ltac:(oD' 0x54e30%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd (ltac:(oF' 0x54e34%Z)) (ltac:(oD' 0x54e34%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x54e38%Z)) (ltac:(oD' 0x54e38%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd (ltac:(oF' 0x54e3c%Z)) (ltac:(oD' 0x54e3c%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W).
fold (art_efas_frame M sp raw regs).
assert (Cmfa' : cellA (art_efas_frame M sp raw regs) (r + 24) 8 mfa) by (unfold art_efas_frame; unfold apart in A; zcell).
zld (ltac:(oF' 0x54e40%Z)) (ltac:(oD' 0x54e40%Z)) (r + 24) Cmfa'.
zstep (ltac:(oF' 0x54e44%Z)) (ltac:(oD' 0x54e44%Z)). zstep (ltac:(oF' 0x54e48%Z)) (ltac:(oD' 0x54e48%Z)).
zbtk (ltac:(oF' 0x54e4c%Z)) (ltac:(oD' 0x54e4c%Z)).
zstep (ltac:(oF' 0x54f0c%Z)) (ltac:(oD' 0x54f0c%Z)).
assert (F8 : cellA (art_efas_frame M sp raw regs) (sp - 8) 8 (U raw)) by (unfold art_efas_frame; zcell).
assert (F16 : cellA (art_efas_frame M sp raw regs) (sp - 16) 8 (U (getr regs 8))) by (unfold art_efas_frame; zcell).
assert (F24 : cellA (art_efas_frame M sp raw regs) (sp - 24) 8 (U (getr regs 9))) by (unfold art_efas_frame; zcell).
assert (F32 : cellA (art_efas_frame M sp raw regs) (sp - 32) 8 (U (getr regs 18))) by (unfold art_efas_frame; zcell).
assert (F40 : cellA (art_efas_frame M sp raw regs) (sp - 40) 8 (U (getr regs 19))) by (unfold art_efas_frame; zcell).
zld (ltac:(oF' 0x54f10%Z)) (ltac:(oD' 0x54f10%Z)) (sp - 8) F8. zld (ltac:(oF' 0x54f14%Z)) (ltac:(oD' 0x54f14%Z)) (sp - 16) F16. zld (ltac:(oF' 0x54f18%Z)) (ltac:(oD' 0x54f18%Z)) (sp - 24) F24. zld (ltac:(oF' 0x54f1c%Z)) (ltac:(oD' 0x54f1c%Z)) (sp - 32) F32. zld (ltac:(oF' 0x54f20%Z)) (ltac:(oD' 0x54f20%Z)) (sp - 40) F40.
rewrite !Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x54f24%Z)) (ltac:(oD' 0x54f24%Z)).
stepret (ltac:(oF' 0x54f28%Z)) (ltac:(oD' 0x54f28%Z)) raw ltac:(rwH; reflexivity).
zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_efas_a_fn := (ltac2:(TCodec.tc2 tcn__JbtPopulate2 "VM&5y5'QAyR0%211%5241'0y8%611%311p061'4'3&?r<(Q?+1(1%33A21%6251r9%93A21r=+2%93G17%<231&Q@%12H7%@3H31r>+:%@3N1>%C231%E3M16r?+;%E3Q31C%H231%J3Q21;r@+<%J3Q81H%M231%O3Q71@rA+=%O3Q=1M%Q2231%Q43Q<1E&D+Q@%221F&E&G+R0%22Q01%42F1&C+Vb\P0%2219%;21Ez%=21G+TP0%72D1%@217%A28FrB+T0%<221+Q?%B2Q@1%D231%H2<6rC+Q0%G2QE1%D231%J217%N2B5'2&F+4rD%3221%Q12;1%6271rE%7261+WooO%Q1221+XPP0%;21B%Q421J%RB3RC41%Q;2E4%@2A1%@26:+`PPPP0%QB221&7&HrL%221QErJ%542QG1Q5&9&BrQ0rM%921QL%54431QM&8rQ1+H%QJ2=1u8rI%65;5321rQ2rN+QH%R1221u1%<5A521QO':&@vJrQ4+Zca8%SC3SO1SA/01SOrQ3%756521>&A+Zcf8%SI3T51SG/01T5%43:SH1%Q62ORI%SB2T91%733SE1+8%T03T>1SN+B%RL2SJ1%R12Q:1%SI2T@1%>3751+9%T73TE1T5rK+S`PPPP0%S02Q<1%S1231%T12TH1%F3861%G31SI2%QI2<7%T52TL1%J33SG1+SVc:%T82TO1%M33SE1+>%TF3U41TD%T<2U3?%Q13421+?%TJ3U81TH%T@2U7B%Q53421%TM3U;LTK%Q7321>+C%U03U>1TN%TF2U=QH%Q;3421+beZ4%U43U@1U2/01U@&>%14QBR:R5QF%QI5QH631R0%QK3R=QC1p0QM1p0R41p0R<1p0RC1p0RJ1p0RN1p0S11p0S:1p0SB1p0SD1p0SJ1p0SL1p0T31p0T51p0T91p0T<1p0TA1p0TG1p0TK1p0U11p0U71p0U=1p0UC1p0UK1pRLV61pR@V71pR:V81pS:V91pRFV:1pRBV;1pR0V<1pRNV=1pRDVE1pRJV@1p>VA1pRHVG1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_efas_a_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_efas_a_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_efas_a_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_efas_a_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_efas_a_fn) 4%nat 0%nat).
Variable ia : ltac:(sec_ty2 constr:(SEC_T_art_efas_a_fn) 5%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_efas_a_fn) 6%nat 0%nat).
Variable rb : ltac:(sec_ty2 constr:(SEC_T_art_efas_a_fn) 7%nat 0%nat).
Variable total : ltac:(sec_ty2 constr:(SEC_T_art_efas_a_fn) 8%nat 0%nat).
Variable mfa : ltac:(sec_ty2 constr:(SEC_T_art_efas_a_fn) 9%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_art_efas_a_fn) 10%nat 0%nat).
Variable rr : ltac:(sec_ty2 constr:(SEC_T_art_efas_a_fn) 11%nat 0%nat).
Lemma art_efas_a_fn : ltac:(sec_stmt2 constr:(SEC_T_art_efas_a_fn) 12%nat 0%nat).
Proof using Type regs M rom raw sp ia r rb total mfa q rr.
intros H1 H2 H10 H11 H12 H13 Hsp Hsp' IMG Hia Hia' Hr Hr' Hrb Hrb' Htot Hmfa Eq Hrr Hq A W Cmfa Cpm.
zstep (ltac:(oF' 0x54e28%Z)) (ltac:(oD' 0x54e28%Z)).
zsd (ltac:(oF' 0x54e2c%Z)) (ltac:(oD' 0x54e2c%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x54e30%Z)) (ltac:(oD' 0x54e30%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd (ltac:(oF' 0x54e34%Z)) (ltac:(oD' 0x54e34%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W).
zsd (ltac:(oF' 0x54e38%Z)) (ltac:(oD' 0x54e38%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd (ltac:(oF' 0x54e3c%Z)) (ltac:(oD' 0x54e3c%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W).
fold (art_efas_frame M sp raw regs).
assert (Cmfa' : cellA (art_efas_frame M sp raw regs) (r + 24) 8 mfa) by (unfold art_efas_frame; unfold apart in A; zcell).
assert (Cpm' : cellA (art_efas_frame M sp raw regs) (ia + 56) 1 0) by (unfold art_efas_frame; zcell).
zld (ltac:(oF' 0x54e40%Z)) (ltac:(oD' 0x54e40%Z)) (r + 24) Cmfa'.
zstep (ltac:(oF' 0x54e44%Z)) (ltac:(oD' 0x54e44%Z)). zstep (ltac:(oF' 0x54e48%Z)) (ltac:(oD' 0x54e48%Z)).
zbft (ltac:(oF' 0x54e4c%Z)) (ltac:(oD' 0x54e4c%Z)).
zstep (ltac:(oF' 0x54e50%Z)) (ltac:(oD' 0x54e50%Z)). zstep (ltac:(oF' 0x54e54%Z)) (ltac:(oD' 0x54e54%Z)). zstep (ltac:(oF' 0x54e58%Z)) (ltac:(oD' 0x54e58%Z)). zstep (ltac:(oF' 0x54e5c%Z)) (ltac:(oD' 0x54e5c%Z)).
stepn (ltac:(oF' 0x54e60%Z)) (ltac:(oD' 0x54e60%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_m18 by lia.
replace ((total * 2 ^ 2 + 262143) / 2 ^ 18) with q by (apply (Z.div_unique_pos _ _ q rr); lia).
zstep (ltac:(oF' 0x54e64%Z)) (ltac:(oD' 0x54e64%Z)). zstep (ltac:(oF' 0x54e68%Z)) (ltac:(oD' 0x54e68%Z)).
zbft (ltac:(oF' 0x54e6c%Z)) (ltac:(oD' 0x54e6c%Z)).
zlbu (ltac:(oF' 0x54e70%Z)) (ltac:(oD' 0x54e70%Z)) (ia + 56) Cpm'.
zstep (ltac:(oF' 0x54e74%Z)) (ltac:(oD' 0x54e74%Z)). zstep (ltac:(oF' 0x54e78%Z)) (ltac:(oD' 0x54e78%Z)). zstep (ltac:(oF' 0x54e7c%Z)) (ltac:(oD' 0x54e7c%Z)). zstep (ltac:(oF' 0x54e80%Z)) (ltac:(oD' 0x54e80%Z)).
zbtk (ltac:(oF' 0x54e84%Z)) (ltac:(oD' 0x54e84%Z)).
zstep (ltac:(oF' 0x54eac%Z)) (ltac:(oD' 0x54eac%Z)). zstep (ltac:(oF' 0x54eb0%Z)) (ltac:(oD' 0x54eb0%Z)). zstep (ltac:(oF' 0x54eb4%Z)) (ltac:(oD' 0x54eb4%Z)). zstep (ltac:(oF' 0x54eb8%Z)) (ltac:(oD' 0x54eb8%Z)). zstep (ltac:(oF' 0x54ebc%Z)) (ltac:(oD' 0x54ebc%Z)). zstep (ltac:(oF' 0x54ec0%Z)) (ltac:(oD' 0x54ec0%Z)).
stepn (ltac:(oF' 0x54ec4%Z)) (ltac:(oD' 0x54ec4%Z)).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_efas_b_fn : ltac2:(TCodec.tc2 tcn__JbtPopulate2 "RK&5y5'QAyR0%211%5241'0y8%611%311p061'4'3&?r5(Q?+:(1%33A21%6251&Q@r2%22C1%;3C41r6+9%;3I19%>231r3%92J1%B3J31r7+B%B3Q01@%E231%G3O16'2&Ez%221I&G+2+R0%3221%72N1%9261':&B&@vJr9+Zcf8%Q53QA1Q3/01QAr8%756521H&A+1%Q;3QI1Q9+Zcg4%Q=3QI1Q;/01QI%63<41%Q;2QLQ7%832Q>1+;%QC3R11QA%Q?2R0QE%<3421+<%QG3R51QE+WJ%QD2R51%A3531+>%QL3R:1QJ%D331=+_YU@%QO3R;1QM/01R;%Q05O41JQA%Q33Q2J1p0Q51p0Q@1p0QF1p0QN1pR4R;1pR>R<1pRJR>1p>R?1pRHRE1").
Proof.
intros regs M rom p len H10 H9 H18 Hp.
zbft (ltac:(oF' 0x54ec8%Z)) (ltac:(oD' 0x54ec8%Z)). zstep (ltac:(oF' 0x54ecc%Z)) (ltac:(oD' 0x54ecc%Z)). zbft (ltac:(oF' 0x54ed0%Z)) (ltac:(oD' 0x54ed0%Z)).
zstep (ltac:(oF' 0x54ed4%Z)) (ltac:(oD' 0x54ed4%Z)). zstep (ltac:(oF' 0x54ed8%Z)) (ltac:(oD' 0x54ed8%Z)). zstep (ltac:(oF' 0x54edc%Z)) (ltac:(oD' 0x54edc%Z)).
stepn (ltac:(oF' 0x54ee0%Z)) (ltac:(oD' 0x54ee0%Z)).
zret.
Qed.
Section SE.
Local Abbreviation SEC_T_art_efas_c_fn := (ltac2:(TCodec.tc2 tcn__JbtPopulate2 "XD&5y5'QAyR0%211%5241'0y8%611%311p061'4'3&?rC(Q?+2(1%33A21%6251&Q@&Hr?+Q@%3221%52F1%>3F71rD+4%>3L1<%A231%;2L9%D3L21rE+8%D3Q21B%G231r:%B2Q31%K3Q331rF+B%K3Q91I%N231%Q03Q816rG+C%Q03Q>1N%Q3231r=%N2Q?1%Q73Q?31&D+R@%221K&E&G+R0%22Q:1%42J1&C+Vb\P0%2219%;21GrA%=241rB+T0%8221+Q?%>2QF1%@231'2z%F218%D29A%4221&;rL%211%L27R2%J2R3G%:221+TP0rI%Q1221rJ%K214%Q121N%Q52@QH%B21O&9&BrQ7rQ4%R:21Q:+Q0%645421&<rQ8rQ3rQ2rQ1rQ0%665:4321&7rQ6%RF21QF+QW`e0%442QH1R;%RI2AQI+RH%RK261%843QL1R?%RM2?QMrQ5&F%12RC;%QJ231%>45R21RErQ9%S421R4+TH%QO281%C43R71RJrQ:%S921R9+RiH%R42=1+@%I44R=21rQ;%S?21R?%L41R@BR2%R:2Q97%N416MR4rQ@%R=2Q6:%Q?4Q>219rQA%QA4Q@1Q9R9&8rQB%RC2B@u8%45QE321Q7rQC+Rj0%RH2A1%85QI315Q;rQD%T22<SE&QB%12TF;%=5QN43:1rQE%T72>K%@5R121=R0rQF+H%T;2>1%D5R531AR4rQG%T>2=R3%G5R821DR7rQH+Q8%TB2<1%K5R<31HR;':&@vJrQJ+Zcg4%TO3U;1TM/01U;rQI%756521<&A+1%U53UC1U3%3391C%U22UCH%532U51%U42UEQE%732TF1+9%U<3UJ1U:%U82UIQO%;3421+:%U@3UN1U>%U<2UM=%?3421+;%UD3V21UB%U@2V1QL%C3421+<%UH3V61UFrQ=%T=21F%UF2V71%I3641+=%UN3V<1UL%L331>%UK2V<RG%N32U61%UM2V>S>%Q032U31&=rQ<rQ>rQ?%48Q7QIR<R??321%Q>5Q=6QF1QC%Q@3SMQ81p0QB1p0QG1p0QK1p0R01p0R41p0R:1p0R?1p0RE1p0RH1p0RL1p0RO1p0S31p0S:1p0S@1p0SG1p0SL1p0T21p0T:1p0TB1p0TC1p0TD1p0TE1p0TH1p0TL1p0U01p0U11p0U51p0U;1p0U:1p0U@1p0UG1p0UJ1p0UO1p0V51p0V91p0VA1p0VG1p0VO1p0W61pQJWF1pQHWG1pQNWH1pQLWI1pR8WJ1pR6WK1pR4WL1pR<WM1pRBWN1pS8WO1pQDX01pS>X11pR2X21pS<X31pRNX41pRDX<1pRJX71p>X81pRHX>1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 4%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 5%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 6%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 7%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 8%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 9%nat 0%nat).
Variable r : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 10%nat 0%nat).
Variable nm : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 11%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 12%nat 0%nat).
Variable m1 : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 13%nat 0%nat).
Variable m2 : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 14%nat 0%nat).
Variable g8 : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 15%nat 0%nat).
Variable g9 : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 16%nat 0%nat).
Variable g18 : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 17%nat 0%nat).
Variable g19 : ltac:(sec_ty2 constr:(SEC_T_art_efas_c_fn) 18%nat 0%nat).
Lemma art_efas_c_fn : ltac:(sec_stmt2 constr:(SEC_T_art_efas_c_fn) 19%nat 0%nat).
Proof using Type regs M rom raw sp tp key tsd ctx t r nm len m1 m2 g8 g9 g18 g19.
intros H2 H4 H8 H18 H19 Hsp Hsp' IMG Hr Hr' Hnm Hlen Hret Hm1 Hm2 Ht Ht' Hg8 Hg9 Hg18 Hg19
W TSD A1 A2 A3 A4 A5 A6 A7 Wt Wr C1 C2 F8 F16 F24 F32 F40.
stepn (ltac:(oF' 0x54ee4%Z)) (ltac:(oD' 0x54ee4%Z)).
zcall (art_thread_stats_fn _ _ _ _ (sp - 48) tp key tsd ctx t).
change (U (347880 : bv 64)%bv) with 347880.
match goal with |- msteps _ (mkst _ _ ?X _) _ => set (MT := X) end.
assert (TT : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> apart (sp - 80) 32 a (Z.of_nat k) -> cellA M a k v -> cellA MT a k v).
{ intros a k v Ha Hak O C. unfold MT. unfold apart in O. do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). exact C. }
assert (WT : forall a k, wrA M a k -> wrA MT a k) by (intros a k Hw; unfold MT; do 2 apply wr_Wn; exact Hw).
assert (C1' : cellA MT (t + 2872) 8 m1) by (apply TT; [lia|cbn; lia|unfold apart in A5 |- *; cbn; lia|exact C1]).
assert (C2' : cellA MT (t + 2880) 8 m2) by (apply TT; [lia|cbn; lia|unfold apart in A5 |- *; cbn; lia|exact C2]).
zld (ltac:(oF' 0x54ee8%Z)) (ltac:(oD' 0x54ee8%Z)) (t + 2880) C2'. zld (ltac:(oF' 0x54eec%Z)) (ltac:(oD' 0x54eec%Z)) (t + 2872) C1'.
zstep (ltac:(oF' 0x54ef0%Z)) (ltac:(oD' 0x54ef0%Z)). zstep (ltac:(oF' 0x54ef4%Z)) (ltac:(oD' 0x54ef4%Z)).
zsd (ltac:(oF' 0x54ef8%Z)) (ltac:(oD' 0x54ef8%Z)) (t + 2872) (m1 + 1) ltac:(eapply (wr_wok _ _ _ _ (WT _ _ Wt)); lia).
zsd (ltac:(oF' 0x54efc%Z)) (ltac:(oD' 0x54efc%Z)) (t + 2880) (m2 + len) ltac:(apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wt)); lia).
zstep (ltac:(oF' 0x54f00%Z)) (ltac:(oD' 0x54f00%Z)).
zsd (ltac:(oF' 0x54f04%Z)) (ltac:(oD' 0x54f04%Z)) (r + 24) nm ltac:(do 2 apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wr)); lia).
zstep (ltac:(oF' 0x54f08%Z)) (ltac:(oD' 0x54f08%Z)). zstep (ltac:(oF' 0x54f0c%Z)) (ltac:(oD' 0x54f0c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => set (ME := X) end.
assert (TE : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> sp - 48 <= a -> a + Z.of_nat k <= sp -> cellA M a k v -> cellA ME a k v).
{ intros a k v Ha Hak Hlo Hhi C. unfold ME. unfold apart in A5, A6. do 3 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). apply TT; [lia|lia|unfold apart; lia|exact C]. }
assert (E8 : cellA ME (sp - 8) 8 (U raw)) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F8]).
assert (E16 : cellA ME (sp - 16) 8 g8) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F16]).
assert (E24 : cellA ME (sp - 24) 8 g9) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F24]).
assert (E32 : cellA ME (sp - 32) 8 g18) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F32]).
assert (E40 : cellA ME (sp - 40) 8 g19) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F40]).
zld (ltac:(oF' 0x54f10%Z)) (ltac:(oD' 0x54f10%Z)) (sp - 8) E8. zld (ltac:(oF' 0x54f14%Z)) (ltac:(oD' 0x54f14%Z)) (sp - 16) E16. zld (ltac:(oF' 0x54f18%Z)) (ltac:(oD' 0x54f18%Z)) (sp - 24) E24. zld (ltac:(oF' 0x54f1c%Z)) (ltac:(oD' 0x54f1c%Z)) (sp - 32) E32. zld (ltac:(oF' 0x54f20%Z)) (ltac:(oD' 0x54f20%Z)) (sp - 40) E40.
rewrite !Z_to_bv_bv_unsigned.
zstep (ltac:(oF' 0x54f24%Z)) (ltac:(oD' 0x54f24%Z)).
stepret (ltac:(oF' 0x54f28%Z)) (ltac:(oD' 0x54f28%Z)) raw ltac:(rwH; reflexivity).
unfold art_efas_c_mem. subst ME MT. zret.
Qed.
End SE.
End FPX.
