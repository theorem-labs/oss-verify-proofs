(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac JatLeaf JatPoison JatAllocG JatUnwind JatFree1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatFxIcpt () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocG."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatFxIcpt."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4bvmap"; "0M"; "0M1"; "5apart"; "5cell"; "5wr"]; ["6msteps"; "7hid"; "8art_fi_mem"; "9art_tsd"; ":getr"; ":mkst"; ":regupd"; ";mem_grows"; "<loaded_segments"; "0S"; "=In"; ">add"; ">le"; ">lt"; ">modulo"; ">mul"]; [">pow"; ">sub"; "0bot"; "0ctx"; "0fx"; "0key"; "0p"; "0qp"; "0r"; "0raw0"; "0regs"; "0regs1"; "0rom"; "?BV"; "?Z_to_bv"; "?bv"]; ["?bv_unsigned"; "0t"; "0top"; "0tp"; "0tsd"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_fi_mem (M : word -> option byte) (S : Z) (raw0 : word) (regs : bvmap 5 word) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (S - 8) (U raw0)) (S - 16) (U (getr regs 8))) (S - 24) (U (getr regs 9))) (S - 32) (U (getr regs 18))) (S - 40) (U (getr regs 19))) (S - 48) (U (getr regs 20))) (S - 56) (U (getr regs 21)).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_fi_a_fn := (ltac2:(TCodec.tc2 tcn__JatFxIcpt "S>&:y5'Q?yR0%211%5241'2y8%611%311p061'9'5&Dr6(Q=+1(3%33A21%6251r3%93A21r7+2%93G17%<231&Q>%12H7%@3H31r8+:%@3N1>%C231%E3M16&L&K+`PQoooPP0+XP0%3221r5%6221&M&Q0+Q?%22E1%42O1'4z%>21Q2+R0%82K1%:2Q51%6241&?&Hr;&Q1+TP0%22M1%645412'@&EvQ4r=+_Sf<%QB3QN1Q@/01QNr<%756521=&F+_Sh0%Q=2R41%339QF1r9+RR@%C221%QB2R91%835QE1+8%R03R>1QN%QF2R=7%<3421+9%R43RB1R2%QJ2RAQG%@3421+B%R83RF1R6r:%D3421+`dP8%R<3RH1R:/01RH&B%14KE6O%Q25Q1631Q8%Q43Q:L1p0Q61p0Q>1p0QF1p0QL1p0R41p0R:1p0RB1pR>RM1pQDRN1pRDS61pRJS11pHS21pRFS81")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_fi_a_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_fi_a_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_fi_a_fn) 2%nat 0%nat).
Variable raw0 : ltac:(sec_ty2 constr:(SEC_T_art_fi_a_fn) 3%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_fi_a_fn) 4%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_fi_a_fn) 5%nat 0%nat).
Lemma art_fi_a_fn : ltac:(sec_stmt2 constr:(SEC_T_art_fi_a_fn) 6%nat 0%nat).
Proof using Type regs M rom raw0 S p.
intros H1 H2 H10 HS HS' Hp W.
zstep (ltac:(oF' 0x78ecc%Z)) (ltac:(oD' 0x78ecc%Z)).
zsd (ltac:(oF' 0x78ed0%Z)) (ltac:(oD' 0x78ed0%Z)) (S - 8) (U raw0) ltac:(rewok W). zsd (ltac:(oF' 0x78ed4%Z)) (ltac:(oD' 0x78ed4%Z)) (S - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x78ed8%Z)) (ltac:(oD' 0x78ed8%Z)) (S - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x78edc%Z)) (ltac:(oD' 0x78edc%Z)) (S - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x78ee0%Z)) (ltac:(oD' 0x78ee0%Z)) (S - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x78ee4%Z)) (ltac:(oD' 0x78ee4%Z)) (S - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x78ee8%Z)) (ltac:(oD' 0x78ee8%Z)) (S - 56) (U (getr regs 21)) ltac:(rewok W).
zstep (ltac:(oF' 0x78eec%Z)) (ltac:(oD' 0x78eec%Z)). zstep (ltac:(oF' 0x78ef0%Z)) (ltac:(oD' 0x78ef0%Z)). zstep (ltac:(oF' 0x78ef4%Z)) (ltac:(oD' 0x78ef4%Z)). zstep (ltac:(oF' 0x78ef8%Z)) (ltac:(oD' 0x78ef8%Z)).
stepn (ltac:(oF' 0x78efc%Z)) (ltac:(oD' 0x78efc%Z)).
unfold art_fi_mem. zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_fi_b := (ltac2:(TCodec.tc2 tcn__JatFxIcpt "]>&:y5'Q?yR0%211%5241'2y8%611%311p061'9'5&Dr=(Q=+2(3%33A21%6251&Q>&Q1r:+RR@%3221%52F1%>3F71r>+4%>3L1<%A231r8%<2M1%E3M31r?+8%E3Q31C%H231r<%C2Q41%L3Q431r@+9%L3Q:1J%O231%Q13Q916rA+:%Q13Q?1O%Q4231+QW_h0%O2Q@1%Q83Q@31&L&K+`PQoooPP0+XP0%3221%521H&M&Q0+Q?%22Q>1%42F1'4z%=21I%3214&O+Q0%:2QF1%321N&N%12K3%D231%QO3R0M1+TP0%H21Q7%H2R02%D21A&A'8%L2QG6+RPP0%O221+VbTP0%Q121QK%6231%811&=rF%R621?%34QJ@1Q4rG%R921B%64QAC1Q7rB%Q;21E%Q=21?%Q>2>3%C221%E11rC%>47K1K+RPX0%QD21<rH%QE21R8%QG21G%QH2J@+QP0%QI251%QK21KrE%QM2QA1%QH22I%QD221+QO%QJ2S61%QL2J1&?&HrQ2rQ0%S721Q@%54431QArQ3rJ%84721QD&CrQ4rOrNrMrLrK%76654321&>rQ5+QW^^Hu1+1%55E4321rQ6+QW^_Lu4+N%:5J4321rQ7+QVYa8u8+QibQ8%?5O4321rQ8+Q2%S5241%C5Q331@?rQ9+SS0%S92Q41%G5Q731DROrQ:rQ1+Q8%S>221%L5Q<41IS4rQ;%SA2Q=T4%O5Q?21B6rQ<+@%SE2Q=1%Q35QC31F:rQ=%SH2SLT;%S;2T<B%SJ221%Q85QH41KS@'6'@&EvQ4rQA+_Sh0%U93UE1U7/01UErQ@rQ?%8576321r2+cWoH%U@3UL1U>/01ULr1%>5=5217%@3R:71%UE3V3QGUC%UH281+`Ub0%UH3V41UF/01V4%UM3V541%UM2=UHrQ>+RU0%UH221%UJ2V;1%V33V;51%V32CU0%UL26UJ%UN2V?1%V73V?31+;%V63VD1V4%V92I1+_TP4%V42VE1%V=3VE31+<%V<3VJ1V:%V?2O1%V92VJB%VB3VJ21+=%VA3VO1V?%VD2Q41%V>2VORC%VG3VO21+>%VF3W41VD%VI2Q91%VC2W4RM%VL3W421+?%VK3W91VI%VN2Q>1%VH2W9RJ%W13W921+H%W03W>1VN%W32QC1+QoO%UL2RN1%VO2W@1%W83W@41%W82QHVH%W22WCR@%W;3WC21%WF1WG&J(0+3%W=3WK1W;+I%W?3WM1W=+J%WA3WO1W?+K%WC3X11WA(1%11<%;3=31%<3>61%=3?91%>3@<1%@3AR81r4%WN21R>rQC%X021R@%X23X:31p061pRBH1&G%12RHRA&7+RW0%X02RJ1&Q@%12XDRF%W3231+R0%X52RO1%W0241%VL241%:11%82XKS1%W92T2T1%XD3XE21%>11r3%I11%H12%XI3XL21p051p0:1pS<Y41+RRH%XE2RO1+_TS0%U35UCS;2TF1+RS0%XI2S31%U65UFS>1TIS4+RS8%XL2S61%U95UISA1TLT5+RS@%XO2S91%Y63YBRNY4/01YB%Q12YD1%U?5UOSG4U21+RSH%Y52S?1%UB5V2SJ1U5U>+RT0%Y82SB1%UE5V5SM1U8S=+RT8%Y;2SE1+RA%Y=2SG1%UJ5V:T23U=1+RT@%Y@2SJ1+F%YH3Z61YF%YK2TB1%QC2Z61%V15VAT95UD1+RTH%YG2T11+G%YO3Z=1YM%Z22TI1%QJ2Z=1%V85VHT@5UK1%Z52TLS3%QM2Z@1%V;5VKTCT7UN1+RR0%Z12T;1%V>5VNTFT6V11+RR8%Z42T>1%VA5W1TI1V9XI+RR4%Z72TA1%VD5W4TL1V<XL%Z92TCXB%W74W6TN1XC%Y0231%Y1271%Y22;1%Y32?1%Y42C1%Y52K1%Y62Q31%Y72Q91%Y82Q=1%Y92QA1%Y:2QH1%Y;2QL1%Y<2R01%Y=2R51%Y>2RL1%Y?2RO1%Y@2SI1%YA2SM1%YB2T51%YC2T;1%YD2TA1%YE2TG1%YF2TM1%YG2U41%YH2U91%YI2U@1%YJ2UG1qJ[A1%V:2[B1qRH[H1%V<2[I1p0V>1p0VD1p0VI1p0VM1p0W31p0W81p0W=1p0WC1p0WI1p0X01p0X91p0X=1p0XD1p0XH1p0XM1p0Y11p0Y31p0Y71p0Y:1p0Y=1p0YD1p0YH1p0YM1p0Z71p0Z:1p0Z=1p0ZF1p0ZK1p0[11p0[81p0[@1p0[F1p0[N1p0\61pR6\F1pS6\G1pS4\H1pR8\I1pS:\J1pR<\K1pS8\L1pR@\M1pR>\N1pQD\O1pRJ]11pH]21pRF]81")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_fi_b) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_fi_b) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_fi_b) 2%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_art_fi_b) 3%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_fi_b) 4%nat 0%nat).
Variable qp : ltac:(sec_ty2 constr:(SEC_T_art_fi_b) 5%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_fi_b) 6%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_fi_b) 7%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_fi_b) 8%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_fi_b) 9%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_fi_b) 10%nat 0%nat).
Variable top : ltac:(sec_ty2 constr:(SEC_T_art_fi_b) 11%nat 0%nat).
Variable bot : ltac:(sec_ty2 constr:(SEC_T_art_fi_b) 12%nat 0%nat).
Lemma art_fi_b : ltac:(sec_stmt2 constr:(SEC_T_art_fi_b) 13%nat 0%nat).
Proof using Type regs M rom S p qp tp key tsd ctx t top bot.
intros H2 H4 H8 H9 H10 HS HS' Hp Eqp Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd Hbt Htop
W Wt TSD Ci Cctx Cg38 Cfast Cunw C40 C8 C16 Cmap.
pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
assert (Hqp : 0 <= qp < 2 ^ 15) by (pose proof (Z.mod_pos_bound p (2 ^ 32) ltac:(lia)); lia).
assert (Hqp' : p / 2 ^ 32 = qp). { symmetry. apply (Z.div_unique_pos _ (2 ^ 32) qp (p mod 2 ^ 32)); [pose proof (Z.mod_pos_bound p (2 ^ 32)); lia|lia]. }
eexists _, _. split.
-
stepn (ltac:(oF' 0x78f00%Z)) (ltac:(oD' 0x78f00%Z)). rwH. rewrite art_zb_srli by lia. rewrite (Z.div_small p (2 ^ 47)) by lia.
zbft (ltac:(oF' 0x78f04%Z)) (ltac:(oD' 0x78f04%Z)).
stepn (ltac:(oF' 0x78f08%Z)) (ltac:(oD' 0x78f08%Z)). rwH. rewrite art_zb_srli by lia. rewrite Hqp'.
stepn (ltac:(oF' 0x78f0c%Z)) (ltac:(oD' 0x78f0c%Z)). rwH. rewrite art_zb_slli by lia.
zstep (ltac:(oF' 0x78f10%Z)) (ltac:(oD' 0x78f10%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmap' : cellA X (0x13bf00 + qp * 2 ^ 3 + 8) 8 0) by (replace (0x13bf00 + qp * 2 ^ 3 + 8) with (0x13bf00 + 8 + 8 * qp) by lia; recell Cmap) end.
zld (ltac:(oF' 0x78f14%Z)) (ltac:(oD' 0x78f14%Z)) (0x13bf00 + qp * 2 ^ 3 + 8) Cmap'.
stepfence (ltac:(oF' 0x78f18%Z)) (ltac:(oD' 0x78f18%Z)).
zbtk (ltac:(oF' 0x78f1c%Z)) (ltac:(oD' 0x78f1c%Z)).
zstep (ltac:(oF' 0x78fa4%Z)) (ltac:(oD' 0x78fa4%Z)). zstep (ltac:(oF' 0x78fa8%Z)) (ltac:(oD' 0x78fa8%Z)). zstep (ltac:(oF' 0x78fac%Z)) (ltac:(oD' 0x78fac%Z)). zstep (ltac:(oF' 0x78fb0%Z)) (ltac:(oD' 0x78fb0%Z)). zstep (ltac:(oF' 0x78fb4%Z)) (ltac:(oD' 0x78fb4%Z)).
zsd (ltac:(oF' 0x78fb8%Z)) (ltac:(oD' 0x78fb8%Z)) (S - 72) 0 ltac:(rewok W).
zsd (ltac:(oF' 0x78fbc%Z)) (ltac:(oD' 0x78fbc%Z)) (S - 2128) (S - 2112) ltac:(rewok W).
zsd (ltac:(oF' 0x78fc0%Z)) (ltac:(oD' 0x78fc0%Z)) (S - 2120) 0 ltac:(rewok W). rewrite (Wn8_zero_split _ (S - 2120)) by lia. replace (S - 2120 + 4) with (S - 2116) by lia.
stepn (ltac:(oF' 0x78fc4%Z)) (ltac:(oD' 0x78fc4%Z)).
zcall (art_malloc_ctx_fn _ _ _ _).
zstep (ltac:(oF' 0x78fc8%Z)) (ltac:(oD' 0x78fc8%Z)).
zbtk (ltac:(oF' 0x78fcc%Z)) (ltac:(oD' 0x78fcc%Z)).
stepn (ltac:(oF' 0x79000%Z)) (ltac:(oD' 0x79000%Z)).
zcall (art_get_pc_fn _ _ _ _).
zstep (ltac:(oF' 0x79004%Z)) (ltac:(oD' 0x79004%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg38' : cellA X 0x132628 8 0x1cc828) by zcell; assert (Cfast' : cellA X (0x1cc828 + 34) 1 1) by zcell end.
zld (ltac:(oF' 0x79008%Z)) (ltac:(oD' 0x79008%Z)) 0x132628 Cg38'. zlbu (ltac:(oF' 0x7900c%Z)) (ltac:(oD' 0x7900c%Z)) (0x1cc828 + 34) Cfast'.
zstep (ltac:(oF' 0x79010%Z)) (ltac:(oD' 0x79010%Z)).
stepn (ltac:(oF' 0x79014%Z)) (ltac:(oD' 0x79014%Z)).
zcall (art_malloc_ctx_fn _ _ _ _).
zstep (ltac:(oF' 0x79018%Z)) (ltac:(oD' 0x79018%Z)). zstep (ltac:(oF' 0x7901c%Z)) (ltac:(oD' 0x7901c%Z)). zstep (ltac:(oF' 0x79020%Z)) (ltac:(oD' 0x79020%Z)).
stepn (ltac:(oF' 0x79024%Z)) (ltac:(oD' 0x79024%Z)). rwH. rewrite art_zb_and by lia. rewrite art_land_full_l by lia.
zstep (ltac:(oF' 0x79028%Z)) (ltac:(oD' 0x79028%Z)).
zsd (ltac:(oF' 0x7902c%Z)) (ltac:(oD' 0x7902c%Z)) (S - 72) S ltac:(rewok W).
zbtk (ltac:(oF' 0x79030%Z)) (ltac:(oD' 0x79030%Z)).
zstep (ltac:(oF' 0x79044%Z)) (ltac:(oD' 0x79044%Z)). zstep (ltac:(oF' 0x79048%Z)) (ltac:(oD' 0x79048%Z)). zstep (ltac:(oF' 0x7904c%Z)) (ltac:(oD' 0x7904c%Z)). zstep (ltac:(oF' 0x79050%Z)) (ltac:(oD' 0x79050%Z)). zstep (ltac:(oF' 0x79054%Z)) (ltac:(oD' 0x79054%Z)). zstep (ltac:(oF' 0x79058%Z)) (ltac:(oD' 0x79058%Z)).
stepn (ltac:(oF' 0x7905c%Z)) (ltac:(oD' 0x7905c%Z)).
zstep (ltac:(oF' 0x81524%Z)) (ltac:(oD' 0x81524%Z)).
zsd (ltac:(oF' 0x81528%Z)) (ltac:(oD' 0x81528%Z)) (S - 2136) 0x79060 ltac:(rewok W). zsd (ltac:(oF' 0x8152c%Z)) (ltac:(oD' 0x8152c%Z)) (S - 2144) S ltac:(rewok W). zsd (ltac:(oF' 0x81530%Z)) (ltac:(oD' 0x81530%Z)) (S - 2152) p ltac:(rewok W).
zsd (ltac:(oF' 0x81534%Z)) (ltac:(oD' 0x81534%Z)) (S - 2160) (U (0x79004 : bv 64)%bv) ltac:(rewok W). zsd (ltac:(oF' 0x81538%Z)) (ltac:(oD' 0x81538%Z)) (S - 2168) 1 ltac:(rewok W). zsd (ltac:(oF' 0x8153c%Z)) (ltac:(oD' 0x8153c%Z)) (S - 2176) (S - 2128) ltac:(rewok W).
zsd (ltac:(oF' 0x81540%Z)) (ltac:(oD' 0x81540%Z)) (S - 2184) (S - 81) ltac:(rewok W). zsd (ltac:(oF' 0x81544%Z)) (ltac:(oD' 0x81544%Z)) (S - 2192) (U (getr regs 22)) ltac:(rewok W).
zsd (ltac:(oF' 0x81548%Z)) (ltac:(oD' 0x81548%Z)) (S - 2200) (U (getr regs 23)) ltac:(rewok W). zsd (ltac:(oF' 0x8154c%Z)) (ltac:(oD' 0x8154c%Z)) (S - 2208) (U (getr regs 24)) ltac:(rewok W).
zstep (ltac:(oF' 0x81550%Z)) (ltac:(oD' 0x81550%Z)). zstep (ltac:(oF' 0x81554%Z)) (ltac:(oD' 0x81554%Z)). zstep (ltac:(oF' 0x81558%Z)) (ltac:(oD' 0x81558%Z)). zstep (ltac:(oF' 0x8155c%Z)) (ltac:(oD' 0x8155c%Z)). zstep (ltac:(oF' 0x81560%Z)) (ltac:(oD' 0x81560%Z)). zstep (ltac:(oF' 0x81564%Z)) (ltac:(oD' 0x81564%Z)).
zsw (ltac:(oF' 0x81568%Z)) (ltac:(oD' 0x81568%Z)) (S - 2120) 0 ltac:(rewok W).
stepn (ltac:(oF' 0x8156c%Z)) (ltac:(oD' 0x8156c%Z)).
zcall (art_asan_inited_fn _ _ _ _).
zbft (ltac:(oF' 0x81570%Z)) (ltac:(oD' 0x81570%Z)).
stepn (ltac:(oF' 0x81574%Z)) (ltac:(oD' 0x81574%Z)).
zcall (art_cur_thread_fn _ _ _ _ (S - 2208) tp key tsd ctx t).
{ unfold art_tsd. repeat split; try lia; zcell. }
zbft (ltac:(oF' 0x81578%Z)) (ltac:(oD' 0x81578%Z)).
zstep (ltac:(oF' 0x8157c%Z)) (ltac:(oD' 0x8157c%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cunw' : cellA X (t + 2047 + 1121) 1 0) by (replace (t + 2047 + 1121) with (t + 3168) by lia; zcell) end.
zlbu (ltac:(oF' 0x81580%Z)) (ltac:(oD' 0x81580%Z)) (t + 2047 + 1121) Cunw'.
zstep (ltac:(oF' 0x81584%Z)) (ltac:(oD' 0x81584%Z)).
zsb (ltac:(oF' 0x81588%Z)) (ltac:(oD' 0x81588%Z)) (t + 2047 + 1121) 1 ltac:(rewok Wt).
zbft (ltac:(oF' 0x8158c%Z)) (ltac:(oD' 0x8158c%Z)).
zstep (ltac:(oF' 0x81590%Z)) (ltac:(oD' 0x81590%Z)).
stepn (ltac:(oF' 0x81594%Z)) (ltac:(oD' 0x81594%Z)).
zcall (art_stack_top_fn _ _ _ _ t top bot).
zstep (ltac:(oF' 0x81598%Z)) (ltac:(oD' 0x81598%Z)). zstep (ltac:(oF' 0x8159c%Z)) (ltac:(oD' 0x8159c%Z)).
stepn (ltac:(oF' 0x815a0%Z)) (ltac:(oD' 0x815a0%Z)).
zcall (art_stack_bottom_fn _ _ _ _ t top bot).
zstep (ltac:(oF' 0x815a4%Z)) (ltac:(oD' 0x815a4%Z)).
zbft (ltac:(oF' 0x815a8%Z)) (ltac:(oD' 0x815a8%Z)).
zstep (ltac:(oF' 0x815ac%Z)) (ltac:(oD' 0x815ac%Z)). zstep (ltac:(oF' 0x815b0%Z)) (ltac:(oD' 0x815b0%Z)). zstep (ltac:(oF' 0x815b4%Z)) (ltac:(oD' 0x815b4%Z)). zstep (ltac:(oF' 0x815b8%Z)) (ltac:(oD' 0x815b8%Z)). zstep (ltac:(oF' 0x815bc%Z)) (ltac:(oD' 0x815bc%Z)). zstep (ltac:(oF' 0x815c0%Z)) (ltac:(oD' 0x815c0%Z)). zstep (ltac:(oF' 0x815c4%Z)) (ltac:(oD' 0x815c4%Z)).
stepn (ltac:(oF' 0x815c8%Z)) (ltac:(oD' 0x815c8%Z)).
stepn (ltac:(oF' 0x8163c%Z)) (ltac:(oD' 0x8163c%Z)).
zcall (art_unwind_fn _ _ _ _ (S - 2208) (S - 2128) 0x79004 S top bot).
apply mst_refl.
- zsplit.
all: lazymatch goal with
| |- getr _ _ = _ => gres; rwH; first [reflexivity | f_equal; lia | bveq]
| |- forall r : reg, In r _ -> _ => intros r Hr; cbn [In] in Hr; destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; gres; reflexivity
| |- mem_grows _ _ => repeat (eapply mem_grows_trans; [|apply Wn_grows]); apply mem_grows_refl
| |- forall x : word, _ => intros x N1 N2; zagree
| |- wr _ _ _ _ => zwr
| |- cell _ _ _ _ _ => zcell
end.
Qed.
End SE.
End FPX.
