(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac JbtLeaf JbtAllocG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtFxBatch1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFxBatch1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1cons"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0L"; "4bvmap"; "0M"; "5apart"; "5cell"]; ["5wr"; "6msteps"; "7ret_ok"; "8art_enq_frame"; "8art_enq_new_mem"; "9getr"; "9mkst"; "9regupd"; ":loaded_segments"; ";In"; "<add"; "<le"; "<lt"; "<modulo"; "<mul"; "<pow"]; ["<sub"; "0b"; "0bytes"; "0c"; "0ca"; "0cnt"; "0fx"; "0m"; "0n"; "0r"; "0raw"; "0regs"; "0regs'"; "0rom"; "0sp"; "0spb"]; ["0st"; "=BV"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0sv"; "0w"; "0x18"; "0x19"; "0x20"; "0x21"; "0x8"; "0x9"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_enq_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)))
(sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21)).
Definition art_enq_new_mem (M : word -> option byte) (c ca L B bytes b m n cnt sv : Z) : word -> option byte :=
Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 M (ca + 1920) (cnt - 1)) (ca + 2576) (sv + 8192)) b 0) (b + 8) (n + 8192)) (b + 16) 1) (b + 24) m)
(if L =? 0 then c + 8 else B) b) c (L + 1)) (c + 16) b) (c + 24) (bytes + (n + 8192)).
Section FPX. Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_enq_new_tail_fn := (ltac2:(TCodec.tc2 tcn__JbtFxBatch1 "\B&<y5'QCyR0%211%5241'3y8%611%311p061':&Jr?&N+H&O+2+Q0%3221%6251%9281+@r;%:221%=241'6&ErG(QA(4%23N>1%5241&QB&Q0rC+R0%3221%52Q31%=3Q371rH+:%=3Q91<%@231%;2Q99%C3Q921rI+;%C3Q?1B%F231%H3Q>16rJ+=%H3QD1G%K231r>%G2QE1%O3QE31rK+>%O3QK1N%Q2231%Q43QJ16rL+?%Q43R01Q3%Q7231%Q93QO1;&B%11B&K%12Q3D&L%QI2QHQ5%22@1z%621B%R12>QK%6215%924@rM+Ra8%R6221%;21:&MrN+R`@%R;221+8%5221%R03R?1?'9rO%RA21<+RPP0%I221+Vb\P0%K215%7231rA+XP0%RI221%N21M'5%Q22MH%Q12IRF%3221rQ1%Q62Q11+QO%RN2RM1%Q7241%9241rQ2%S621J%Q;21Q:%Q>2Q93rQ3rQ0%S;221%S<21D%QA21Q@%QD2Q?5%QC26QB%E221+1%QH21=%QI2>S9%I221%QI2@QH%K2>1&>rQD%S321S1rQC%442S31SErQE%S721S5+Ql0%SO251+dH%:44S921rQF%S=21S;rQ4%>42S=1SO&8%SI3T8=R8%211rQH%SD21SB%D41SCAQOp041rQG%T>2<@%H42T91?rQ7%J48T;1T;%T43TC@RC%=11rQJ%N41T?CR9p031rQI%TH21JrQ9%Q342J1TD%T=3TLBRL%F11rQK%TN21Q0%Q841OFRCp041%TC3U2:S2%L11rQ<%Q=41TN=RHp031&@&HrR1rQM%44321U4rR2%U<23Q>+4%847321rR3rQN%UA21S7%<4;31S6rR4rQ?%?4>21U?%U83UG6SG%QA11rR6%C4B19S=p031&?+Ql@%UM2E1%U82Q7R=%UM2B1%V0231u4rQL%85L;321rR7+Ql8%V62K1u8%=5Q1421S@rR8%V:2KT0%@5Q4214QGrR9+QWToH%C5Q7217OrR:%E5Q91H9Q1%V33VBNTB%R<11rR<%VD2;V:%J5Q>21>Q2p041%VG2>VD%M5QA51AQ9rR=%V42;T>&QDrR;%22W61%Q35QG54G1rR>%V:24VFrQO%Q75QK32K1rR?%V>2AW1%Q:5QN21N4rR@%VA2>W1%Q=5R121Q17rRA+Q8%VE2<1%QA5R531Q5;rRB+Q@%VI2<1%QE5R931Q9?rRC+QH%VM2=1%QI5R=31Q=C'A&FvQ6rRE+ZiS8%W93X31W8/01X3rRD%756521<&G%W>3X:T>W=%2381C%W<2X:H%432W?1%WB3X>UGWArR5%W@2X>1%83431+9%WG3XC1WF%WD2XBRF%<3421%X;2R2UC%X<2Q@1%WH2XF1%@34W:1+<%WO3XK1WN%XA2QHU0%WM2XK1%E3531%WO2XM9%G32W51%X12XOQM%I32W21%X73Y3X>X6+SPPPPPP0%X52Y31%M3431+B%X<3Y81X;%X92Y7S?%Q13421+C%X@3Y<1X?%X=2Y;SG%Q53421+D%XD3Y@1XC%XA2Y?SN%Q93421+E%XH3YD1XGrR0%XF2YD1%Q>3531&D%1;QBR8R;RERKRBR=S2S5S:SF%QI5QH3R21QN%QK3T9QC1p0QM1p0R21p0R71p0R<1p0R@1p0RD1p0RI1p0S01p0S31p0S:1p0S=1p0SA1p0SE1p0SK1p0T51p0T;1p0T?1p0TD1p0TI1p0TO1p0U51p0U<1p0UA1p0UG1p0UJ1p0UN1p0V61p0V;1p0VB1p0VH1p0VI1p0VJ1p0VK1p0VL1p0VM1p0VN1p0W11p0W61p0WG1p0W;1p0WA1p0WC1p0WK1p0WH1p0WO1p0X41p0X:1p0X:1p0XC1p0XK1p0Y01p0Y21p0Y51p0Y81p0Y<1p0Y?1p0YB1p0YH1p0YN1p0Z61p0Z<1p0ZC1tR4[@[21pSF[A1pSD[B1pSB[C1pS@[D1pSJ[E1pSH[F1pS<[G1pR<[H1pRB[I1pR@[J1pS>[K1pR6[L1p2[M1pH[N1pS0[O1pR:\01pR8\11pRN\21pRF\:1pRL\51pL\61pRH\<1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 5%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 6%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 7%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 8%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 9%nat 0%nat).
Variable bytes : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 10%nat 0%nat).
Variable w : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 11%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 12%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 13%nat 0%nat).
Variable cnt : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 14%nat 0%nat).
Variable sv : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 15%nat 0%nat).
Variable x8 : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 16%nat 0%nat).
Variable x9 : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 17%nat 0%nat).
Variable x18 : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 18%nat 0%nat).
Variable x19 : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 19%nat 0%nat).
Variable x20 : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 20%nat 0%nat).
Variable x21 : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_tail_fn) 21%nat 0%nat).
Lemma art_enq_new_tail_fn : ltac:(sec_stmt2 constr:(SEC_T_art_enq_new_tail_fn) 22%nat 0%nat).
Proof using Type regs M rom raw sp c ca spb L B bytes w m n cnt sv x8 x9 x18 x19 x20 x21.
intros b H2 H10 H11 H13 H14 H15 Hret
Hsp Hsp' Hc Hc' Hca Hca' Hca8 Hcai Hspb Hb Hw HL HB HB' Hby Hby' Hn Hm Hcnt Hsv Hx8 Hx9 Hx18 Hx19 Hx20 Hx21
A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 Wc Wcnt Wst Wb WB Cw Ccs Csv Cspb CL CB Cby F1 F8 F9 F18 F19 F20 F21.
assert (Eb : b = spb + 24 * 2 ^ 32 + 16 * w) by reflexivity. clearbody b.
zstep (ltac:(oF' 0x56468%Z)) (ltac:(oD' 0x56468%Z)).
stepn (ltac:(oF' 0x5646c%Z)) (ltac:(oD' 0x5646c%Z)). rwH. rewrite art_zb_slli by lia.
zsw (ltac:(oF' 0x56470%Z)) (ltac:(oD' 0x56470%Z)) (ca + 1920) (cnt - 1) ltac:(zwok').
stepn (ltac:(oF' 0x56474%Z)) (ltac:(oD' 0x56474%Z)). rwH. rewrite art_zb_srli by lia. replace ((cnt + -1) * 2 ^ 32 / 2 ^ 30) with (4 * (cnt - 1)) by (replace ((cnt + -1) * 2 ^ 32) with (4 * (cnt - 1) * 2 ^ 30) by lia; rewrite Z_div_mult by lia; reflexivity).
zstep (ltac:(oF' 0x56478%Z)) (ltac:(oD' 0x56478%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Ccs' : cellA X (ca + 1928) 8 8192) by zcell;
assert (Cw' : cellA X (ca + 4 * (cnt - 1) + 1936) 4 w) by (replace (ca + 4 * (cnt - 1) + 1936) with (ca + 1936 + 4 * (cnt - 1)) by lia; zcell);
assert (Csv' : cellA X (ca + 2576) 8 sv) by zcell; assert (Wst' : wokA X (ca + 2576) 8) by zwok end.
zld (ltac:(oF' 0x5647c%Z)) (ltac:(oD' 0x5647c%Z)) (ca + 1928) Ccs'.
zstep (ltac:(oF' 0x56480%Z)) (ltac:(oD' 0x56480%Z)). zstep (ltac:(oF' 0x56484%Z)) (ltac:(oD' 0x56484%Z)).
zlwu (ltac:(oF' 0x56488%Z)) (ltac:(oD' 0x56488%Z)) (ca + 4 * (cnt - 1) + 1936) Cw'.
zamoadd_d (ltac:(oF' 0x5648c%Z)) (ltac:(oD' 0x5648c%Z)) (ca + 2576) sv 8192 Csv' ltac:(exact Wst').
zstep (ltac:(oF' 0x56490%Z)) (ltac:(oD' 0x56490%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X 0x1393f8 8 spb) by zcell end.
zld (ltac:(oF' 0x56494%Z)) (ltac:(oD' 0x56494%Z)) 0x1393f8 Cspb'.
zstep (ltac:(oF' 0x56498%Z)) (ltac:(oD' 0x56498%Z)). zstep (ltac:(oF' 0x5649c%Z)) (ltac:(oD' 0x5649c%Z)). zstep (ltac:(oF' 0x564a0%Z)) (ltac:(oD' 0x564a0%Z)). zstep (ltac:(oF' 0x564a4%Z)) (ltac:(oD' 0x564a4%Z)). zstep (ltac:(oF' 0x564a8%Z)) (ltac:(oD' 0x564a8%Z)).
zbft (ltac:(oF' 0x564ac%Z)) (ltac:(oD' 0x564ac%Z)).
zstep (ltac:(oF' 0x564b0%Z)) (ltac:(oD' 0x564b0%Z)). zstep (ltac:(oF' 0x564b4%Z)) (ltac:(oD' 0x564b4%Z)). zstep (ltac:(oF' 0x564b8%Z)) (ltac:(oD' 0x564b8%Z)).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell end.
zld (ltac:(oF' 0x564bc%Z)) (ltac:(oD' 0x564bc%Z)) c CL'.
zsd (ltac:(oF' 0x564c0%Z)) (ltac:(oD' 0x564c0%Z)) b 0 ltac:(zwok').
zsd (ltac:(oF' 0x564c4%Z)) (ltac:(oD' 0x564c4%Z)) (b + 8) (n + 8192) ltac:(zwok').
zsd (ltac:(oF' 0x564c8%Z)) (ltac:(oD' 0x564c8%Z)) (b + 16) 1 ltac:(zwok').
zsd (ltac:(oF' 0x564cc%Z)) (ltac:(oD' 0x564cc%Z)) (b + 24) m ltac:(zwok').
destruct (Z.eq_dec L 0) as [EL|NL].
- zbtk (ltac:(oF' 0x564d0%Z)) (ltac:(oD' 0x564d0%Z)).
zsd (ltac:(oF' 0x5650c%Z)) (ltac:(oD' 0x5650c%Z)) (c + 8) b ltac:(zwok').
zsd (ltac:(oF' 0x56510%Z)) (ltac:(oD' 0x56510%Z)) c (L + 1) ltac:(zwok').
zsd (ltac:(oF' 0x56514%Z)) (ltac:(oD' 0x56514%Z)) (c + 16) b ltac:(zwok').
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell end.
zld (ltac:(oF' 0x56518%Z)) (ltac:(oD' 0x56518%Z)) (c + 24) Cby'.
zstep (ltac:(oF' 0x5651c%Z)) (ltac:(oD' 0x5651c%Z)).
zsd (ltac:(oF' 0x56520%Z)) (ltac:(oD' 0x56520%Z)) (c + 24) (bytes + (n + 8192)) ltac:(zwok').
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (F1' : cellA X (sp - 8) 8 (U raw)) by zcell; assert (F8' : cellA X (sp - 16) 8 x8) by zcell; assert (F9' : cellA X (sp - 24) 8 x9) by zcell;
assert (F18' : cellA X (sp - 32) 8 x18) by zcell; assert (F19' : cellA X (sp - 40) 8 x19) by zcell; assert (F20' : cellA X (sp - 48) 8 x20) by zcell;
assert (F21' : cellA X (sp - 56) 8 x21) by zcell end.
zld (ltac:(oF' 0x56524%Z)) (ltac:(oD' 0x56524%Z)) (sp - 8) F1'. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56528%Z)) (ltac:(oD' 0x56528%Z)) (sp - 16) F8'. zld (ltac:(oF' 0x5652c%Z)) (ltac:(oD' 0x5652c%Z)) (sp - 24) F9'. zld (ltac:(oF' 0x56530%Z)) (ltac:(oD' 0x56530%Z)) (sp - 32) F18'.
zld (ltac:(oF' 0x56534%Z)) (ltac:(oD' 0x56534%Z)) (sp - 40) F19'. zld (ltac:(oF' 0x56538%Z)) (ltac:(oD' 0x56538%Z)) (sp - 48) F20'. zld (ltac:(oF' 0x5653c%Z)) (ltac:(oD' 0x5653c%Z)) (sp - 56) F21'.
zstep (ltac:(oF' 0x56540%Z)) (ltac:(oD' 0x56540%Z)).
stepret (ltac:(oF' 0x56544%Z)) (ltac:(oD' 0x56544%Z)) raw ltac:(gres; reflexivity).
unfold art_enq_new_mem. rewrite (proj2 (Z.eqb_eq L 0) EL). zret.
- zbft (ltac:(oF' 0x564d0%Z)) (ltac:(oD' 0x564d0%Z)).
specialize (A4 NL). specialize (A7 NL). specialize (A9 NL). specialize (A10 NL). specialize (WB NL). specialize (CB NL).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CB' : cellA X (c + 16) 8 B) by zcell end.
zld (ltac:(oF' 0x564d4%Z)) (ltac:(oD' 0x564d4%Z)) (c + 16) CB'.
zsd (ltac:(oF' 0x564d8%Z)) (ltac:(oD' 0x564d8%Z)) B b ltac:(zwok').
zstep (ltac:(oF' 0x564dc%Z)) (ltac:(oD' 0x564dc%Z)).
stepn (ltac:(oF' 0x564e0%Z)) (ltac:(oD' 0x564e0%Z)).
zsd (ltac:(oF' 0x56510%Z)) (ltac:(oD' 0x56510%Z)) c (L + 1) ltac:(zwok').
zsd (ltac:(oF' 0x56514%Z)) (ltac:(oD' 0x56514%Z)) (c + 16) b ltac:(zwok').
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell end.
zld (ltac:(oF' 0x56518%Z)) (ltac:(oD' 0x56518%Z)) (c + 24) Cby'.
zstep (ltac:(oF' 0x5651c%Z)) (ltac:(oD' 0x5651c%Z)).
zsd (ltac:(oF' 0x56520%Z)) (ltac:(oD' 0x56520%Z)) (c + 24) (bytes + (n + 8192)) ltac:(zwok').
match goal with |- msteps _ (mkst _ _ ?X _) _ =>
assert (F1' : cellA X (sp - 8) 8 (U raw)) by zcell; assert (F8' : cellA X (sp - 16) 8 x8) by zcell; assert (F9' : cellA X (sp - 24) 8 x9) by zcell;
assert (F18' : cellA X (sp - 32) 8 x18) by zcell; assert (F19' : cellA X (sp - 40) 8 x19) by zcell; assert (F20' : cellA X (sp - 48) 8 x20) by zcell;
assert (F21' : cellA X (sp - 56) 8 x21) by zcell end.
zld (ltac:(oF' 0x56524%Z)) (ltac:(oD' 0x56524%Z)) (sp - 8) F1'. rewrite Z_to_bv_bv_unsigned.
zld (ltac:(oF' 0x56528%Z)) (ltac:(oD' 0x56528%Z)) (sp - 16) F8'. zld (ltac:(oF' 0x5652c%Z)) (ltac:(oD' 0x5652c%Z)) (sp - 24) F9'. zld (ltac:(oF' 0x56530%Z)) (ltac:(oD' 0x56530%Z)) (sp - 32) F18'.
zld (ltac:(oF' 0x56534%Z)) (ltac:(oD' 0x56534%Z)) (sp - 40) F19'. zld (ltac:(oF' 0x56538%Z)) (ltac:(oD' 0x56538%Z)) (sp - 48) F20'. zld (ltac:(oF' 0x5653c%Z)) (ltac:(oD' 0x5653c%Z)) (sp - 56) F21'.
zstep (ltac:(oF' 0x56540%Z)) (ltac:(oD' 0x56540%Z)).
stepret (ltac:(oF' 0x56544%Z)) (ltac:(oD' 0x56544%Z)) raw ltac:(gres; reflexivity).
unfold art_enq_new_mem. rewrite (proj2 (Z.eqb_neq L 0) NL). zret.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_enq_new_head := (ltac2:(TCodec.tc2 tcn__JbtFxBatch1 "VB&<y5'QCyR0%211%5241'3y8%611%311p061':'6&Er8(QA+1(4%33A21%6251r5%93A21r9+2%93G17%<231&QB%12H7%@3H31r:+:%@3N1>%C231%E3M16&K+R0r7%3221&L&O%12A5%32K1z%921M&J+Q0%22H1%9217'5%?27K+QO%<2L1%>2N1%5241%:2I9%A21?&>&Q0r>%221Hr=%542J1@&8%QC3QD3E%211r@%921O%;41Q07Fp041&@&HrC%34216Q5&?rDu8r?%4573<21%R23R3=Q4%A11rFrB+@%Q7221%;5>419C%Q92D3+oM%>5A72<1%Q8241p0:1'7'A&FvQ6rH+ZiQ8%RA3RM1R?/01RMrG%756521Cr1+ZiS0%RG3S31RE/01S3&CrE%248Q01<%?5>741K%A3Q691%S029RE%QE2Q4R;%RE2S<1%S43S<31%S?1S@&I(1+3%S63SD1S4+4%S83SF1S6+8%S:3SH1S8+9%S<3SJ1S:+;%S>3SL1S<+<%S@3SN1S>+=%SB3T01S@+>%SD3T21SB+B%SF3T41SD+C%SH3T61SF+D%SJ3T81SH+E%SL3T:1SJ+F%SN3T<1SL+G%T03T>1SN+H%T23T@1T0+I%T43TB1T2+J%T63TD1T4+K%T83TF1T6(2%11Q8%Q73Q931%Q83Q:61%Q93Q;91%Q:3Q<<1%Q;3Q=?1%Q<3Q>B1%Q=3Q?E1%Q>3Q@H1%Q?3QAK1%Q@3QBN1%QA3QCQ11%QB3QDQ41%QC3QEQ71%QD3QFQ:1%QE3QGT91%QF3QHQ>1%QG3QIQA1%QH3QJQD1%QI3QKQG1%QJ3QLTK1%QL3QMR:1r3r2%U4221rJ%U6213%U83U@31p071pRDR51%T72R71%T82R<1qRJUD1%S02UE1p0S21p0S?1p0SE1p0SJ1p0T21p0T91p0T@1p0T=1p0TD1p0TI1p0TL1p0U11p0U61p0U<1p0UD1p2UO1pHV01pR8V11pRNV21pRFV:1pRLV51pLV61pRHV<1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_head) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_head) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_head) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_head) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_head) 4%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_head) 5%nat 0%nat).
Variable L : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_head) 6%nat 0%nat).
Variable B : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_head) 7%nat 0%nat).
Lemma art_enq_new_head : ltac:(sec_stmt2 constr:(SEC_T_art_enq_new_head) 8%nat 0%nat).
Proof using Type regs M rom raw sp c L B.
intros H1 H2 H10 Hsp Hsp' Hc Hc' HL HB HB' A1 A2 W CL CB.
assert (PRE : msteps ASEGS (mkst regs (0x56428 : word) M rom)
(mkst (regupd (regupd regs 2 (Z_to_bv 64 (sp - 64))) 15 (Z_to_bv 64 L)) (0x5644c : word) (art_enq_frame M sp raw regs) rom)).
{ zstep (ltac:(oF' 0x56428%Z)) (ltac:(oD' 0x56428%Z)).
zsd (ltac:(oF' 0x5642c%Z)) (ltac:(oD' 0x5642c%Z)) (sp - 8) (U raw) ltac:(rewok W). zsd (ltac:(oF' 0x56430%Z)) (ltac:(oD' 0x56430%Z)) (sp - 16) (U (getr regs 8)) ltac:(rewok W).
zsd (ltac:(oF' 0x56434%Z)) (ltac:(oD' 0x56434%Z)) (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd (ltac:(oF' 0x56438%Z)) (ltac:(oD' 0x56438%Z)) (sp - 32) (U (getr regs 18)) ltac:(rewok W).
zsd (ltac:(oF' 0x5643c%Z)) (ltac:(oD' 0x5643c%Z)) (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd (ltac:(oF' 0x56440%Z)) (ltac:(oD' 0x56440%Z)) (sp - 48) (U (getr regs 20)) ltac:(rewok W).
zsd (ltac:(oF' 0x56444%Z)) (ltac:(oD' 0x56444%Z)) (sp - 56) (U (getr regs 21)) ltac:(rewok W).
match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell end.
zld (ltac:(oF' 0x56448%Z)) (ltac:(oD' 0x56448%Z)) c CL'.
unfold art_enq_frame. zret. }
destruct (Z.eq_dec L 0) as [EL|NL].
- eexists. split.
{ eapply msteps_trans; [exact PRE|]. zbtk (ltac:(oF' 0x5644c%Z)) (ltac:(oD' 0x5644c%Z)). apply mst_refl. }
split; [gres; reflexivity|]. intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
- destruct (CB NL) as (CB1 & CB2). specialize (A2 NL).
eexists. split.
{ eapply msteps_trans; [exact PRE|]. zbft (ltac:(oF' 0x5644c%Z)) (ltac:(oD' 0x5644c%Z)).
assert (CB1' : cellA (art_enq_frame M sp raw regs) (c + 16) 8 B) by (unfold art_enq_frame; zcell).
assert (CB2' : cellA (art_enq_frame M sp raw regs) (B + 16) 8 1021) by (unfold art_enq_frame; zcell).
zld (ltac:(oF' 0x56450%Z)) (ltac:(oD' 0x56450%Z)) (c + 16) CB1'.
zld (ltac:(oF' 0x56454%Z)) (ltac:(oD' 0x56454%Z)) (B + 16) CB2'.
zstep (ltac:(oF' 0x56458%Z)) (ltac:(oD' 0x56458%Z)).
zbft (ltac:(oF' 0x5645c%Z)) (ltac:(oD' 0x5645c%Z)).
apply mst_refl. }
split; [gres; reflexivity|]. intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End SE.
#[using="Type"] Lemma art_enq_new_pop_fn : ltac2:(TCodec.tc2 tcn__JbtFxBatch1 "RA&<y5'QCyR0%211%5241'3y8%611%311p061':'6&Er5(QA+;(4%33A21%6251&QBr2%22C1%;3C41&Kzr3%3221&L&Jr4+Ra8%3221&O+2+R0%3221%9251'5+1%@21:+@%B2<1%5231&?&Hr8r6+Ql0%D221u4%756521Q5'A&FvQ6r:+ZiS0%Q:3QF1Q8/01QFr9%756521>&G+?%Q@3QN1Q>%Q<2QMA%43:21+ZiS8%QD3R01QB/01R0%@5?41:G%B3I:1p0D1p0M1p0Q41p0Q?1p0QD1pR<R11pR:R21pRLR41pLR51pRHR;1").
Proof.
intros regs M rom ca cnt H11 Hca Hca' Hcnt Ccnt.
zlw (ltac:(oF' 0x56460%Z)) (ltac:(oD' 0x56460%Z)) (ca + 1920) Ccnt.
zbft (ltac:(oF' 0x56464%Z)) (ltac:(oD' 0x56464%Z)).
zret.
Qed.
Section SE.
Local Abbreviation SEC_T_art_enq_new_ra_fn := (ltac2:(TCodec.tc2 tcn__JbtFxBatch1 "T8&<y5'QCyR0%211%5241'3y8%611%311p061':'6&Er8(QA+:(4%33A21%6251&QBr5%22C1%;3C41r9+;%;3I19%>231%@3H16r:+<%@3N1>%C231%E3M1;r;+=%E3Q31C%H231%J3Q21@r<+>%J3Q81H%M231%O3Q71E&Kz%221F&L&J+Ra8%22E1&O+2+R0%3221%8251&?&Hr>+Ql0%<2J1u4%655421A'A&FvQ6r@+ZiS0%QE3R11QC/01R1r?%756521=&G+1%QK3R91QI+Zi[L%QH2R91%53;31+8%R03R>1QN%Q02Q9E%QM2R>1%:3531+9%R53RC1R3%R12RBQ>%>3421%?31R52%@31QN7+QWTnH%R62RG1%C33QL1+H%R92RJ1%F33QJ1+?%RA3RO1R?%I3317+B%RD3S21RB%R@2S1R7%M3421+C%RH3S61RFr=%RE2S61%Q23531+D%RM3S;1RK%RI2S:R;%Q63421+E%S13S?1RO%RM2S>RI%Q:3421+ZkZL%S53SA1S3/01SA%QF5QE41Q@QL%QH3QNQ@1p0QJ1p0R21p0R<1p0R@1p0RF1p0RL1p0S21p0S81pRBSE1pR@SF1pS2SG1pR:SH1pR8SI1pRLSK1pLSL1pRHT21")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_ra_fn) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_ra_fn) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_ra_fn) 2%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_ra_fn) 3%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_ra_fn) 4%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_ra_fn) 5%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_ra_fn) 6%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_enq_new_ra_fn) 7%nat 0%nat).
Lemma art_enq_new_ra_fn : ltac:(sec_stmt2 constr:(SEC_T_art_enq_new_ra_fn) 8%nat 0%nat).
Proof using Type regs M rom c ca st m n.
intros H10 H11 H12 H13 H14 Hca Hca' Ccnt.
zlw (ltac:(oF' 0x56460%Z)) (ltac:(oD' 0x56460%Z)) (ca + 1920) Ccnt.
zbtk (ltac:(oF' 0x56464%Z)) (ltac:(oD' 0x56464%Z)).
zstep (ltac:(oF' 0x56548%Z)) (ltac:(oD' 0x56548%Z)). zstep (ltac:(oF' 0x5654c%Z)) (ltac:(oD' 0x5654c%Z)). zstep (ltac:(oF' 0x56550%Z)) (ltac:(oD' 0x56550%Z)). zstep (ltac:(oF' 0x56554%Z)) (ltac:(oD' 0x56554%Z)). zstep (ltac:(oF' 0x56558%Z)) (ltac:(oD' 0x56558%Z)). zstep (ltac:(oF' 0x5655c%Z)) (ltac:(oD' 0x5655c%Z)).
zstep (ltac:(oF' 0x56560%Z)) (ltac:(oD' 0x56560%Z)). zstep (ltac:(oF' 0x56564%Z)) (ltac:(oD' 0x56564%Z)). zstep (ltac:(oF' 0x56568%Z)) (ltac:(oD' 0x56568%Z)). zstep (ltac:(oF' 0x5656c%Z)) (ltac:(oD' 0x5656c%Z)). zstep (ltac:(oF' 0x56570%Z)) (ltac:(oD' 0x56570%Z)). zstep (ltac:(oF' 0x56574%Z)) (ltac:(oD' 0x56574%Z)).
stepn (ltac:(oF' 0x56578%Z)) (ltac:(oD' 0x56578%Z)).
zret.
Qed.
End SE.
#[using="Type"] Lemma art_enq_new_rb_fn : ltac2:(TCodec.tc2 tcn__JbtFxBatch1 "TC&<y5'QCyR0%211%5241'3y8%611%311p061':'6&Er9(QA+:(4%33A21%6251&QB+1%22C1%;3C41r:+8%;3I19%>231&Jr6+Ql0%3221%<2M1%E3M61r;+9%E3Q31C%H231r7%C2Q41%L3Q431r<+B%L3Q:1J%O231%I2Q:@%Q23Q:21r=+C%Q23Q@1Q0%Q5231%O2Q@K%Q83Q@21r>+D%Q83QF1Q6%Q;231%Q52QFQ;%Q>3QF21r?+E%Q>3QL1Q<%QA231r8%Q<2QM1%QE3QM31&Kz%221K&L+Ra8%Q;2H1&O+2+R0%3221%7251'5%<2QIQF+@%>2QH1%4231&?&HrB%QI2JQGu4%554321QE'A&FvQ6rD+Zi[L%R>3RJ1R</01RJrC%756521<&GrA%R?2S01%339RB1+;%RG3S51REr@%RD2S51%83531+<%RL3S:1RJ%RH2S9QA%<3421+=%S03S>1RN%RL2S=QK%@3421+>%S43SB1S2%S02SAR5%D3421+?%S83SF1S6%S42SER?%H3421+ZiS8%S<3SH1S:/01SH%Q45Q341NQ9%Q63Q;N1p0Q81p0Q?1p0QE1p0QN1p0R21p0R:1p0RA1p0RH1p0RO1p0S71p0SB1pR<SO1pRBT01pR@T11pS2T21pR:T31pR8T41pRLT61pLT71pRHT=1").
Proof.
intros regs M rom c ca st m n cnt H10 H8 H9 H18 H19 H20 H21 Hca Hca' Hcnt Ccnt.
zstep (ltac:(oF' 0x5657c%Z)) (ltac:(oD' 0x5657c%Z)).
zbft (ltac:(oF' 0x56580%Z)) (ltac:(oD' 0x56580%Z)).
zstep (ltac:(oF' 0x56584%Z)) (ltac:(oD' 0x56584%Z)). zstep (ltac:(oF' 0x56588%Z)) (ltac:(oD' 0x56588%Z)). zstep (ltac:(oF' 0x5658c%Z)) (ltac:(oD' 0x5658c%Z)).
zlw (ltac:(oF' 0x56590%Z)) (ltac:(oD' 0x56590%Z)) (ca + 1920) Ccnt.
zstep (ltac:(oF' 0x56594%Z)) (ltac:(oD' 0x56594%Z)).
stepn (ltac:(oF' 0x56598%Z)) (ltac:(oD' 0x56598%Z)).
zret.
Qed.
End FPX.
