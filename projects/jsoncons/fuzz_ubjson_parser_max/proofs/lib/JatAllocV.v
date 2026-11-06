(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JatLeaf JatPoison JatClassId JatClassId2 JatCombAllocHit JatAllocC JatAllocD JatAllocE.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatAllocV () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatAllocV."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatClassId2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1cons"; "1nat"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4bvmap"; "0M"; "5apart"; "5cell"; "5wr"]; ["6class_id"; "7msteps"; "8ret_ok"; "9art_d1_addr"; "9art_d1_kept"; "9art_d1_mem"; "9art_e_mem"; ":art_cid2_kept"; ";art_layout"; ";kHighMemBeg"; "<getr"; "<mkst"; "=mem_grows"; ">loaded_segments"; "?In"; "@add"]; ["@div"; "@land"; "@le"; "@lt"; "@modulo"; "@mul"; "@of_nat"; "@pow"; "@sub"; "0ab"; "0b"; "0b1"; "0fx"; "0loff"; "0m"; "0n"]; ["0r"; "0raw0"; "0regs"; "0regs'"; "0rom"; "0rs"; "0rz"; "0s0v"; "0s10v"; "0s11v"; "0s1v"; "0s2v"; "0s3v"; "0s4v"; "0s5v"; "0s6v"]; ["0s7v"; "0s8v"; "0s9v"; "0sp"; "ABV"; "AZ_to_bv"; "Abv"; "Abv_unsigned"; "0tp"; "0u"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_d1_addr (ab rz n : Z) : Z := 2147450880 + (ab + rz + n / 8 * 8) / 8.
Definition art_d1_mem (M : word -> option byte) (ab rz n : Z) : word -> option byte :=
if n mod 8 =? 0 then M else Wn 1 M (art_d1_addr ab rz n) (n mod 8).
Definition art_d1_kept (r : reg) : Prop :=
r <> 1%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv /\ r <> 22%bv.
Lemma art_d1_grows : ltac2:(TCodec.tc2 tcn__JatAllocV "E'R6yR0%211'3y8%511%311p051':&Lr4&Er3r2r1%445321%7261pS091pS>:1pRD;1pJ=1").
Proof. intros. unfold art_d1_mem. destruct (_ =? _); [apply mem_grows_refl | apply Wn_grows]. Qed.
Lemma cell_d1_other : ltac2:(TCodec.tc2 tcn__JatAllocV "R7'R6yR0%211'3y8%511%311p051':'1&Q2z&Cr6r5r4%43321%7261&Q3&Or7%93187+1%4221&Q7+2+R0%3221%:251%C2B?&Q6%11A%=2C1%?216&8'6&Q4r8+8%3221%53Q01M%711&=r;r:r9%Q23321%A1K%642J;1p081&>&Mr<%3521@Q1Q8&Er=%2414=<%7561<DQ5p051p0:1p0K1p0Q01p0Q21p0Q>1pTDQH1pRNQH1pRFQJ1pS0QK1pS>QL1pRDQM1pJQO1").
Proof. intros M ab rz n b m u H1 H2 H3 H4 A C. unfold art_d1_mem. destruct (Z.eqb_spec (n mod 8) 0) as [E|NE]; [exact C|]. apply cell_Wn_other; [lia|cbn; lia|lia|lia|exact (A NE)|exact C]. Qed.
Lemma art_d1_outside : ltac2:(TCodec.tc2 tcn__JatAllocV "QH'R6yR0%211'3y8%511%311p051':&Q2z&Cr4r3r2%43321%7261&Q3&Or5%93187+1%4221&Q7+2+R0%3221%:251&8'6&Q4+8%22D1%43I1G%611&R7%12Q3Hr7r6%L321D%;3Q041%=11p081&Er8%25187JQ1%21Q2%B3Q921p061p0F1p0Q21pTFQA1pS0Q<1pS>Q=1pRDQ>1pJQ@1").
Proof. intros M ab rz n x H1 H2 Hx. unfold art_d1_mem. destruct (Z.eqb_spec (n mod 8) 0) as [E|NE]; [reflexivity|]. specialize (Hx NE). rewrite Wn_outside; [reflexivity|lia|cbn; lia|cbn; lia]. Qed.
Lemma wr_d1 : ltac2:(TCodec.tc2 tcn__JatAllocV "M'R6yR0%211'3y8%511%311p051':&?&Mr6r2r1%544321&Er7r5r4%443821r3%<4;219p081pRN?1pRF@1pS0A1pS>B1pRDC1pJE1").
Proof. intros. eapply wr_grows; [apply art_d1_grows | assumption]. Qed.
Lemma art_layout_d1 : ltac2:(TCodec.tc2 tcn__JatAllocV "QH'R6yR0%211'3y8%511%311p051':&Q2z&Cr3r2r1%43321%7261&Q3&Or4%93187+1%4221&Q7+2+R0%3221%:251&=r5%C31;B+QVXR0+Q`P0%543<21r6%H316@+QibQ8+X0%:43A21&Hr8%211&Er9r7%34251;%711p061p0:1p0@1p0G1p0Q31pS0Q<1pS>Q=1pRDQ>1pJQ@1").
Proof. intros M ab rz n H1 H2 A1 A2 L. unfold art_d1_mem. destruct (_ =? _); [exact L|]. apply art_layout_Wn; [lia|cbn; lia|exact A1|exact A2|exact L]. Qed.
Definition art_e_mem (M : word -> option byte) (sp ab rz n b1 : Z) : word -> option byte :=
if rz =? 16 then Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 1 M (ab + rz - 15) (Z.land b1 243)) (ab + rz - 16) 2) (sp - 8) 0x52318) (sp - 16) 1) (sp - 24) n) (sp - 32) ab
else Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 1 M (ab + rz - 15) (Z.land b1 243)) (ab + rz - 16) 2) (ab + 8) (ab + rz - 16)) ab 0xcc6e96b9cc6e96b9) (sp - 8) 0x52318) (sp - 16) 1) (sp - 24) n) (sp - 32) ab.
Lemma art_e_grows : ltac2:(TCodec.tc2 tcn__JatAllocV "I'R6yR0%211'3y8%511%311p051':&Lr6&Fr5r4r3r2r1%66754321%9281pRH;1pS0<1pS>=1pRD>1pT8?1pJA1").
Proof. intros. unfold art_e_mem. destruct (_ =? _); repeat (eapply mem_grows_trans; [|apply Wn_grows]); apply mem_grows_refl. Qed.
Lemma cell_e_other : ltac2:(TCodec.tc2 tcn__JatAllocV "RA'R6yR0%211'3y8%511%311p051':'1&Q2+Q0r8%3221&Q3r9&Q7+2+R0%3221%6251z%<217&Or:%221:%<217+@%B214%C28A&Q6%11C%92A1%C21>&=&Q8r?%221J%81G%542L?1r;%;1A%846?21r@%E218%:21Br<%A17%>43E21&>&MrCr=%453217=&FrDrBrA%463721?Fr>%;5:218>p081p0>1p0E1p0I1p0Q01p0Q51p0Q71p0Q:1p0Q?1p0QB1p0QJ1pTDR01pRNR01pRFR21pRHR31pS0R41pS>R51pRDR61pT8R71pJR91").
Proof.
intros M sp ab rz n b1 b m u Hsp Hsp' Hab Hab' Hrz Hb Hm A1 A2 A3 C. unfold art_e_mem. unfold apart in A1, A2, A3.
destruct (_ =? _); repeat (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]); exact C.
Qed.
Lemma art_e_outside : ltac2:(TCodec.tc2 tcn__JatAllocV "R>'R6yR0%211'3y8%511%311p051':&Q2+Q0r6%3221&Q3r7&Q7+2+R0%3221%6251z%<217&Or8%221:%<217+@%B214&8'5&Q8r;%221F&R7%12Q1G%J231%G225%8221%:11%62Q6I%O291%C2:?%M231%>231%@11r<%H21?%A21E%?2Q?I%Q8221%Q5224%F221%H11'6&Fr?r>r=r:r9%67543?M21%612%93QH21p0;1p0D1p0K1p0Q71p0Q:1p0Q?1p0QB1p0QJ1pTFR51pRHR01pS0R11pS>R21pRDR31pT8R41pJR61").
Proof.
intros M sp ab rz n b1 x Hsp Hsp' Hab Hab' Hrz N1 N2 N3. unfold art_e_mem.
destruct (_ =? _); repeat (rewrite Wn_outside; [|lia|cbn; lia|cbn; lia]); reflexivity.
Qed.
Lemma art_e_state : ltac2:(TCodec.tc2 tcn__JatAllocV "QO'R6yR0%211'3y8%511%311p051':&Q2+Q0r5%3221&Q3r6&Q7+2+R0%3221%6251z%<217&Or7%221:%<217'9%B2A4'6+@%23F71%5241&=&Q8r:%221Ir9r8%@221%621:%845N1;&>&M&Fr<r;%3621<:9G%I2=;%?21Cu1%958421Q2p0;1p0E1p0L1p0Q11p0Q41p0Q<1pRHQA1pS0QB1pS>QC1pRDQD1pT8QE1pJQG1").
Proof.
intros M sp ab rz n b1 Hsp Hsp' Hab Hab' Hrz A. unfold art_e_mem. unfold apart in A.
destruct (Z.eqb_spec rz 16); repeat (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]); apply cell_Wn_hit; cbn; lia.
Qed.
Lemma art_e_type : ltac2:(TCodec.tc2 tcn__JatAllocV "R6'R6yR0%211'3y8%511%311p051':&Q2+Q0r5%3221&Q3r6&Q7+2+R0%3221%6251z%<217&Or7%221:%<217'9%B2A4'6+@%23F71%5241&=&Q8r:%221Ir9r8%@221%621:%845N1;%Q02EB&>&M&Fr=r<r;%46321><;%K22?+?%B221u1&Q1+WC%22B1%>5=8541p0@1p0B1p0L1p0Q31p0Q81p0Q;1p0QC1pRHQH1pS0QI1pS>QJ1pRDQK1pT8QL1pJQN1").
Proof.
intros M sp ab rz n b1 Hsp Hsp' Hab Hab' Hrz A Hb1. unfold art_e_mem. unfold apart in A.
destruct (Z.eqb_spec rz 16); repeat (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]); apply cell_Wn_hit; cbn; lia.
Qed.
Lemma cell_e_hi16 : ltac2:(TCodec.tc2 tcn__JatAllocV "R6'R6yR0%211'3y8%511%311p051':&Q2+Q0r6%3221&Q3r7&Q7+2+R0%3221%6251z%<217&Or8%221:%<217'9'6+@%23E61%E2D7%5221&=&Q8r;%221Ir:r9%@221+>%7221%946O1I&>&Mr=%G2;9%=217u2%655421Q2&Fr>r<%36281B@?%O22C%E21?%=5<318Q0p081p0@1p0K1p0Q21p0Q71p0Q:1p0QB1pTDQG1pRHQH1pS0QI1pS>QJ1pRDQK1pT8QL1pJQN1").
Proof.
intros M sp ab rz n b1 u Hsp Hsp' Hab Hab' Hrz A C. unfold art_e_mem. unfold apart in A.
destruct (Z.eqb_spec rz 16); repeat (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]); exact C.
Qed.
Lemma wr_e : ltac2:(TCodec.tc2 tcn__JatAllocV "Q1'R6yR0%211'3y8%511%311p051':&?&Mr8r2r1%544321&Fr9r7r6r5r4%665:4321r3%>4=21;p0:1pRNA1pRFB1pRHC1pS0D1pS>E1pRDF1pT8G1pJI1").
Proof. intros. eapply wr_grows; [apply art_e_grows | assumption]. Qed.
Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_alloc_d1_run : ltac2:(TCodec.tc2 tcn__JatAllocV "TD&;y5'R6yR0%211%5241'3y8%611%311p061':'6&Jr6(R4+9(4%33A21%6251&R5r2%22C1%;3C41r7+D%;3I19%>231&Or4%2219%;2L1%D3L51r8+F%D3Q21B%G231&Q5&Q0+8%22;1%4212%F2Q71%O3Q771&Q2&I%221Q0&Q3+RPP0%E2I1&Q7+2+Q?%3221%7251&Q4+@%22H1z%Q?3Q@21'5%A25Q5+RP0%C2Q71%4231r:%F2K1+Q8%B2A1%F241%:241r;%Q<217%M21I&Hr?%211&>&Mr@+QWQWH+RE%QF221u1+1%8576321&8r>%Q121QA%R=3R>1O%411&?rB&C%13?7C%44A31;p061'7'A&KvQ<rD+ZXTL%RH3S41RF/01S4rC%756521>r1+ZXY@%RN3S:1RL/01S:&ErA%2481Q6Q2%?5>741F%A3Q591%SB1SC&D%11;r3%S;21S3rF%S=21S5%S?3SG31p061pS291%R22;1qS8SJ1%O2SK1p0Q11p0Q=1p0QG1p0QK1p0QO1p0R;1p0R71p0R=1p0RC1p0RL1p0S01p0S<1p0SF1pS>T31pS0T41pRDT51pS:T71pJT81pS6T>1").
Proof.
intros regs M rom ab n rz H9 H20 H22 Hab Hab' Hab16 Hrz Hrz16 Hn Hprim L Cpp Wsh.
unfold art_d1_mem, art_d1_addr in *.
destruct (Z.eqb_spec (n mod 8) 0) as [E|NE].
- exists regs. split; [|intros r _; reflexivity].
apply (art_alloc_d1_none regs M rom n H9 H22 ltac:(lia) E).
- eexists. split.
+ apply (art_alloc_d1_part_fn regs M rom ab n rz H9 H20 H22 Hab Hab' Hab16 Hrz Hrz16 ltac:(lia) NE Hprim L Cpp (Wsh NE)).
+ intros r Hr. unfold art_d1_kept in Hr. decompose [and] Hr. kept_solve.
Qed.
#[using="Type"] Lemma art_alloc_d2b_run : ltac2:(TCodec.tc2 tcn__JatAllocV "S0&;y5'R6yR0%211%5241'3y8%611%311p061':'6&Jr5(R4+;(4%33A21%6251&R5+`0%22C1%;3C41r6+C%;3I19%>231&Or3r2%3221%<2M1%E3M61'5&Q2+1r4%:219%4231+RPP0%6231%8231&Q4%@2N7+8%3221z%Q43Q521'7'A&M&KvQ<r:+ZX\8%Q93QE1Q7/01QEr9r8%8576321r1+ZXcD%Q@3QL1Q>/01QL%=5<4176%@3?61%QF26QA&@r7%Q:21Q>%311%QD2R51%QM3R561%R81R9&G%11?%R02Q@Q?r<%R221QA%R43R<31p051pS281%QA2:1%QB2B1qS8R@1%Q52RA1p0Q71p0Q>1p0QH1p0R31pS>R@1pS<RA1pS:RC1pJRD1pS6RJ1").
Proof.
intros regs M rom rs rz H11 H19 Hs Hs8.
destruct (Z.leb_spec (rs + rz) 512) as [LE|GT].
- eexists. split; [|split].
+ apply (art_alloc_d2b_small_fn regs M rom rs rz H11 H19 ltac:(lia)).
+ gres. f_equal. symmetry. apply class_id_small. lia.
+ intros r Hr. unfold art_cid2_kept in Hr. decompose [and] Hr. kept_solve.
- destruct (art_classid2_hi_run regs M rom (Z_to_bv 64 (rs + rz)) H19) as (r' & RUN & P11 & K).
exists r'. split; [|split].
+ eapply msteps_trans; [apply (art_alloc_d2b_big regs M rom rs rz H11 H19 ltac:(lia)) | exact RUN].
+ rewrite P11. apply art_cid_w_ok; lia.
+ exact K.
Qed.
#[using="Type"] Lemma art_alloc_e_run : ltac2:(TCodec.tc2 tcn__JatAllocV "]3&;y5'R6yR0%211%5241'3y8%611%311p061':'6&JrG(R4+2(4%33A21%6251&R5rC%22C1%;3C41rH+4%;3I19%>231r?%92J1%B3J31rI+8%B3Q01@%E231+1%@2Q11%I3Q131rJ+9%I3Q71G%L231rD%G2Q81%Q03Q831rK+B%Q03Q>1N%Q3231rF%N2Q?1%Q73Q?31rL+D%Q73QE1Q5%Q:231&OrE%22Q<1%Q72QH1%Q@3QH51rM+E%Q@3QN1Q>%QC231&Q8%:2Q:A+@%3221%QA2R21%QJ3R261&Q2+Q0%221Q3&Q3+T0%D2O1&Q7+R0%22QO1%6241+VbTP0%J21:%<21O&I%>21Q1+RPP0%O2J1+Q?%<2R91%@231&Q4rN%221Jz%RC3RD21'5%J2QN5+Q8%F2RC1%J281%5241%O28Q9+X0%N2Q;1%9231+TP0%QC2?1%Q221M%Q62?ArQ0rO%QH221%QI21RH%Q821Q3&BrQ7%211&>&MrQ:+QV\dHu8rQ1%6554321rQ;rQ3rQ2%R8221u4%<5;521Q4&=rQ4%R=217rQ8rQ6%R@221%R821R6%745SA1R7rQ=rQ9%RE21I%R=21R;%RG21S<u1%K5J621:&?rQ>%RL2L>%RD21RB%44O31RCrQ?rQ<%RH21RA%84Q331RB&HrQ@%211rQA+Qian0%Q:5Q921Q6R2%S92>9%S121RO%S22<RK+U0%Q243S221%S52:RN%Q44@S413rQD+SH%SB2<1&R7rQB%22U:1%QH5QG64QD1rQE+S@%SI251%QL5QK31QHQErQFrQC+S8%SN221%R15R041QMQJrQG+S0%T22B1%R55R431R1QNrQH+RH%T62?1%R95R831R5R2rQI+R@%T:2?1%R=5R<31R9R6rQJ+R8%T>2>1%RA5R@31R=R:rQK%TA2=SK%RD5RC21R@R=rQL+QH%TE2=1%RH5RG31RDRArQM+Q@%TI2=1%RL5RK31RHRErQN%TL2<SB%RO5RN21RKRHrQO%TO2<T?%S25S121RNRKrR0+H%U32<1%S65S531S2RO%TF2TJE+RP0%TH2G1%T0231%T62FTN%VF3VG1T4rR3%RB4S=1>U1rR4+RPjH+\hkdfgWVVmUeI%SB5SA32S>1'7'A&KvQ<rR7+ZXf4%W03W<1VN/01W<rR6rR5%8576321r1&FrR2rR1%367E2O1Q2%>5=5D17%@3T371+:%W=3WK1W;%W@291%V628Q5%W;2WL1%WD3WL31%WD2=W?%V:2OUG%W?2X01%WH3X031%WF3X4W2WD%WI2B1%WK3X31Q2%WK2DW7%WE2X6QN%WN3X621%WN2GW3%WH2X9R4%X13X921%X12JVO%WK2X<R;%X43X<21+C%X33XA1X1%X62O1%X02XARD%X93XA21%X92Q2W0%X32XDRK%X<3XD21%X<2Q5VJ%X62XGS2%X?3XG21+F%X>3XL1X<%XA2Q:1%X;2XLS<%XD3XL21+G%XC3Y11XA%XF2Q?1%X@2Y1SE%XI3Y121%XG3Y5R<XE%XJ2QC1%XD2Y5T0%XM3Y521+I%XL3Y:1XJ%XO2QH1%XI2Y:SI%Y23Y:21+J%Y13Y?1XO%Y42QM1%XN2Y?T6%Y73Y?21+K%Y63YD1Y4%Y92R21%Y32YDTI%Y<3YD21%YG1YH&N(0+3%Y>3YL1Y<(2%116%537Y61%63841%839R>1r3r2%YH221rR9%YJ213%YL3Z431p071pS2A1%W;2C1%W<2I1%W=2O1%W>2Q51%W?2Q:1%W@2Q@1%WA2QF1%WB2QJ1%WC2QN1%WD2R41%WE2R81%WF2R<1%WG2R@1%WH2RD1%WI2RI1%WJ2S01qS8ZF1%SC2ZG1p0SE1p0SJ1p0SM1p0T01p0T51p0T:1p0T>1p0TB1p0TG1p0TL1p0U01p0U51p0U:1p0U?1p0UD1p0UJ1p0UO1p0V71p0V:1p0V@1p0VD1p0VH1p0VM1p0W31p0W;1p0WD1p0WK1p0X31p0X71p0X=1p0X?1p0XF1p0XD1p0XI1p0Y01p0Y61p0Y<1p0Y?1p0YC1p0YK1p0YO1p0Z:1p0ZD1p0ZL1p0[41p0[<1p0[D1pSD\11pSB\21pT6\31pT4\41pT2\51pT0\61pSN\71pSL\81pSJ\91pSH\:1pSF\;1pS@\<1pRL\=1pTB\>1pRH\?1pS>\@1pS0\A1pRD\B1pT8\C1pS4\K1pS:\F1pJ\G1pS6\M1").
Proof.
intros regs M rom raw0 sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v H2 H4 H8 H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24.
intros Hrz Hrz16 Wab Cmag. unfold art_e_mem.
destruct (Z.eqb_spec rz 16) as [E|NE].
- eexists. split. apply (art_alloc_e16_fn regs M rom raw0 sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v H2 H4 H8 H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24 E).
zsplit; try (gres; reflexivity).
intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; gres; reflexivity.
- assert (Hrz32 : 32 <= rz <= 2048). { pose proof (Z.div_mod rz 16 ltac:(lia)). lia. }
eexists. split. apply (art_alloc_e32_fn regs M rom raw0 sp ab n rz b1 tp loff s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v H2 H4 H8 H9 H18 H20 H21 Hsp Hsp' IMG Hab Hab' Hab16 Hn Hb1 Htp Htp' Hloff Hloff' Hret Cg Ct Atl Cb1 Wh Wf32 L Chook Afr Afr2 F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24 Hrz32 Hrz16 Wab Cmag).
zsplit; try (gres; reflexivity).
intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; gres; reflexivity.
Qed.
End FPX.
