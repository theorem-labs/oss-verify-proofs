(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim MemsetLib As0StepLib As0Tables
ArtMem ArtRegs ArtAtomics ArtTac JbtLeaf JbtAllocG JbtPoison JbtPoisonRun JbtPoison3 JbtAllocC JbtAllocD JbtAllocE JbtAllocV ArtRuns ArtRunsMem JbtFp JbtCellEx
JbtAllocSecC JbtAllocSecD JbtAllocSecE.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import muslA.Jb0SumsMemset_code muslA.Jb0SumsMemset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtAllocPostL () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtAllocPostL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtLeaf."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "4bvmap"; "0M'"; "0M8"; "5apart"; "5cell"; "5wr"; "6msteps"; "7ret_ok"]; ["8art_postL_fp"; "9art_agree"; ":art_tsd"; ";art_layout"; "<getr"; "<mkst"; "=mem_grows"; ">loaded_segments"; "?add"; "?div"; "?land"; "?le"; "?lt"; "?modulo"; "?mul"; "?pow"]; ["?sub"; "0a"; "0ab"; "0b"; "0b1"; "0ctx"; "0f104"; "0f112"; "0f120"; "0f24"; "0f32"; "0f40"; "0f48"; "0f56"; "0f64"; "0f72"]; ["0f80"; "0f88"; "0f96"; "0fx"; "0id"; "0j"; "0key"; "0loff"; "0m8"; "0n"; "0nd"; "0q"; "0qn"; "0qr"; "0qz"; "0r8"]; ["0raw"; "0regs'"; "0rom"; "0rs"; "0rz"; "0sp"; "0spb"; "@BV"; "@Z_to_bv"; "@bv"; "@bv_unsigned"; "0t"; "0tp"; "0tsd"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Definition art_postL_fp (sp t ab rz q : Z) : list (Z * Z) :=
[ (sp - 128 - 64, 64); (ab, 16); (ab + rz - 16, 16 + 4096); (2147450880 + ab / 8, 512 * q); (t + 2800, 112) ].
Section FPX. Context {fx : PropExec.FPState}.
#[using="Type"] Lemma art_div8_add : ltac2:(TCodec.tc2 tcn__JbtAllocPostL "J'7'3&Mr2+8%3221z%63721&Kr3%2241&I&Hr5r4%3221%521<%624=%724>%7221%C3D41p0;1p0<1p0@1pR8H1pR4I1").
Proof.
intros a b Ha H0 Hb. pose proof (Z.div_mod a 8 ltac:(lia)) as E. rewrite Ha in E.
replace (a + b) with (b + (a / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_allocate_post_sec := (ltac2:(TCodec.tc2 tcn__JbtAllocPostL "f<&8y5'R9yR0%211%5241'0y8%611%311p061'7'3r=&R:rQ2%22=1%53641&?rQ3%211&DrQ7(R7+2(1%33I21%6251&R8&Q0+T0%22<1%42M1%E3M61rQ8+4%=3Q31;%@231rG%;2Q41%L3Q431rQ9+8%D3Q:1B%G231z%B2Q;1%Q33Q;31rQ:+9%K3QA1I%N231rQ5%I2QB1%Q:3QB31rQ;+:%Q23QH1Q0%Q5231rE%Q02QI1%QA3QI31rQ<+B%Q93QO1Q7%Q<231rN%Q72R01%QH3R031rQ=+C%Q@3R61Q>%QC231rQ1%Q>2R71%QO3R731rQ>+D%QG3R=1QE%QJ231&HrQ0rQ4%3221%QH2RA1%R93RA61rQ?+E%R13RG1QO%R4231%:2AQ6+@%QO221%R12RJ1%RB3RJ51rQ@+F%R:3S01R8%R=231+QWTnH%R82S11%RI3S131rQA+H%RA3S71R?%RD231%RN3S61QLrQB+I%RF3S<1RD%RI231%O2MR=%Q021Q;%RE2S>1%S63S>41'2&K+TP0%221Q:&L&O+Q7%22S21%42Q?1%9261&N%12RDQB%Q?21QJ%SD3SEQ:1%=2RDQE+7%?2QG1%A231%82RKR0%SJ3SKQJ1%C2LQA%QH2M6%E2QC1%G231%>2Q@R6%T03T1R01+Q0%J21QH+RP0%L2QJ1%N231%R22Q7QC%R321QD%T83T9R81+RPP0%O21R0+1%SK2R21%L2Q41%Q321QK%N2Q6R5%Q82QM1%Q:231+`PQoooPP0%R?21Q:rQI%Q=221rQJ+RS0%RD221+Q?%Q>2T>1%QC231%QD2QCRB%RI2R:QD%QC214'6%RL2R6QG%QI21H+Vb\P0%QK21R9%5231&;rQN+Qm0%TG221+Um0%54R;R121rQC+QoooPP0+`PPPPPPP0%943R521rR0%TO219%<4S7R818%R:2EQ9%R;2AS0%E221rQF%A41R=RLR=%B4RHR>;:%R@2TG3+RPX0rQH%RC221%SH2Q8TN%RE21K%SJ2Q8Q:%RG2QF1rQK%SM21Q;%SN21U;%RK21Q1%RL2QKQ@+QP0%T22Q@1%RO21Q5&MrR1%221S1%V;3V<1U:%T82Q:S3rR2%S6221rR3rR4%S02S81%T>231%S821Q7%S<2R15%QF221rR5%S62S>1%TD281%S>21QO%V924SArR6%S;2SC1%TI21SDrR?%V>21QH%QK4631QG%V@26SHrR7%SB2SJ1%U021SK%R0441ESL%VE24SMrR8%SG2SO1%U521T0%R5441QKT1%T32V:9+Q5%T12W11%U:271+Q@%T42W41%T6231rR:rR9%T9221%UA228%T>214%RH231%T@2VGQ9%T=2W=SH%T?2Q;1%TD231+X0%TB2Q>1%TG261+R0%TD2WD1%TF2QB1%TK2:1&=&GrS7rS4%WF21S0%54431S1rS8rRKrRL%TK2U31%:49431rS9&I%125WB%V=2S51+`0rRM%U3221%B4A741rS:%D4C1=U>&CrS;%211&BrS<rRJrRIrRH%564E321=&<rS=%VO2V<U2u8rRO%55Q24321rS>%W42VAQ9%85Q5215V0rS?rS2%XK21V3%W921VN%=5Q:41:Q8rS@+QWXaH+RE%W>221u1%C5Q@521U9rSA+Q<%WC271u4%H5QE421V@rSB+QD%WH2<1+UN%M5QJ4261rSC+QVdP0%Q05QM21MFrSDrS3%X02QN1%Q45R131=Y4rSE+QiiX0%Q75R421Q4Y7rSF+RPjH+\hkdfgWVVmUeI%Q;5R832Q81rSG%X:2QHQ7+?%YO221rS1%QA5R>52O1rSH%X@2QKQ:+<%Z5221%QF5RC41OErSI%XE2QMQ:+>%Z:221u2%QL5RI521YLrSJ%Z>2BZ=%XL21Z2%R05RM31QMVFrSK%ZB2@ZA+SH%Y1221%R55S241R2S0rSL%ZG2@ZF+S@%Y6221%R:5S741R7S5rSM%ZL2?ZK+S8%Y;221%R?5S<41R<S:rSN%[12@[0+S0%Y@221%RD5SA41RAS?rSO%[62@[5+RH%YE221%RI5SF41RFSDrT0%[;2@[:+R@%YJ221%RN5SK41RKSIrT1%[@2@[?+R8%YO221%S35T041S0SNrT2%[E2@[D%Z321T8%S75T431S4T2rT3%[I2?[H+QH%Z8221%S<5T941S9T7rT4%[N2?[M%Z<21U1%S@5T=31S=T;rT5%\22>\1+Q8%ZA221%SE5TB41SBT@rT6%\72?\6%ZE21XH%SI5TF31SFTDrT7%\;2>\:%ZI21Z2%SM5TJ31SJTH'4'>&EvQCrT;+ZXc0%\J3]>1\H/01]>rT:rT9%8576321r2rT8r1%<5;3215%>3U:51%]625\2%[<2R4Q@%]12]J1%]B3]J31%]:29]5%]42]MI%]E3]M21%];3^1Y;]9%]>2=1%]H3^01=%]@2?\J%]:2^3T0%]K3^321%]C2B\F%]=2^6T8%]N3^621%]F2E\;%]@2^9TA%^13^921%]I2H\7%]C2^<TI%^43^<21%]L2K\3%]F2^?TO%^73^?21%]O2N[L%]I2^BU7%^:3^B21%^22Q1[F%]L2^EU@%^=3^E21+G%^43^J1^2%^72Q61%^12^JUH%^B3^J21%^:2Q9[G%^42^MUN%^E3^M21%^=2Q<[E%^72_0V9%^H3_021+J%^?3_51^=%^B2QA1%^<2_5VC%^M3_521+K%^D3_:1^B%^G2QF1%^A2_:VL%_23_:21&F%12QMQH&A&@%15R<T5SKS7SF%331R1QL%^H2QI\J%V95W6QN1UG^N%^J2QKTF%V;5W8R01UDRE%^L2QMTN&J+WC%22U>1%V@5W=R54UN1%_12R2TH%VB5W?R71TG^B%_32R4^F%VD5WAR91VAU?%VE5WBR:T:VBU;%]C2T;^I%VG5WDR<1VD?%\A2^HR=%\?2R>S3%\D221r3%W>2T7^O%]J2ZB1%\>2_CSJ%]L221%]M21RG%W15WN61V?_1p081pS<`51&5%`63`7SH_5%211%WI2TG_:%^52ZM1%\I2_NT:%^7221%^821SE%W<5X9S31VJSKp071+3%`53`K1`3%`82S71%`92S?2%`C3`K21%`;2S:_L%`<2SB_M%`F3`N21%]@241%]A2:1%]B2E1%]C2Q21%]D2Q51%]E2Q71%]F2Q:1%]G2Q=1%]H2QC1%]I2QF1%]J2QI1%]K2QN1%]L2R11%]M2R71%]N2R=1%]O2RA1%^02RE1%^12RK1%^22RO1%^32S31%^42S71%^52S;1%^62S?1%^72SC1%^82SG1%^92SK1%^:2SO1%^;2T41qDaE1%TE2aF1qT4aL1%TG2aM1p0TI1p0TN1p0U31p0U91p0U>1p0UD1p0UI1p0UO1p0V51p0V;1p0VA1p0VG1p0VM1p0W31p0W81p0W?1p0WE1p0WL1p0X11p0X51p0X:1p0X>1p0XD1p0XJ1p0Y11p0Y71p0Y;1p0YB1p0YI1p0YM1p0Z01p0Z91p0Z?1p0ZF1p0ZG1p0ZH1p0ZI1p0ZJ1p0ZK1p0ZL1p0ZM1p0ZN1p0ZO1p0[01p0[11p0[21p0[71p0[;1p0[@1p0[G1p0[N1p0\01p0\61p0\<1p0\D1p0\I1p0]11p0]51p0]:1p0]>1p0]@1p0]E1p0]H1p0]K1p0]O1p0^11p0^31p0^61p0^:1p0^>1p0^C1p0^J1p0_11p0_41p0_61p0_=1p0_B1p0_J1p0_M1p0`11p0`71p0`:1p0`?1p0`B1p0`G1p0`L1p0a71p0a@1p0aF1p0aN1p0b81p0bC1p0bK1p0c31p0c;1p0cC1p0cK1p0d31p0dA1p0dE1pRDdL1pRFdM1pRHdN1pRJdO1pRLe01pRNe11pS0e21pS2e31pS4e41pS6e51pR>e61pR@e71pRBe81pR:e91pS:e:1pR<e;1pTLe<1pS>e=1pS@e>1pTJe?1pTHe@1pT>eA1pR6eB1pSHeC1pSFeD1pSNeE1pT:eF1pSLeG1pT8eH1pSBeI1pSJeJ1pSDeK1pT<eL1pT2f41pT6eO1pFf01pT0f61")) (only parsing).
Variable r8 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 0%nat 0%nat).
Variable M8 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 2%nat 0%nat).
Variable raw : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 3%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 5%nat 0%nat).
Variable qn : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 6%nat 0%nat).
Variable m8 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 7%nat 0%nat).
Variable rs : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 8%nat 0%nat).
Variable qr : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 9%nat 0%nat).
Variable rz : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 10%nat 0%nat).
Variable qz : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 11%nat 0%nat).
Variable nd : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 12%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 13%nat 0%nat).
Variable ab : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 14%nat 0%nat).
Variable spb : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 15%nat 0%nat).
Variable t : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 16%nat 0%nat).
Variable tp : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 17%nat 0%nat).
Variable loff : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 18%nat 0%nat).
Variable key : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 19%nat 0%nat).
Variable tsd : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 20%nat 0%nat).
Variable ctx : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 21%nat 0%nat).
Variable id : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 22%nat 0%nat).
Variable b1 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 23%nat 0%nat).
Variable f120 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 24%nat 0%nat).
Variable f112 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 25%nat 0%nat).
Variable f104 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 26%nat 0%nat).
Variable f96 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 27%nat 0%nat).
Variable f88 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 28%nat 0%nat).
Variable f80 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 29%nat 0%nat).
Variable f72 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 30%nat 0%nat).
Variable f64 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 31%nat 0%nat).
Variable f56 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 32%nat 0%nat).
Variable f48 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 33%nat 0%nat).
Variable f40 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 34%nat 0%nat).
Variable f32 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 35%nat 0%nat).
Variable f24 : ltac:(sec_ty2 constr:(SEC_T_art_allocate_post_sec) 36%nat 0%nat).
Theorem art_allocate_post_sec : ltac:(sec_stmt2 constr:(SEC_T_art_allocate_post_sec) 37%nat 0%nat).
Proof using Type r8 M8 rom raw sp n qn m8 rs qr rz qz nd q ab spb t tp loff key tsd ctx id b1 f120 f112 f104 f96 f88 f80 f72 f64 f56 f48 f40 f32 f24.
intros Ef120 Hret Q2 Q4 Q8 Q9 Q10 Q18 Q19 Q20 Q21 Q22 Q24 Q25.
intros Hn En Hm8 Ers Hrs Erz Hrz End Hnd Hq.
intros Hsp Hsp' Ht Ht' Timg Atsp Atsh Acsp Cimg Atc Acsh Hloff Htp Htp8 Htpl Htpl' Htsd Htsd'.
intros Hab4 Hab Hmem Hab' Absp Abt Abc Hspb Hspb' OUT Hid Hb1.
intros B120 B112 B104 B96 B88 B80 B72 B64 B56 B48 B40 B32 B24.
intros W Wab Wsh Wt L TSD Cspb Cpg Cnd Cpp Cmax Cfb Cg Clsan Chook Cmag Bh1 Bh12 Bh14 Ccf F120 F112 F104 F96 F88 F80 F72 F64 F56 F48 F40 F32 F24.
change (hid (t + 4096 <= 0x10000 \/ 0x693000 <= t)) in Timg. change (hid (ctx + 4096 <= 0x10000 \/ 0x693000 <= ctx)) in Cimg.
change (hid (ab + 4096 * q < 0x7fff8000 \/ 0x10007fff8000 + 4096 <= ab)) in Hmem. change (hid (ab < spb \/ spb + 2 ^ 37 <= ab)) in OUT.
assert (Eka : ab = 4096 * (ab / 4096)) by (pose proof (Z.div_mod ab 4096 ltac:(lia)); lia).
set (ka := ab / 4096) in *.
assert (Hab8 : ab / 8 = 512 * ka). { rewrite Eka. replace (4096 * ka) with (512 * ka * 8) by lia. apply Z.div_mul. lia. }
assert (Mab8 : ab mod 8 = 0). { rewrite Eka. replace (4096 * ka) with (512 * ka * 8) by lia. apply Z_mod_mult. }
assert (Mab16 : ab mod 16 = 0). { rewrite Eka. replace (4096 * ka) with (256 * ka * 16) by lia. apply Z_mod_mult. }
assert (Mrz16 : rz mod 16 = 0). { rewrite Erz, Z.mul_comm. apply Z_mod_mult. }
assert (Hub8 : (ab + rz) / 8 = 512 * ka + 2 * qz). { rewrite Eka, Erz. replace (4096 * ka + 16 * qz) with ((512 * ka + 2 * qz) * 8) by lia. apply Z.div_mul. lia. }
assert (Mub8 : (ab + rz) mod 8 = 0). { rewrite Eka, Erz. replace (4096 * ka + 16 * qz) with ((512 * ka + 2 * qz) * 8) by lia. apply Z_mod_mult. }
assert (Hn8 : n / 8 = qn). { symmetry. apply (Z.div_unique n 8 qn m8); lia. }
assert (Hnm : n mod 8 = m8). { symmetry. apply (Z.mod_unique n 8 qn m8); lia. }
assert (Hn88 : n / 8 * 8 = 8 * qn) by lia.
assert (Hn888 : n / 8 * 8 / 8 = qn). { rewrite Hn88. rewrite Z.mul_comm, Z.div_mul; lia. }
assert (Etb : (ab + rz + n + 7) / 8 * 8 = ab + rz + rs).
{ assert (E : (ab + rz + n + 7) / 8 = 512 * ka + 2 * qz + qr).
{ symmetry. apply (Z.div_unique _ 8 _ (n + 7 - rs)); lia. }
rewrite E. lia. }
set (tb := ab + rz + rs) in *.
assert (Htl : 4096 * q - rz - rs = 8 * (512 * q - 2 * qz - qr)) by lia.
assert (Htl8 : (ab + 4096 * q - tb) / 8 = 512 * q - 2 * qz - qr). { unfold tb. replace (ab + 4096 * q - (ab + rz + rs)) with ((512 * q - 2 * qz - qr) * 8) by lia. apply Z.div_mul. lia. }
assert (Htb8 : tb / 8 = 512 * ka + 2 * qz + qr). { unfold tb. rewrite Eka, Erz, Ers. replace (4096 * ka + 16 * qz + 8 * qr) with ((512 * ka + 2 * qz + qr) * 8) by lia. apply Z.div_mul. lia. }
assert (Hqz : 2 <= qz <= 128) by lia.
assert (Hrz8 : rz / 8 = 2 * qz). { rewrite Erz. replace (16 * qz) with (2 * qz * 8) by lia. apply Z.div_mul. lia. }
pose proof L as LL. destruct LL as (G48 & Csb & _).
pose proof TSD as (_ & _ & _ & _ & _ & TR).
assert (PAP1 : apart (sp - 128 - 64) 64 0x134038 0xc000) by (unfold apart; lia).
assert (PAP2 : apart (sp - 128 - 64) 64 0x1ce568 256) by (unfold apart; lia).
destruct (art_alloc_csec1 r8 M8 rom 1283032 ab n rz id nd q spb Q10 Q8 Q9 Q18 Q20 Q21 Q22 Q24 Q25
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hab4 ltac:(lia) ltac:(lia) ltac:(lia) Hid Hq Hspb Hspb' OUT
ltac:(eapply wr_sub; [exact Wab|lia|lia]) Cspb Cpg Cnd ltac:(unfold apart; lia) ltac:(unfold apart; lia))
as (r9 & RUN9 & P9_1 & P9_10 & P9_11 & P9_12 & P9_8 & P9_22 & K9).
set (M9 := Wn 8 M8 (ab + rz - 8) id) in RUN9.
rewrite Etb in P9_22.
assert (KK9 : forall x v, x <> 1%bv -> x <> 8%bv -> x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> x <> 22%bv -> x <> 25%bv -> getr r8 x = v -> getr r9 x = v).
{ intros x v N1 N8 N10 N11 N12 N22 N25 E. rewrite K9 by assumption. exact E. }
assert (A89 : art_agree [(ab + rz - 8, 8)] M8 M9). { unfold M9. eapply art_agree_sub; [zagree|]. clear - Hab Hab' Hrz. zsub. }
assert (G89 : mem_grows M8 M9) by (unfold M9; zgrows).
assert (MEMab : art_poison_lo_ok ab rz \/ art_poison_hi_ok ab rz).
{ clear - Hmem Hab Hrz Hq Hnd End Hrs Hn Hab'. unfold hid in Hmem. unfold art_poison_lo_ok, art_poison_hi_ok, SB, kHighMemBeg, kHighMemEnd. lia. }
assert (L9 : art_layout M9). { eapply art_layout_fp; [exact A89| |exact L]. intros z Hz. clear - Hz Hab Hrz. cbn [art_out fst snd]. repeat split; try exact I; lia. }
assert (W9f : wrA M9 (sp - 128 - 64) 64) by (eapply wr_grows; [exact G89|]; eapply wr_sub; [exact W|lia|lia]).
assert (W9s : wrA M9 (SB + ab / 8) (rz / 8)). { eapply wr_grows; [exact G89|]. eapply wr_sub; [exact Wsh|unfold SB; lia|unfold SB; clear - Hrz8 Hqz Hq Hnd End Hrs Hn Erz; lia]. }
destruct (art_poison3_run r9 M9 rom (0x52338 : bv 64)%bv (sp - 128) ab rz 250 P9_1 ltac:(unfold ret_ok; bveq)
ltac:(apply KK9; try discriminate; exact Q2) P9_10 P9_11 P9_12 ltac:(lia) ltac:(lia) W9f PAP1 PAP2 L9 MEMab Mab8
ltac:(clear - Erz; rewrite Erz; replace (16 * qz) with (2 * qz * 8) by lia; apply Z_mod_mult) ltac:(lia) ltac:(lia) ltac:(intros E; discriminate E) W9s)
as (r10 & RUN10 & _ & P10_1 & P10_2 & P10_8 & P10_9 & P10_18 & P10_19 & P10_20 & P10_21 & K10).
lazymatch type of RUN10 with msteps _ _ (mkst _ _ ?MM _) => set (M10 := MM) in RUN10 end.
assert (KK10 : forall x v, art_poison_kept x -> getr r9 x = v -> getr r10 x = v). { intros x v Kx E. rewrite K10 by exact Kx. exact E. }
#[local] Ltac pk := unfold art_poison_kept; repeat split; discriminate.
assert (A910 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)] M9 M10).
{ unfold M10, art_poison_frame, SB. rewrite Hrz8. clear - Hsp Hsp' Hab Hab' Eka Hab8 Hqz Hq Hnd End Hrs Hn Erz. eapply art_agree_sub; [zagree|].
intros z Hz H. cbn [art_out app fst snd] in H |- *. rewrite ?Z2Nat.id by lia. repeat split; try exact I; lia. }
assert (G910 : mem_grows M9 M10) by (unfold M10, art_poison_frame; zgrows).
assert (R10_18 : getr r10 18 = Z_to_bv 64 ab) by (rewrite P10_18; apply KK9; try discriminate; exact Q18).
assert (R10_22 : getr r10 22 = Z_to_bv 64 tb) by (apply KK10; [pk|exact P9_22]).
assert (R10_8 : getr r10 8 = Z_to_bv 64 (4096 * q)) by (rewrite P10_8; exact P9_8).
pose proof (art_alloc_csec2 r10 M10 rom ab tb q R10_18 R10_22 R10_8 ltac:(lia) ltac:(unfold tb; lia) ltac:(unfold tb; lia) ltac:(lia)) as RUN11a.
lazymatch type of RUN11a with msteps _ _ (mkst ?R _ _ _) => set (R11a := R) in RUN11a end.
assert (MEMtb : art_poison_lo_ok tb (ab + 4096 * q - tb) \/ art_poison_hi_ok tb (ab + 4096 * q - tb)).
{ clear - Hmem Hab Hrz Hq Hnd End Hrs Hn Hab'. unfold hid in Hmem. unfold tb, art_poison_lo_ok, art_poison_hi_ok, SB, kHighMemBeg, kHighMemEnd. lia. }
assert (G810 : mem_grows M8 M10) by (eapply mem_grows_trans; [exact G89|exact G910]).
assert (L10 : art_layout M10).
{ eapply art_layout_fp; [exact (art_agree_trans _ _ _ _ _ A89 A910)| |exact L]. intros z Hz. clear - Hz Hab Hrz Hsp Hab8. cbn [art_out app fst snd]. repeat split; try exact I; lia. }
assert (W10f : wrA M10 (sp - 128 - 64) 64) by (eapply wr_grows; [exact G810|]; eapply wr_sub; [exact W|lia|lia]).
assert (W10s : wrA M10 (SB + tb / 8) ((ab + 4096 * q - tb) / 8)).
{ eapply wr_grows; [exact G810|]. rewrite Htl8, Htb8. eapply wr_sub; [exact Wsh|unfold SB; clear - Hab8 Hqz Hrs Ers Hn; lia|unfold SB; clear - Hab8; lia]. }
destruct (art_poison3_run R11a M10 rom (0x5234c : bv 64)%bv (sp - 128) tb (ab + 4096 * q - tb) 250 ltac:(unfold R11a; gres; reflexivity) ltac:(unfold ret_ok; bveq)
ltac:(unfold R11a; gres; exact P10_2) ltac:(unfold R11a; gres; reflexivity) ltac:(unfold R11a; gres; reflexivity) ltac:(unfold R11a; gres; reflexivity)
ltac:(lia) ltac:(lia) W10f PAP1 PAP2 L10 MEMtb
ltac:(unfold tb; clear - Eka Erz Ers; rewrite Eka, Erz, Ers; replace (4096 * ka + 16 * qz + 8 * qr) with ((512 * ka + 2 * qz + qr) * 8) by lia; apply Z_mod_mult)
ltac:(unfold tb; clear - Htl; replace (ab + 4096 * q - (ab + rz + rs)) with ((512 * q - 2 * qz - qr) * 8) by lia; apply Z_mod_mult)
ltac:(unfold tb; lia) ltac:(lia) ltac:(intros E; discriminate E) W10s)
as (r11 & RUN11 & _ & P11_1 & P11_2 & P11_8 & P11_9 & P11_18 & P11_19 & P11_20 & P11_21 & K11).
lazymatch type of RUN11 with msteps _ _ (mkst _ _ ?MM _) => set (M11 := MM) in RUN11 end.
assert (KK11 : forall x v, art_poison_kept x -> getr R11a x = v -> getr r11 x = v). { intros x v Kx E. rewrite K11 by exact Kx. exact E. }
assert (A1011 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)] M10 M11).
{ unfold M11, art_poison_frame, SB. rewrite Htl8, Htb8. clear - Hsp Hsp' Hab Hab' Eka Hab8 Hqz Hq Hnd End Hrs Hn Erz Ers. eapply art_agree_sub; [zagree|].
intros z Hz H. cbn [art_out app fst snd] in H |- *. rewrite ?Z2Nat.id by lia. repeat split; try exact I; lia. }
assert (G1011 : mem_grows M10 M11) by (unfold M11, art_poison_frame; zgrows).
assert (R11_9 : getr r11 9 = Z_to_bv 64 n). { rewrite P11_9. unfold R11a. gres. rewrite P10_9. apply KK9; try discriminate. exact Q9. }
assert (R11_20 : getr r11 20 = Z_to_bv 64 (ab + rz)). { rewrite P11_20. unfold R11a. gres. rewrite P10_20. apply KK9; try discriminate. exact Q20. }
pose proof (art_alloc_csec3 r11 M11 rom ab n rz R11_9 R11_20 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RUN12a.
lazymatch type of RUN12a with msteps _ _ (mkst ?R _ _ _) => set (R12a := R) in RUN12a end.
assert (MEMub : art_poison_lo_ok (ab + rz) (n / 8 * 8) \/ art_poison_hi_ok (ab + rz) (n / 8 * 8)).
{ rewrite Hn88. clear - Hmem Hab Hrz Hq Hnd End Hrs Hn Hab' En Hm8. unfold hid in Hmem. unfold art_poison_lo_ok, art_poison_hi_ok, SB, kHighMemBeg, kHighMemEnd. lia. }
assert (G811 : mem_grows M8 M11) by (eapply mem_grows_trans; [exact G810|exact G1011]).
assert (A811 : art_agree ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) M8 M11)
by (exact (art_agree_trans _ _ _ _ _ A89 (art_agree_trans _ _ _ _ _ A910 A1011))).
assert (L11 : art_layout M11).
{ eapply art_layout_fp; [exact A811| |exact L]. intros z Hz. clear - Hz Hab Hrz Hsp Hab8. cbn [art_out app fst snd]. repeat split; try exact I; lia. }
assert (W11f : wrA M11 (sp - 128 - 64) 64) by (eapply wr_grows; [exact G811|]; eapply wr_sub; [exact W|lia|lia]).
assert (W11s : wrA M11 (SB + (ab + rz) / 8) (n / 8 * 8 / 8)).
{ eapply wr_grows; [exact G811|]. rewrite Hn888, Hub8.
eapply wr_sub; [exact Wsh|unfold SB; clear - Hab8 Hqz; lia|unfold SB; clear - Hab8 Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia]. }
destruct (art_poison3_run R12a M11 rom (0x5236c : bv 64)%bv (sp - 128) (ab + rz) (n / 8 * 8) 0 ltac:(unfold R12a; gres; reflexivity) ltac:(unfold ret_ok; bveq)
ltac:(unfold R12a; gres; exact P11_2) ltac:(unfold R12a; gres; reflexivity) ltac:(unfold R12a; gres; reflexivity) ltac:(unfold R12a; gres; reflexivity)
ltac:(lia) ltac:(lia) W11f PAP1 PAP2 L11 MEMub Mub8
ltac:(apply Z_mod_mult) ltac:(lia) ltac:(lia) ltac:(intros _; rewrite Hn888; lia) W11s)
as (r12 & RUN12 & _ & P12_1 & P12_2 & P12_8 & P12_9 & P12_18 & P12_19 & P12_20 & P12_21 & K12).
lazymatch type of RUN12 with msteps _ _ (mkst _ _ ?MM _) => set (M12 := MM) in RUN12 end.
assert (KK12 : forall x v, art_poison_kept x -> getr R12a x = v -> getr r12 x = v). { intros x v Kx E. rewrite K12 by exact Kx. exact E. }
assert (A1112 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)] M11 M12).
{ unfold M12, art_poison_frame, SB. rewrite Hn888, Hub8. clear - Hsp Hsp' Hab Hab' Eka Hab8 Hqz Hq Hnd End Hrs Hn Erz Ers En Hm8. eapply art_agree_sub; [zagree|].
intros z Hz H. cbn [art_out app fst snd] in H |- *. rewrite ?Z2Nat.id by lia. repeat split; try exact I; lia. }
assert (G1112 : mem_grows M11 M12) by (unfold M12, art_poison_frame; zgrows).
#[local] Ltac r12hop P12 K12 R12a P11 K11 R11a P10 K10 :=
first [rewrite P12 | rewrite K12 by pk]; unfold R12a; gres; first [reflexivity | (first [rewrite P11 | rewrite K11 by pk]; unfold R11a; gres; first [reflexivity | (first [rewrite P10 | rewrite K10 by pk])])].
assert (R12_2 : getr r12 2 = Z_to_bv 64 (sp - 128)) by exact P12_2.
assert (R12_4 : getr r12 4 = Z_to_bv 64 tp). { rewrite K12 by pk. unfold R12a. gres. rewrite K11 by pk. unfold R11a. gres. rewrite K10 by pk. apply KK9; try discriminate. exact Q4. }
assert (R12_3 : getr r12 3 = getr r8 3). { rewrite K12 by pk. unfold R12a. gres. rewrite K11 by pk. unfold R11a. gres. rewrite K10 by pk. apply KK9; try discriminate. reflexivity. }
assert (R12_8 : getr r12 8 = Z_to_bv 64 (4096 * q)). { rewrite P12_8. unfold R12a. gres. rewrite P11_8. unfold R11a. gres. exact R10_8. }
assert (R12_9 : getr r12 9 = Z_to_bv 64 n). { rewrite P12_9. unfold R12a. gres. exact R11_9. }
assert (R12_18 : getr r12 18 = Z_to_bv 64 ab). { rewrite P12_18. unfold R12a. gres. rewrite P11_18. unfold R11a. gres. exact R10_18. }
assert (R12_19 : getr r12 19 = Z_to_bv 64 nd). { rewrite P12_19. unfold R12a. gres. rewrite P11_19. unfold R11a. gres. rewrite P10_19. apply KK9; try discriminate. exact Q19. }
assert (R12_20 : getr r12 20 = Z_to_bv 64 (ab + rz)). { rewrite P12_20. unfold R12a. gres. exact R11_20. }
assert (R12_21 : getr r12 21 = Z_to_bv 64 (ab + rz - 16)). { rewrite P12_21. unfold R12a. gres. rewrite P11_21. unfold R11a. gres. rewrite P10_21. apply KK9; try discriminate. exact Q21. }
assert (R12_22 : getr r12 22 = Z_to_bv 64 (n / 8 * 8)). { rewrite K12 by pk. unfold R12a. gres. reflexivity. }
assert (A912 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)] M9 M12).
{ eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A910 (art_agree_trans _ _ _ _ _ A1011 A1112))|]. clear. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
assert (G812 : mem_grows M8 M12) by (eapply mem_grows_trans; [exact G811|exact G1112]).
assert (A812 : art_agree ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) M8 M12) by (exact (art_agree_trans _ _ _ _ _ A89 A912)).
assert (Hd1 : art_d1_addr ab rz n = 2147450880 + 512 * ka + 2 * qz + qn).
{ unfold art_d1_addr. rewrite Hn88. replace (ab + rz + 8 * qn) with ((512 * ka + 2 * qz + qn) * 8) by lia. rewrite Z.div_mul by lia. lia. }
assert (L12 : art_layout M12).
{ eapply art_layout_fp; [exact A812| |exact L]. intros z Hz. clear - Hz Hab Hrz Hsp Hab8 Eka. cbn [art_out app fst snd]. repeat split; try exact I; lia. }
assert (GI : forall a n0, 0x10000 <= a -> 0 <= n0 -> a + n0 <= 0x693000 -> art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) a n0).
{ intros a n0 Ha Hn0 Hn1. clear - Ha Hn0 Hn1 Hab Hrz Hsp Hab8 Eka. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
assert (Cpp12 : cellA M12 (0x13a238 + 85) 1 1) by (apply (art_cell_tr1 _ M8 M12 _ _ _ A812); [split; [apply GI; cbn; lia|cbn; lia]|exact Cpp]).
destruct (art_alloc_d1_any r12 M12 rom ab n rz R12_9 R12_20 R12_22 ltac:(lia) ltac:(clear - Hab' Hq Hnd End Hrs Hn Hrz; lia)
ltac:(clear - Hmem Hq Hnd End Hrs Hn Hrz; unfold hid in Hmem; unfold SB, kHighMemBeg; lia) ltac:(lia) ltac:(lia) L12 Cpp12
ltac:(intros _; rewrite Hd1; eapply wr_grows; [exact G812|]; eapply wr_sub; [exact Wsh|clear - Hab8 Hqz Hn En Hm8; lia|clear - Hab8 Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia]))
as (r13 & RUN13 & K13).
set (M13 := art_d1_mem M12 ab rz n) in RUN13.
#[local] Ltac dk := unfold art_d1_kept; repeat split; discriminate.
assert (A1213 : art_agree [(2147450880 + ab / 8, 512 * q)] M12 M13).
{ intros x Hx. unfold M13. apply art_d1_outside; [rewrite Hd1; clear - Eka Hab Hqz Hn En Hm8; lia|rewrite Hd1; clear - Eka Hab' Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia|].
intros _. rewrite Hd1. cbn [art_out fst snd] in Hx. clear - Hx Hab8 Hqz Hq Hnd End Hrs Hn En Hm8 Erz. lia. }
assert (G1213 : mem_grows M12 M13) by (unfold M13; apply art_d1_grows).
assert (A913 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)] M9 M13).
{ eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A912 A1213)|]. clear. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
assert (G813 : mem_grows M8 M13) by (eapply mem_grows_trans; [exact G812|exact G1213]).
assert (A813 : art_agree ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) M8 M13) by (exact (art_agree_trans _ _ _ _ _ A89 A913)).
assert (GT : art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) t 4096).
{ clear - Atsp Atsh Abt Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
assert (GC : art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) ctx 4096).
{ clear - Acsp Acsh Abc Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
assert (GF : art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q)]) (sp - 128) 128).
{ clear - Absp Hsp Hsp' Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
assert (T13 : art_tsd M13 tp key tsd ctx t).
{ eapply art_tsd_fp; [exact A813| | |exact Htp|exact Htp8|exact Htsd|exact Htsd'|exact TSD].
- intros z Hz. eapply art_gap_out; [apply (GI 0x10000 (0x693000 - 0x10000)); lia|lia].
- intros z Hz. eapply art_gap_out; [exact GC|lia]. }
assert (L13 : art_layout M13).
{ eapply art_layout_fp; [exact A813| |exact L]. intros z Hz. eapply art_gap_out; [apply (GI 0x10000 (0x693000 - 0x10000)); lia|lia]. }
assert (Wt13 : wrA M13 t 4096) by (eapply wr_grows; [exact G813|exact Wt]).
assert (Toff : forall d, 0 <= d -> d + 8 <= 4096 -> t + d + Z.of_nat 8 <= 0x10000 \/ 0x693000 <= t + d) by (intros d Hd0 Hd1'; unfold hid in Timg; cbn; clear - Timg Hd0 Hd1'; lia).
destruct (art_cell_exists M13 (t + 2800) 8 ltac:(lia) (Toff 2800 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wt13|lia|cbn; lia])) as (mc & Hmc & Cmc).
destruct (art_cell_exists M13 (t + 2800 + 8) 8 ltac:(lia) ltac:(replace (t + 2800 + 8) with (t + 2808) by lia; exact (Toff 2808 ltac:(lia) ltac:(lia))) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wt13|lia|cbn; lia])) as (mb & Hmb & Cmb).
destruct (art_cell_exists M13 (t + 2800 + 16) 8 ltac:(lia) ltac:(replace (t + 2800 + 16) with (t + 2816) by lia; exact (Toff 2816 ltac:(lia) ltac:(lia))) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wt13|lia|cbn; lia])) as (mr & Hmr & Cmr).
destruct (art_cell_exists M13 (t + 2800 + 104) 8 ltac:(lia) ltac:(replace (t + 2800 + 104) with (t + 2904) by lia; exact (Toff 2904 ltac:(lia) ltac:(lia))) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wt13|lia|cbn; lia])) as (ml & Hml & Cml).
assert (Ccf13 : cellA M13 (sp - 128 + 8) 8 1) by (apply (art_cell_tr1 _ M8 M13 _ _ _ A813); [split; [eapply art_gap_sub; [exact GF|lia|cbn; lia]|cbn; lia]|exact Ccf]).
assert (Cmax13 : cellA M13 (0x13a238 + 44) 4 4096) by (apply (art_cell_tr1 _ M8 M13 _ _ _ A813); [split; [apply GI; cbn; lia|cbn; lia]|exact Cmax]).
assert (Cfb13 : cellA M13 (0x13a238 + 52) 4 190) by (apply (art_cell_tr1 _ M8 M13 _ _ _ A813); [split; [apply GI; cbn; lia|cbn; lia]|exact Cfb]).
destruct (art_alloc_d2_large_fn r13 M13 rom (sp - 128) ab n nd rz tp key tsd ctx t mc mb mr ml
ltac:(rewrite K13 by dk; exact R12_2) ltac:(rewrite K13 by dk; exact R12_4) ltac:(rewrite K13 by dk; exact R12_9)
ltac:(rewrite K13 by dk; exact R12_19) ltac:(rewrite K13 by dk; exact R12_20)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - End Hrs Hrz; lia) ltac:(clear - Hnd End Hrs Hrz Hn; lia) ltac:(lia) Hmc Hmb Hmr Hml
ltac:(eapply wr_grows; [exact G813|]; eapply wr_sub; [exact W|lia|lia]) T13 Ht ltac:(lia) Timg
ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(clear - Acsp; unfold apart in *; lia)
ltac:(clear - Atsp; unfold apart in *; lia)
Cmc Cmb Cmr Cml ltac:(eapply wr_sub; [exact Wt13|lia|lia]) Ccf13 L13 Cmax13 Cfb13)
as (r14 & RUN14 & P14_1 & P14_10 & P14_11 & P14_12 & K14).
set (M14 := art_d2_large_mem M13 (sp - 128) t n nd mc mb mr ml) in RUN14.
#[local] Ltac d2k := unfold art_d2_kept; repeat split; discriminate.
assert (A1314 : art_agree [(sp - 128 - 64, 64); (t + 2800, 112)] M13 M14).
{ unfold M14, art_d2_large_mem. clear - Hsp Hsp' Ht Ht'. eapply art_agree_sub; [zagree|]. zsub. }
assert (G1314 : mem_grows M13 M14) by (unfold M14, art_d2_large_mem; zgrows).
assert (A914 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q); (t + 2800, 112)] M9 M14).
{ eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A913 A1314)|]. clear. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
assert (G814 : mem_grows M8 M14) by (eapply mem_grows_trans; [exact G813|exact G1314]).
assert (OK14 : store_ok ASEGS M14 (Z_to_bv 64 (ab + rz)) (Z.to_nat 4096) = true).
{ apply (wr_wok _ _ _ _ ltac:(eapply wr_grows; [exact G814 | exact Wab])); [lia|]. rewrite Z2Nat.id by lia. clear - Hq Hnd End Hrs Hn Hrz. lia. }
destruct (memset_summary M14 (Z_to_bv 64 (ab + rz)) (Z_to_bv 64 190) (0x52594 : bv 64)%bv 4096 rom
ltac:(lia) ltac:(rewrite art_u_lit by lia; lia) OK14 ltac:(unfold ret_ok; bveq) r14 P14_10 P14_11 P14_12 P14_1)
as (r15 & RUN15 & P15_10 & AG15).
rewrite cbyte_cbz in RUN15. unfold cbz in RUN15. rewrite art_u_lit in RUN15 by lia. change (190 mod 256) with 190 in RUN15.
replace (Z_to_bv 64 ms_base) with (0x126be8 : bv 64)%bv in RUN15 by (apply bv_eq; vm_compute; reflexivity).
change (wbytes M14 (Z_to_bv 64 (ab + rz)) (repeat (Z_to_bv 8 190) (Z.to_nat 4096))) with (Wf M14 (ab + rz) (Z.to_nat 4096) 190) in RUN15.
set (M15 := Wf M14 (ab + rz) (Z.to_nat 4096) 190) in RUN15.
#[local] Ltac mk := cbn; intuition discriminate.
assert (R15 : forall x v, ~ In x ms_clob -> art_d2_kept x -> art_d1_kept x -> getr r12 x = v -> getr r15 x = v).
{ intros x v C1 C2 C3 E. rewrite (AG15 x C1). rewrite K14 by exact C2. rewrite K13 by exact C3. exact E. }
assert (A1415 : art_agree [(ab + rz, 4096)] M14 M15).
{ unfold M15. clear - Hab Hab' Hrz Hq Hnd. eapply art_agree_sub; [zagree|]. intros z Hz H. cbn [art_out app fst snd] in H |- *. rewrite ?Z2Nat.id by lia. repeat split; try exact I; lia. }
assert (G1415 : mem_grows M14 M15) by (unfold M15; zgrows).
assert (A915 : art_agree [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q); (t + 2800, 112); (ab + rz, 4096)] M9 M15).
{ eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A914 A1415)|]. clear. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
assert (G815 : mem_grows M8 M15) by (eapply mem_grows_trans; [exact G814|exact G1415]).
assert (A815 : art_agree ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q); (t + 2800, 112); (ab + rz, 4096)]) M8 M15) by (exact (art_agree_trans _ _ _ _ _ A89 A915)).
assert (GI5 : forall a n0, 0x10000 <= a -> 0 <= n0 -> a + n0 <= 0x693000 ->
art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q); (t + 2800, 112); (ab + rz, 4096)]) a n0).
{ intros a n0 Ha Hn0 Hn1. unfold hid in Timg. clear - Ha Hn0 Hn1 Hab Hrz Hsp Hab8 Eka Timg Ht. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
assert (GF5 : art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q); (t + 2800, 112); (ab + rz, 4096)]) (sp - 128) 128).
{ clear - Absp Atsp Hsp Hsp' Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
assert (GH5 : art_gap ([(ab + rz - 8, 8)] ++ [(sp - 128 - 64, 64); (2147450880 + ab / 8, 512 * q); (t + 2800, 112); (ab + rz, 4096)]) (ab + rz - 16) 8).
{ unfold hid in Hmem. clear - Absp Abt Hmem Hsp Hsp' Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
assert (TI : forall a (k : nat) v, 0x10000 <= a -> a + Z.of_nat k <= 0x693000 -> cellA M8 a k v -> cellA M15 a k v).
{ intros a k v Ha Hk Cc. apply (art_cell_tr1 _ M8 M15 a k v A815); [split; [apply GI5; lia|lia]|exact Cc]. }
assert (TF : forall a (k : nat) v, sp - 128 <= a -> a + Z.of_nat k <= sp -> cellA M8 a k v -> cellA M15 a k v).
{ intros a k v Ha Hk Cc. apply (art_cell_tr1 _ M8 M15 a k v A815); [split; [eapply art_gap_sub; [exact GF5|lia|lia]|lia]|exact Cc]. }
assert (TH : forall a (k : nat) v, ab + rz - 16 <= a -> a + Z.of_nat k <= ab + rz - 8 -> cellA M8 a k v -> cellA M15 a k v).
{ intros a k v Ha Hk Cc. apply (art_cell_tr1 _ M8 M15 a k v A815); [split; [eapply art_gap_sub; [exact GH5|lia|lia]|lia]|exact Cc]. }
assert (L15 : art_layout M15).
{ eapply art_layout_fp; [exact A815| |exact L]. intros z Hz. eapply art_gap_out; [apply (GI5 0x10000 (0x693000 - 0x10000)); lia|lia]. }
pose proof (art_alloc_e32_sec_fn r15 M15 rom raw (sp - 128) ab n rz b1 tp loff (4096 * q) f112 f104 f96 f88 f80 f72 f64 f56 f48 f40 f32 f24
ltac:(apply R15; [mk|d2k|dk|exact R12_2]) ltac:(apply R15; [mk|d2k|dk|exact R12_4]) ltac:(apply R15; [mk|d2k|dk|exact R12_8])
ltac:(clear - Hq Hnd Hab Hab'; lia)
ltac:(apply R15; [mk|d2k|dk|exact R12_9]) ltac:(apply R15; [mk|d2k|dk|exact R12_18]) ltac:(apply R15; [mk|d2k|dk|exact R12_20])
ltac:(apply R15; [mk|d2k|dk|exact R12_21])
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - Hab' Hq Hnd End Hrs Hn Hrz; lia) Mab16 ltac:(lia) Hb1 ltac:(lia) ltac:(lia) Hloff ltac:(lia) Hret
ltac:(apply TI; [lia|cbn; lia|exact Cg]) ltac:(apply TI; [lia|cbn; lia|exact Clsan])
ltac:(unfold apart; clear - Htpl' Hab Hrz; lia)
ltac:(apply TH; [lia|cbn; lia|]; replace (ab + rz - 16 + 1) with (ab + rz - 15) by lia; exact Bh1)
ltac:(eapply wr_grows; [exact G815|]; eapply wr_sub; [exact Wab|lia|clear - Hq Hnd End Hrs Hn Hrz; lia])
ltac:(eapply wr_grows; [exact G815|]; eapply wr_sub; [exact W|lia|lia])
L15 ltac:(apply TI; [lia|cbn; lia|exact Chook])
ltac:(clear - Absp Hq Hnd End Hrs Hn Hrz; unfold apart in *; lia) ltac:(clear - Absp Hq Hnd End Hrs Hn Hrz; unfold apart in *; lia)
ltac:(apply TF; [lia|cbn; lia|]; rewrite <- Ef120; exact F120)
ltac:(apply TF; [lia|cbn; lia|exact F112]) ltac:(apply TF; [lia|cbn; lia|exact F104]) ltac:(apply TF; [lia|cbn; lia|exact F96])
ltac:(apply TF; [lia|cbn; lia|exact F88]) ltac:(apply TF; [lia|cbn; lia|exact F80]) ltac:(apply TF; [lia|cbn; lia|exact F72])
ltac:(apply TF; [lia|cbn; lia|exact F64]) ltac:(apply TF; [lia|cbn; lia|exact F56]) ltac:(apply TF; [lia|cbn; lia|exact F48])
ltac:(apply TF; [lia|cbn; lia|exact F40]) ltac:(apply TF; [lia|cbn; lia|exact F32]) ltac:(apply TF; [lia|cbn; lia|exact F24])
Hrz Mrz16 ltac:(eapply wr_grows; [exact G815|]; eapply wr_sub; [exact Wab|lia|clear - Hq Hnd; lia])
ltac:(apply TI; [lia|cbn; lia|exact Cmag])) as RUN16.
lazymatch type of RUN16 with msteps _ _ (mkst ?R _ ?MM _) => set (R16 := R) in RUN16; set (M16 := MM) in RUN16 end.
assert (A1516 : art_agree [(sp - 128 - 64, 64); (ab, 16); (ab + rz - 16, 8)] M15 M16).
{ unfold M16. clear - Hsp Hsp' Hab Hab' Hrz Hq Hnd. eapply art_agree_sub; [zagree|]. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
assert (G1516 : mem_grows M15 M16) by (unfold M16; zgrows).
assert (Bh12_15 : cellA M15 (ab + rz - 12) 4 n) by (apply TH; [lia|cbn; lia|exact Bh12]).
assert (Bh14_15 : cellA M15 (ab + rz - 14) 2 0) by (apply TH; [lia|cbn; lia|exact Bh14]).
assert (Bid_15 : cellA M15 (ab + rz - 8) 8 id).
{ apply (art_cell_tr1 _ M9 M15 _ _ _ A915); [|unfold M9; apply cell_Wn_hit; [lia|cbn; lia]].
unfold hid in Hmem. clear - Absp Abt Hmem Hsp Hsp' Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; cbn; lia. }
assert (APH : apart (sp - 128 - 64) 64 ab (rz + 16)) by (clear - Absp Hq Hnd End Hrs Hn Hrz; unfold apart in *; lia).
exists R16, M16.
split. { eapply msteps_trans; [exact RUN9|]. eapply msteps_trans; [exact RUN10|]. eapply msteps_trans; [exact RUN11a|]. eapply msteps_trans; [exact RUN11|].
eapply msteps_trans; [exact RUN12a|]. eapply msteps_trans; [exact RUN12|]. eapply msteps_trans; [exact RUN13|]. eapply msteps_trans; [exact RUN14|].
eapply msteps_trans; [exact RUN15|]. exact RUN16. }
split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; f_equal; lia|]. split; [unfold R16; gres; reflexivity|].
split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|].
split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|].
split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|]. split; [unfold R16; gres; reflexivity|].
split; [eapply mem_grows_trans; [exact G815|exact G1516]|].
split. { eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ A815 A1516)|]. unfold art_postL_fp. clear. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; try exact I; lia. }
split; [unfold M16; clear - APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
split; [unfold M16; clear - Bh12_15 APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
split; [unfold M16; clear - APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
split; [unfold M16; clear - Bh14_15 APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
split; [unfold M16; clear - Bid_15 APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
split; [unfold M16; clear - APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
split; [unfold M16; clear - APH Hab Hab' Hrz Hsp Hsp' Hq Hnd; zcell|].
assert (A1316 : art_agree ([(sp - 128 - 64, 64); (t + 2800, 112)] ++ [(ab + rz, 4096)] ++ [(sp - 128 - 64, 64); (ab, 16); (ab + rz - 16, 8)]) M13 M16)
by (exact (art_agree_trans _ _ _ _ _ A1314 (art_agree_trans _ _ _ _ _ A1415 A1516))).
assert (GSH : forall y, 0 <= y < 512 * q ->
art_gap ([(sp - 128 - 64, 64); (t + 2800, 112)] ++ [(ab + rz, 4096)] ++ [(sp - 128 - 64, 64); (ab, 16); (ab + rz - 16, 8)]) (2147450880 + ab / 8 + y) 1).
{ intros y Hy. unfold hid in Hmem. clear - Hy Atsh Hmem Hsp Hsp' Hab Hab8 Eka Hrz Hq Hnd End Hrs Hn Hab'. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia. }
split.
- intros j Hj.
assert (C12 : cellA M12 (2147450880 + ab / 8 + 2 * qz + j) 1 0).
{ unfold M12. rewrite Hn888, Hub8. unfold SB. replace (2147450880 + ab / 8 + 2 * qz + j) with (2147450880 + (512 * ka + 2 * qz) + j) by (rewrite Hab8; lia).
apply cell_Wf_in; [clear - Eka Hab Hqz; lia|rewrite Z2Nat.id by lia; clear - Eka Hab' Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia|rewrite Z2Nat.id by lia; lia|lia]. }
apply (art_cell_tr1 _ M13 M16 _ _ _ A1316).
+ split; [|cbn; clear - Hab8 Eka Hab Hab' Hqz Hj Hq Hnd End Hrs Hn En Hm8 Erz; lia]. replace (2147450880 + ab / 8 + 2 * qz + j) with (2147450880 + ab / 8 + (2 * qz + j)) by lia.
apply GSH. clear - Hj Hqz Hq Hnd End Hrs Hn En Hm8 Erz. lia.
+ unfold M13. apply cell_d1_other; [rewrite Hd1; clear - Eka Hab Hqz Hn En Hm8; lia|rewrite Hd1; clear - Eka Hab' Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia
|clear - Hab8 Eka Hab Hqz Hj; lia|cbn; clear - Hab8 Eka Hab' Hqz Hj Hq Hnd End Hrs Hn En Hm8 Erz; lia
|intros _; rewrite Hd1, Hab8; unfold apart; cbn; clear - Hj; lia|exact C12].
- split; [|split; [unfold R16; gres; apply R15; [mk|d2k|dk|exact R12_3]|unfold R16; gres; rewrite Q4; apply R15; [mk|d2k|dk|exact R12_4]]].
intros Hm.
assert (C13 : cellA M13 (2147450880 + ab / 8 + 2 * qz + qn) 1 m8).
{ unfold M13, art_d1_mem. rewrite Hnm. destruct (Z.eqb_spec m8 0) as [E|NE]; [contradiction|]. rewrite Hd1.
replace (2147450880 + ab / 8 + 2 * qz + qn) with (2147450880 + 512 * ka + 2 * qz + qn) by (rewrite Hab8; lia).
apply cell_Wn_hit; [clear - Eka Hab Hqz Hn En Hm8; lia|cbn; clear - Eka Hab' Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia]. }
apply (art_cell_tr1 _ M13 M16 _ _ _ A1316); [|exact C13].
split; [|cbn; clear - Hab8 Eka Hab Hab' Hqz Hq Hnd End Hrs Hn En Hm8 Erz; lia]. replace (2147450880 + ab / 8 + 2 * qz + qn) with (2147450880 + ab / 8 + (2 * qz + qn)) by lia.
apply GSH. clear - Hqz Hq Hnd End Hrs Hn En Hm8 Erz. lia.
Qed.
End SE.
End FPX.
