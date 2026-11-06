(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStepAB0 PmSpecs PmParKit PmBSrcKit LibIfaceAJ.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBParKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepARB0.L5SAR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "1list"; "1option"; "1prod"; "2and"; "2eq"; "2or"; "3Z"; "0FF"; "0HI"; "0L"; "0LB"; "0LK"; "4Model"; "0M"; "0M'"]; ["0MV"; "5mrestrict"; "6credit"; "7ahid"; "7ar_sptop"; "7fframe"; "7ri_inv"; "7vml_of"; "8defined"; "8outside"; "8range"; "8u32_at"; "8u64_at"; "8u8_at"; "8writable"; "9avis"]; [":zeros_at"; ";ADDR_B"; "<CHUNK"; "<PST"; "<VLong"; "<p_b"; "<p_depth"; "<p_done"; "<p_k"; "<p_src"; "<p_stk"; "<p_tb"; "<p_tg"; "<parser_at"; "<pot_parser"; "<pot_text"]; ["<pst"; "<pstate"; "<sr_qc"; "<srcst"; "<strm"; "<vec_at"; "<vstr"; "=agA"; "=agsh"; ">set_more"; "?HV"; "?accA"; "?annA"; "?aobjA"; "?credit_keep"; "?credit_le"]; ["?ec_at"; "?frame_okA"; "?o_ec"; "?o_p"; "?o_v"; "?scA"; "?src_step"; "?visitor_at"; "@base_okA"; "Aek"; "Bloaded_segments"; "Cremovelast"; "Dadd"; "Ddiv"; "Dle"; "Dlt"]; ["Dmodulo"; "Dmul"; "Dpow"; "Dsub"; "0W"; "0a"; "0ar"; "0c"; "0cr"; "0cr'"; "0cr1"; "0cr2"; "0cr3"; "0fb"; "0model"; "0n"]; ["0oec"; "0ois"; "0op"; "0ov"; "0p"; "0p1"; "0p2"; "0p3"; "0s"; "0s'"; "0scr"; "0sm1"; "0sm2"; "0sm3"; "0sp"; "0src1"]; ["0src2"; "0src3"; "Ebv"; "0v"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBPAR.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Lemma parser_pop_updA : ltac2:(TCodec.tc2 tcn__PmBParKit "TH'SByR0%211'2y8%511%311p051'7'Q@&Q=&R:&Q1&QK&QLr5r3r2r1%9887654321&R>zr4%3221&R<+\0%22;1&RB+2+R0%3221%;251&QGr8r7r6+8%544321r9+9%@261+3%:44921r:+@%E2<1+ZH%?44921&QHr;%2417<I&H%1339K&Mr<%O26C+1%44Q>321&Kr=+<%Q5271&RC&Q6%11E%3219%84QG751%41B%621<%QA2Q@1&QEr?r>+[8%QB221&Q5%11F&Q8%11H&R;'QA&Q:%11L%4231%>8R9R7R6=:861&QB&Q9%11L%311%R52R41%41B%611&Q2%R5221%R:21R0rCrB%;1J%=11%R344317'5'QF&Q;%118(Q4%13RIRHRG%63531rHrG%R=421RLRGp041pV:S71pV0S81pU@S91rD(Q3&Q7rA%211%QH12%QJ21R0%Q314%D15&Q<%117%QB18%QA19%Q>1:%QA2Q@1%>9R9;9875431%SH8SGSFSESD@Q3Q21p0B1p0Q11p0Q71p0Q=1p0QC1p0R31p0R71p0RA1p0RG1p0RJ1p0RN1p0S41p0S:1p0SA1p0SJ1p0SO1pVBT:1pV4T<1pV6T=1pQ0T?1pNT@1").
Proof. intros M M' op ois s.
intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
[AG1 _] [AG9 _] AG2 SH D' C8 C12 Hd VEC' Hq Hq' AGQ AGT.
pose proof AG2 as [AG2d _].
unfold PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
assert (AG4 : forall a n, op + 16 <= a -> a + n <= op + 360 -> PMFA.agA M M' a n).
{ intros a n X1 X2. split; [eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| intros x Hx; apply SH; lia]. }
split; [apply (L5C.u64_at_agree RSEGS M M'); [exact AG1| lia| lia| exact H0]|].
split; [exact D'|].
split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
split; [exact C8|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [eapply L5C.agree_on_sub; [exact AG9|lia|lia]|lia|lia|exact H9]|].
split; [exact C12|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 16) 1); lia|lia|lia|exact H16]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 20) 4); lia|lia|lia|exact H20]|].
split; [apply (PMFA.nullis_at_agreeA RSEGS PMB.AD M M' (op + 32)); [lia|lia| apply AG4; lia| exact NI]|].
split; [apply (PMFA.src_fields_at_agreeA RSEGS M M' (op + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 320) 4); lia|lia|lia|exact H320]|].
split; [apply (L5C.u64_at_agree RSEGS M M'); [apply (AG4 (op + 328) 8); lia|lia|lia|exact H328]|].
split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
split; [exact VEC'|].
split; [right; reflexivity|]. split; [exact B2|]. unfold PM.MAX_DEPTH in *. lia.
Qed.
Lemma src_step_transA : ltac2:(TCodec.tc2 tcn__PmBParKit "B'QC'QD&R6r6r5r3r2%544321r8%741654p031p041pVL;1pVJ<1pVH=1pW4?1pW2@1pW0A1").
Proof. intros src1 src2 src3 sm1 sm2 sm3.
unfold PMSPA.src_step. intros (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5).
split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply B4; apply A4; exact X| lia].
Qed.
Lemma parser_more_updA : ltac2:(TCodec.tc2 tcn__PmBParKit "T8'SByR0%211'2y8%511%311p051'7'Q@&Q=&R:&Q1&QK&QLr6r4r3r2%9887654321&R>zr5%3221&R<+\0%22;1&RB+2+R0%3221%;251&QGr9r8r7+8%544321r:+9%@261+[G%:44921&QHr;%2417<D&H%1339F&Mr<%J26>%34Q821A'6'5%13Q>EQ1+1%33Q@G1%5231&QB&Q9%11@%311%Q:2Q91%41>%611&Q2%Q:221%Q?21Q5rAr@r=%<11%>11%Q945418&Q5r>%211%QI2QH1r?%511&RA+Q0&Q8%115%QI2QH1%5241%QN271%R321QIrDrC%@1E%91F%R12R01%=2<1%QN46541'QF&Q;%119(Q4r1%23RCRB1%Q@3641rIrH%R8421RFRHp041pV:S21pV0S31pU@S41rE&QIrB%221Q<%S78S6S5S4S34IH1p061p0E1p0M1p0Q81p0Q=1p0QD1p0QJ1p0R01p0R71p0R<1p0R?1p0RC1p0RI1p0S01p0S91p0S>1pW8SJ1pVBSJ1pV4SL1pV6SM1pQ0SO1pNT01").
Proof. intros M M' op ois s v.
intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
[AG1 _] AG2 SH D' C8 Hv Hq Hq' AGQ Hb Hb' AGV AGT.
pose proof AG2 as [AG2d _].
unfold PMPK.set_more, PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
assert (AG4 : forall a n, op + 9 <= a -> a + n <= op + 384 -> PMFA.agA M M' a n).
{ intros a n X1 X2. split; [eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| intros x Hx; apply SH; lia]. }
split; [apply (L5C.u64_at_agree RSEGS M M'); [exact AG1| lia| lia| exact H0]|].
split; [exact D'|].
split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
split; [exact C8|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 9) 1); lia|lia|lia|exact H9]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 12) 4); lia|lia|lia|exact H12]|].
split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 16) 1); lia|lia|lia|exact H16]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 20) 4); lia|lia|lia|exact H20]|].
split; [apply (PMFA.nullis_at_agreeA RSEGS PMB.AD M M' (op + 32)); [lia|lia| apply AG4; lia| exact NI]|].
split; [apply (PMFA.src_fields_at_agreeA RSEGS M M' (op + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 320) 4); lia|lia|lia|exact H320]|].
split; [apply (L5C.u64_at_agree RSEGS M M'); [apply (AG4 (op + 328) 8); lia|lia|lia|exact H328]|].
split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
split; [apply (PMFA.vec_at_agreeA RSEGS M M' (op + 360)); [lia|lia|exact Hb|exact Hb'| eapply (L5C.agree_on_sub M M'); [exact AG2d|lia|lia]| exact AGV| exact VEC]|].
split; [exact Hv|]. split; [exact B2| exact B3].
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Lemma op_vis : ltac2:(TCodec.tc2 tcn__PmBParKit "T?'1'3'7%2211%411&E%611&B'SByR0%211'2y8%511%311p051'='Q@&Fv9r:r9r8r7r6r5&Gr4%211%;8:9876541&R1%12;4&Q=&R:&Q1&QK&QL&R3%124=r3%887654A2=1%427A&A&C%12HF%321H'4&R>+Vb\P0r2%3221+Soooooood0%5231%7231'5&R@+8%2281z%53QI21'6&R<+QoonlP0+`PPPPPTP0%3221%B21@+\0%62B1%E216%9241%H2;1%I2B1&Q0r1&R=%12JC+QoooPP0%@221+3%73621+Q0%D2Q01%821J%F217+Q<%=3<21+D%J2Q61%>21Q0%L21=+1%C3B21&N%14QLDQ<K&RC&DvRF%211+XPPP0%5221%QE2Q11%QF2R:QD%Q92QOQE%Q:2R>Q5%QI221&Or?r=%R1221%431RBR6p061p0:1pV0S>1pU<S?1&QMr>%231R3QB+^@%QI2S01%R13SER61%R:241%R;281%R<2F1%R=2N1%R>2Q11%R?2Q81%R@2Q?1%RA2QH1tQ2SARC1tV6SORH1p0RJ1p0S41p0S71pVBSD1pV4T41pULT51pUNSH1pNSJ1p2T61pUBT41pJT61pBT71pHT:1").
Proof. intros LB FF LK cr Aw M model fb ois s.
intros HH FOK PA op MV.
assert (Eop : op = fb + 464) by reflexivity.
pose proof FOK as ((rs & Hf) & F1024).
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n).
{ intros a n X1 X2. exists (fb, 4, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
assert (O8 : op mod 8 = 0).
{ rewrite Eop. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite F1024, Z.add_0_r in Dm.
rewrite Dm. replace (1024 * (fb / 1024) + 464) with ((128 * (fb / 1024) + 58) * 8) by lia. apply Z_mod_mult. }
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model op 384 0 0 HH (PMKB.aobj_of_aobjA FF op 384 (AOF op 384 ltac:(lia) ltac:(lia)) O8)
ltac:(lia) ltac:(reflexivity)) as ((X1 & X2 & X3 & X4 & X5) & OBIG & ODEF & OVIS & _ & _ & _).
pose proof PA as (_ & _ & PC0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & PC320 & _).
pose proof (PMBSK.src_acc M op ois s PA) as CS.
assert (C32 : PMSPA.accA M (op + 32) 352).
{ intros a Ha. destruct (Z_lt_le_dec a (op + 320)) as [Y|Y]; [apply CS; lia| apply PC320; lia]. }
assert (Zop : L5KA.zeros_at MV (op / 8 + SB) (24 / 8)).
{ apply (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model op 24 HH (AOF op 24 ltac:(lia) ltac:(lia)) O8); [lia| reflexivity| exact PC0]. }
assert (Z32 : L5KA.zeros_at MV ((op + 32) / 8 + SB) (352 / 8)).
{ apply (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model (op + 32) 352 HH (AOF (op + 32) 352 ltac:(lia) ltac:(lia))); [| lia| reflexivity| exact C32].
replace (op + 32) with (op + 4 * 8) by lia. rewrite Z_mod_plus_full. exact O8. }
change (24 / 8) with 3 in Zop. change (352 / 8) with 44 in Z32. unfold SB in Zop, Z32.
split; [split; [lia| split; [exact O8| unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia]]|].
split; [exact Zop|]. split; [exact Z32|].
split.
{ assert (E20 : (op + 20) / 8 = op / 8 + 2).
{ replace (op + 20) with (4 + (op / 8 + 2) * 8) by (pose proof (Z.div_mod op 8 ltac:(lia)); lia). rewrite Z.div_add by lia. lia. }
rewrite E20. intros i Hi. replace (op / 8 + 2 + 2147450880 + i) with (op / 8 + 2147450880 + (2 + i)) by lia. apply Zop. lia. }
split; [apply (proj2 (L5A.writable_vis _ M op 384 OVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]|].
split; [lia|]. split; [intros a n Ha Hn; eapply L5A.avis_sub; [exact OVIS| lia| lia]|]. split; [apply AOF; lia| exact Eop].
Qed.
Lemma ov_vis : ltac2:(TCodec.tc2 tcn__PmBParKit "S?'1'3'7%2211%411&E%611&B'SByR0%211'2y8%511%311p051'=&Fv9r8r7r6r5r4r3&Gr2%211%;8:9876541&R1%12;4&R7&R:&Q1&R4%122;%5443>1%324>&A&C%12EC%321E'4&R>+Vb\P0%221C+SooooooooH%42E1%6231'5&R@+8%22J1z%53QD21'6&R<+QoonlP0+`PPPPPTP0%3221%A21Q2%52Q3:%C215%8231%F2:1%G2A1&Q0r1&R=%12Q;B+QoooPP0%?221+1%73621&N%14Q;8QAH&RC&DvRF%211+XPPP0%5221%Q72E1&L+QUik0%24QEBQK1&QMr<%231QNQ5+]@%Q22R51%Q:3RIR11%QB241%QC281%QD2<1%QE2D1%QF2G1%QG2Q01tQ2RCQI1tV8S1QN1p0R01p0R71p0R:1pULS51pUNRH1pNRJ1p2S61pUBS41pJS61pBS71pHS:1").
Proof. intros LB FF LK cr Aw M model fb.
intros HH FOK (VU & VC) ov MV.
assert (Eov : ov = fb + 432) by reflexivity.
pose proof FOK as ((rs & Hf) & F1024).
assert (AO : PMSPA.aobjA FF ov 8).
{ exists (fb, 4, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
assert (O8 : ov mod 8 = 0).
{ rewrite Eov. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite F1024, Z.add_0_r in Dm.
rewrite Dm. replace (1024 * (fb / 1024) + 432) with ((128 * (fb / 1024) + 54) * 8) by lia. apply Z_mod_mult. }
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model ov 8 0 0 HH (PMKB.aobj_of_aobjA FF ov 8 AO O8)
ltac:(lia) ltac:(reflexivity)) as ((X1 & X2 & X3 & X4 & X5) & OBIG & ODEF & OVIS & _ & _ & _).
assert (Zov : L5KA.zeros_at MV (ov / 8 + SB) (8 / 8)) by exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model ov 8 HH AO O8 ltac:(lia) ltac:(reflexivity) VC).
change (8 / 8) with 1 in Zov. unfold SB in Zov.
split; [split; [lia| split; [exact O8| unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia]]|].
split; [exact Zov|].
split; [apply (proj2 (L5A.writable_vis _ M ov 8 OVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]|].
split; [lia|].
split; [apply (proj2 (L5A.u64_at_vis _ M ov 1238880 OVIS ltac:(lia) ltac:(lia))); exact VU|].
split; [exact AO| exact Eov].
Qed.
Lemma base_keepW : ltac2:(TCodec.tc2 tcn__PmBParKit "R<'1'3'7%2211%411&E%611&J%811'SByR0%211'2y8%511%311p051&R9v:vRFr7r6r5r4r3r2r1%:9987654321'4&R>+RPP0%2215&R?+QVhP0%2281%7241&I%12@<p031pU<Q51+VbRh0%<21?+VbRh8%;2A1%@231%92IDp021pU<Q=1+VbSZC%=2L1+VbSa@%F21I+VbSaD%E2K1%J231r9%D21Op031pU<QH1&R8&R:&Q1%3321Q:p011p061p0@1p0C1p0L1p0Q91pQ0QE1pNQF1pU:QO1pVFR61pVNR71pBR41pHR71").
Proof. intros LB FF sp scr W M M'.
intros E O1 O2 O3 O4 (RO0 & (can & Hcan & CAN) & NL & LL).
assert (AGD : forall a, 0 <= a < 2 ^ 64 -> PMST.dep PMB.AD a -> L5.outside W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha D Ho. apply E. split; [exact Ha|]. split; [|exact Ho]. unfold aclient, aclient_g. right; right; left.
pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia| exact (PMB.ly_static L C LY a D)]. }
cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock PMB.AD ADDR_A] in *.
split; [|split; [|split]].
- intros i Hi. cbn [pa_rw_lo PMB.AD ADDR_A] in Hi. rewrite E; [apply RO0; cbn [pa_rw_lo PMB.AD ADDR_A]; exact Hi|]. split; [lia|]. split; [| apply O1; lia]. unfold aclient, aclient_g. right; right; left.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia| intros X; pose proof (L5A.aly_static_lo L C LYa _ X); lia].
- exists can. split; [exact Hcan|]. apply (L5C.u64_at_agree RSEGS M M'); [|cbn [pa_canary PMB.AD ADDR_A]; lia|cbn [pa_canary PMB.AD ADDR_A]; lia| exact CAN]. intros i Hi. cbn [pa_canary PMB.AD ADDR_A] in Hi. apply AGD; [lia| right; left; cbn [pa_canary PMB.AD ADDR_A]; lia| apply O2; lia].
- cbn [pa_need_locks PMB.AD ADDR_A] in NL |- *. apply (L5C.u8_at_agree RSEGS M M'); [|lia|lia| exact NL]. intros i Hi.
apply AGD; [lia| apply PMST.in_foot_nl; cbn [pa_need_locks PMB.AD ADDR_A]; lia| replace i with 0x690d53 by lia; exact O3].
- cbn [pa_locale_lock PMB.AD ADDR_A] in LL |- *. unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4%nat 0x690e30); [exact LL| lia| cbn; lia|].
intros i Hi. cbn in Hi. apply AGD; [lia| apply PMST.in_foot_ll; cbn [pa_locale_lock PMB.AD ADDR_A]; lia| apply O4; lia].
Qed.
Lemma oec_vis : ltac2:(TCodec.tc2 tcn__PmBParKit "SC'1'3'7%2211%411&E%611&B'SByR0%211'2y8%511%311p051'=&Fv9r:r9r8r7r6r5&Gr4%211%;8:9876541&R1%12;4&R0&R:&R2&Q1%221;r3%655?2;1%524?&A&C%12FD%321F'4&R>+Vb\P0r2%3221+Soooooooo@%5231%7231'5&R@+8%2281z%53QF21'6&R<+QoonlP0+`PPPPPTP0%3221%B21@+@%62B1%E216%9241%H2;1%I2B1&Q0r1&R=%12JC+QoooPP0%@221+2%73621&N%14Q>8Q0?&RC&DvRF%211+XPPP0%5221%Q92E1&K%14QGAQ9R1&QMr>%231Q<K+o0%Q22R71%Q:3RKQ?1%QC241%QD281%QE2;1%QF2C1%QG2F1%QH2O1tQ2REQJ1tV2S3QO1p0R11p0R91p0R<1pU@S71pW8S81pULS91pUNRL1pNRN1p2S:1pUBS81pJS:1pBS;1pHS>1").
Proof. intros LB FF LK cr Aw M model fb v c.
intros HH FOK (EU & EU8 & ED & EC) oec MV.
assert (Eo : oec = fb + 992) by reflexivity.
pose proof FOK as ((rs & Hf) & F1024).
assert (AO : PMSPA.aobjA FF oec 16).
{ exists (fb, 4, rs). split; [exact Hf|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
assert (O8 : oec mod 8 = 0).
{ rewrite Eo. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite F1024, Z.add_0_r in Dm.
rewrite Dm. replace (1024 * (fb / 1024) + 992) with ((128 * (fb / 1024) + 124) * 8) by lia. apply Z_mod_mult. }
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model oec 16 0 0 HH (PMKB.aobj_of_aobjA FF oec 16 AO O8)
ltac:(lia) ltac:(reflexivity)) as ((X1 & X2 & X3 & X4 & X5) & OBIG & ODEF & OVIS & _ & _ & _).
assert (Zo : L5KA.zeros_at MV (oec / 8 + SB) (16 / 8)) by exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model oec 16 HH AO O8 ltac:(lia) ltac:(reflexivity) EC).
change (16 / 8) with 2 in Zo. unfold SB in Zo.
split; [split; [lia| split; [exact O8| unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia]]|].
split; [exact Zo|].
split; [apply (proj2 (L5A.writable_vis _ M oec 16 OVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]|].
split; [lia|].
split; [apply (proj2 (L5A.u32_at_vis _ M oec v (L5A.avis_sub _ oec 16 oec 4 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EU|].
split; [exact AO| exact Eo].
Qed.
Lemma pot_text_le_parserA : ltac2:(TCodec.tc2 tcn__PmBParKit "Q4'Q@&B'4&R>z&Q8r2%211%5241+;%7231%9231&QO&R5v:&Q>&QJvRF%2241r3%5221%8271%:21@&Q?&Q;r4%211&Q<%113%63;31%A2@1%C21<p0:1p0F1pUBQ11pVBQ31").
Proof. intros s cr.
intros Hk CR. pose proof (PMB.ly_cost L C LY) as (K8 & B3 & BO).
pose proof (PMPK.pot_text_le_parser (PMSPA.HV L ar) s (PM.pot_parser (PMSPA.HV L ar) s)) as X.
unfold PMSP.credit_le in X. cbn [PMSPA.HV LibIfaceAJ.heap_view HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in X.
rewrite K8, BO in X. specialize (X ltac:(lia) ltac:(lia) Hk ltac:(split; lia)). destruct X as (X1 & X2).
unfold PMSPA.credit_le, PMSPA.scA in *. cbn [fst snd] in *. rewrite B3 in *. destruct CR as (C1 & C2). split; lia.
Qed.
Lemma credit_le_keepA : ltac2:(TCodec.tc2 tcn__PmBParKit "@&B&QOr2r4%3221&QNr5r3%342516%8223p021p071pV<<1pV:=1pUF>1pUB?1").
Proof. intros cr cr1 p p1. unfold PMSPA.credit_le, PMSPA.credit_keep. intros (A1 & A2) (B1 & B2). split; lia. Qed.
Lemma credit_keep_transA : ltac2:(TCodec.tc2 tcn__PmBParKit "A&B&QNr6r5r3r2%544321r8%741654p031p041pV@;1pV><1pV<=1pUJ>1pUH?1pUF@1").
Proof. intros cr1 cr2 cr3 p1 p2 p3. unfold PMSPA.credit_keep. intros (A1 & A2) (B1 & B2). split; lia. Qed.
Lemma credit_keep_textA : ltac2:(TCodec.tc2 tcn__PmBParKit "Q<'Q@&B&QNr2r1&R5v:&Q?&QJvRF%2241&Q;r4%211&Q<%113%93631%<2;1r3%811%612%>3;21%A2@1%E4DC61'5'7&Q8%11?r5%311%63531&Q>r6%22G1%M2L1%42I7%O2N1%Q34IC31p081p0@1pUDQ71pUBQ81pVDQ:1pVBQ;1").
Proof. intros s s' cr cr'.
intros CK Ek. pose proof (PMB.ly_cost L C LY) as (K8 & B3 & BO).
unfold PMSPA.credit_keep, PMSPA.scA, PM.pot_parser, PM.credit_add in *. rewrite Ek. cbn [fst snd] in *. rewrite B3 in *. destruct CK as (C1 & C2). split; lia.
Qed.
End WithHeap.
End PMBPAR.
