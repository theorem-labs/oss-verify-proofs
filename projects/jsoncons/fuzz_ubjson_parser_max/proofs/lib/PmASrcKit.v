(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa
PmModelFactsA PmStepA PmStep.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmASrcKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStatics.PMST."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStaticsA.PMSTA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmStepA.PMKA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepAR.L5SAR."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["0Aw"; "0B1"; "0B2"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2I"]; ["2and"; "2eq"; "2ex"; "2not"; "2or"; "3map"; "4Z"; "0FF"; "0HI"; "0K"; "0L"; "0LB"; "0LK"; "5fetch_word"; "5is_ecall"; "6Model"]; ["7decode_any"; "8Jalr"; "8instr"; "9bvmap"; "0M"; "0M'"; "0M2"; "0M3"; "0MV"; "0R"; ":mrestrict"; ";credit"; "<FS_BYTES"; "<aclient"; "<ahid"; "<ar_fs"]; ["<ar_sptop"; "<asan_layout"; "<asan_run"; "<ff_addr"; "<ff_bytes"; "<ff_class"; "<fframe"; "<model_rt"; "<ri_inv"; "<vml"; "<vml_of"; ">defined"; ">img_clear"; ">outside"; ">range"; ">u32_at"]; [">u64_at"; ">writable"; "=SCFG"; "?avis"; "?cfg"; "@zeros_at"; "AADDR_A"; "BCHUNK"; "BSRC"; "BSTRM"; "BVLong"; "Biss_at"; "Bp_b"; "Bp_k"; "Bp_src"; "Bp_tb"]; ["Bparser_at"; "Bparser_own"; "Bpst"; "Bsm_eg"; "Bsm_g"; "Bsr_qc"; "Bstrm"; "Bvs_own"; "Bvstr"; "CagA"; "Cagsh"; "DaccA"; "DannA"; "DaobjA"; "Dframe_okA"; "Do_is"]; ["Do_p"; "Do_src"; "Dwith_src"; "Edep"; "Fbase_okA"; "Gwapp"; "HFPState"; "Hgetr"; "ITSet"; "Jsrealizes"; "Kmem_grows"; "Lamodel_ok"; "Lastk"; "Mdk"; "Mek"; "Nloaded_segments"]; ["0SCFG_P"; "OIn"; "Oincl"; "Padd"; "Pdiv"; "Ple"; "Plt"; "Pmodulo"; "Pmul"; "Pof_nat"; "Ppow"; "Psub"; "0V"; "0W"; "0a"; "0ar"]; ["0b"; "0c"; "0cr"; "0de'"; "0eg"; "0f"; "0fb"; "0fr"; "0fx"; "0g"; "0i"; "0l"; "0l1"; "0l2"; "0m"; "0m1"]; ["0m2"; "0model"; "0model1"; "0n"; "0o"; "0ois"; "0op"; "0os"; "0p"; "0pc"; "0q"; "0r"; "0rem'"; "0s"; "0scr"; "0sm"]; ["0sp"; "0st"; "0st'"; "QNoDup"; "Qelem_of"; "Qlist_elem_of"; "RBV"; "RZ_to_bv"; "Rbv"; "0str"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Module PMASK.
Abbreviation RSEGS := Asan.M.loaded_segments.
Lemma src_acc : ltac2:(TCodec.tc2 tcn__PmASrcKit "O'U8yR0%211';y8%511%311p051'F'RB&R@&S?&R6&RK&RLr4r3r2r1%9887654321r5&SC+Q0%2281+Y0%<3521p071pYLB1pY<D1pY>E1pR:G1").
Proof. intros M op ois s.
intros PA. destruct PA as (_ & _ & _ & _ & _ & _ & _ & _ & NI & SF & _).
destruct NI as (_ & _ & NC & _ & _ & IOS). destruct IOS as (_ & _ & _ & _ & _ & _ & _ & IC).
destruct SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC).
intros a Ha. destruct (Z_lt_le_dec a (op + 32 + 80)) as [X|X]; [apply NC; lia|].
destruct (Z_lt_le_dec a (op + 32 + 80 + 152)) as [Y|Y]; [apply IC; lia|]. apply SC; lia.
Qed.
Lemma parser_src_fieldsA : ltac2:(TCodec.tc2 tcn__PmASrcKit "U6'U8yR0%211';y8%511%311p051'F'RB&R@&S?&R6&RK&RLr7r5r4r3%9887654321&SEzr6%3221&SC+\0%22;1&SJ+2+R0%3221%;251&RIr:r9r8+XH%544321r;+Z0%@261%94381<&RJr<%D2;8+Q8%443821&RE&R>%11?%311%O2N1%41C%611&R7%O221%Q421Jr?r>%;1E%=11%M44317&R<%11D%Q<2Q;1r=%411&SH+Q0&R=%115%Q<2Q;1%5241%QA271%QF21Q<rBrA%?1C%91D%QD2QC1%=2<1%QA46541'A'RH&R?%11:(R:r2r1%33R721%83751rGrF%QM4216R<p041pYBRG1pY8RH1pX4RI1&S:rDrC%3221&R0+Y0%R@241%QI1M%QK11%54S0831rE+Y8%RF2;1%94S431QI+Y@%RI251%<4S7F1Q7+YH%RL2H1%?4S:J1Q:%R61:%R811%S421E%S52S4F%S22N>%R;1Q0%R=11%S521R7%S:241rKrJrI&S2rH(R8%RE12%RG11%331Q<Q;%6251%SO8SNSMSLSK:981p0<1p0B1p0D1p0H1p0L1p0Q01p0Q51p0Q<1p0QA1p0R21p0R:1p0RE1p0RI1p0RO1p0S51p0S;1p0SA1p0SF1p0SM1p0T61p0T;1pYJTG1pX8TH1pYLTH1pY<TJ1pY>TK1pR<TM1pR:TN1").
Proof. intros M M' op ois s de' rem'.
intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
[AG1 SH1] [AG2 SH2] SH3 Hq Hq' AGQ Hb Hb' AGB AGT MG C1 C2 C3 C4 Q1 Q2 Q3.
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & CC & C240).
unfold PMSPA.with_src, PM.parser_at, PM.src_fields_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.sr_qc PM.sr_de PM.sr_rem] in *.
assert (U64 : forall a v, op <= a -> a + 8 <= op + 280 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
assert (U64b : forall a v, op + 320 <= a -> a + 8 <= op + 384 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact X]. }
assert (U32 : forall a v, op <= a -> a + 4 <= op + 280 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
assert (U8 : forall a v, op <= a -> a + 1 <= op + 280 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
split; [apply U64; [lia|lia|exact H0]|].
split; [apply (L5.defined_grows M M' op 384 MG D)|].
split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH1; lia| exact C24]|].
split; [apply U8; [lia|lia|exact H8]|]. split; [apply U8; [lia|lia|exact H9]|]. split; [apply U32; [lia|lia|exact H12]|].
split; [apply U8; [lia|lia|exact H16]|]. split; [apply U32; [lia|lia|exact H20]|].
split; [apply (PMFA.nullis_at_agreeA RSEGS PMA.AD M M' (op + 32)); [lia|lia| split; [intros i Hi; apply AG1; lia| intros x Hx; apply SH1; lia]| exact NI]|].
split.
{ split; [apply U64; [lia|lia|exact F1]|]. split; [apply U64; [lia|lia|exact F2]|].
split; [apply (L5.defined_grows M M' _ 8 MG F3)|].
split; [replace (op + 24 + 264) with (op + 288) by lia; exact C1|]. split; [replace (op + 24 + 272) with (op + 296) by lia; exact C2|].
split; [replace (op + 24 + 280) with (op + 304) by lia; exact C3|]. split; [replace (op + 24 + 288) with (op + 312) by lia; exact C4|].
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact G4|].
split; [destruct AGQ as [AGq _]; apply (L5C.defined_agree M M'); [exact AGq| exact DC]|].
split; [destruct AGQ as [_ SHq]; apply (PMFA.accA_agree M M' _ _ SHq CC)|].
apply (PMFA.accA_agree M M' (op + 24 + 240) 56); [intros x Hx; destruct (Z_lt_le_dec x (op + 280)) as [X|X]; [apply SH1; lia| apply SH3; lia]| exact C240]. }
split; [apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact H320]|].
split; [apply U64b; [lia|lia|exact H328]|].
split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH2; lia| exact C320]|].
split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| split; [intros i Hi; apply AG2; lia| intros x Hx; apply SH2; lia]| exact AGT| exact TB]|].
split; [apply (PMFA.vec_at_agreeA RSEGS M M' (op + 360)); [lia|lia|lia|lia| intros i Hi; apply AG2; lia| exact AGB| exact VEC]|].
split; [exact B1|]. split; [exact B2|]. exact B3.
Qed.
Lemma agsh_blk : ltac2:(TCodec.tc2 tcn__PmASrcKit "R0'QA'QB'9'='F%2211%411&QF%611&QN%811'U8yR0%211';y8%511%311p051&S>r;r:r9r8r7r6r5r4r3%:9987654321&S5%116&SA(<%14NN76%33N1?&SEz%221<&SC%12?>&SJ+2+Q?%3221%9251&RJ%14IHGFp031p0;1p0?1p0D1p0G1pXNQA1pYFQB1pR<Q51pR:Q61pWLQ?1pYNQF1pZ2QG1pQ@QD1pQHQG1pX0QM1pQFQO1").
Proof. intros L ar LB FF sp scr W M M' q m.
intros E WAPP Hin Hq Hqm x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SH. unfold BIGSHADOW_LO, BIGSHADOW_HI in SH.
apply E. split; [lia|]. split.
- unfold aclient, aclient_g. do 6 right. exists (q, m). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKA.S_mono; lia.
- apply (PMKA.wapp_outside_shadow W (S x) WAPP). unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.
Lemma parser_chunk_keepA : ltac2:(TCodec.tc2 tcn__PmASrcKit "SB'U8yR0%211';y8%511%311p051'F'RB&R@&S?&R6&RK&RLr5r3r2r1%9887654321&SEzr4%3221&SC+\0%22;1&SJ+2+R0%3221%;251&RIr8r7r6%44321;&RE&R>%11H%311%E2D1%417%611&R7%E221%J21@&RJr;r:%<1@%>11%544318&QK%1365Mr<r9%C11%E11%6341?&R<%11<%Q:2Q91%31?&SH+Q0&R=%11C%Q92Q81%5241%Q>271%QC21Q9r@r?%>1C%91D%QA2Q@1%=2<1%Q>46541'A'RH&R?%11:(R:%13R4R3R2%63531rErD%QH421R7R2p041pYBRB1pY8RC1pX4RD1rAr>%RE8RDRCRBRA2GF1p041p0C1p0K1p0Q51p0Q91p0Q?1p0QB1p0QI1p0QO1p0R51p0R;1p0RD1p0RI1pYLS41pY<S61pY>S71pR<S91pR:S:1").
Proof. intros M M' op ois s.
intros PA Ho Ho' [AG SH] Hq Hq' SHQ DOP DCQ Hb Hb' AGB AGT.
pose proof PA as (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3).
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & CC & C240).
assert (U64 : forall a v, op <= a -> a + 8 <= op + 384 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
assert (U32 : forall a v, op <= a -> a + 4 <= op + 384 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
assert (U8 : forall a v, op <= a -> a + 1 <= op + 384 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
unfold PM.parser_at, PM.src_fields_at.
split; [apply U64; [lia|lia|exact H0]|]. split; [exact DOP|].
split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
split; [apply U8; [lia|lia|exact H8]|]. split; [apply U8; [lia|lia|exact H9]|]. split; [apply U32; [lia|lia|exact H12]|].
split; [apply U8; [lia|lia|exact H16]|]. split; [apply U32; [lia|lia|exact H20]|].
split; [apply (PMFA.nullis_at_agreeA RSEGS PMA.AD M M' (op + 32)); [lia|lia| split; [intros i Hi; apply AG; lia| intros x Hx; apply SH; lia]| exact NI]|].
split.
{ split; [apply U64; [lia|lia|exact F1]|]. split; [apply U64; [lia|lia|exact F2]|].
split; [intros i Hi; replace (op + 24 + 256 + i) with (op + (280 + i)) by lia; apply DOP; lia|].
split; [apply U64; [lia|lia|exact F4]|]. split; [apply U64; [lia|lia|exact F5]|]. split; [apply U64; [lia|lia|exact F6]|]. split; [apply U64; [lia|lia|exact F7]|].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
split; [exact DCQ|].
split; [apply (PMFA.accA_agree M M' _ _ SHQ CC)|].
apply (PMFA.accA_agree M M' (op + 24 + 240) 56); [intros x Hx; apply SH; lia| exact C240]. }
split; [apply U32; [lia|lia|exact H320]|]. split; [apply U64; [lia|lia|exact H328]|].
split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| split; [intros i Hi; apply AG; lia| intros x Hx; apply SH; lia]| exact AGT| exact TB]|].
split; [apply (PMFA.vec_at_agreeA RSEGS M M' (op + 360)); [lia|lia|lia|lia| intros i Hi; apply AG; lia| exact AGB| exact VEC]|].
split; [exact B1|]. split; [exact B2|]. exact B3.
Qed.
Lemma iss_st_updA : ltac2:(TCodec.tc2 tcn__PmASrcKit "S0'U8yR0%211';y8%511%311p051'F'RH&R;&S?&R6&RKr8r6r5(R9r4r3r2%43321%<7;:98761&SEzr7%3221&SC+X@%22?1&SJ+2+R0%3221%;251&RIr;r:r9+TH%544321r<+TL%@261+SD%:44921&RJr=%E2<9+4%443921&S:r>%2216'Ar?(R:r1%23Q7Q61%53QB41rCrB%K421Q:Q<p041pYBQH1pY8QI1pX4QJ1&QO%Q92@M%24QJ>1O'D%A3QOQ2Q?%B3R0Q3Q9%3221rAr@%QK3HMQ8%R37R2R1R032F1p051p0:1p0>1p0L1p0Q01p0Q61p0Q<1p0QC1p0QL1p0R11pZ6R@1pZ4RA1pX:RB1pXDRC1pZDRC1pY<RE1pR<RG1pR:RH1").
Proof. intros M M' ois str g eg st st'.
intros IA Ho Ho' [AG1 SH1] [AG2 SH2] SH3 MG AGB C32 ST'.
destruct IA as (H0 & D & C & H16 & H24 & H32 & H40 & H48 & H64 & VS & H104 & H112 & IOS & E1 & E2).
destruct IOS as (I0 & I32 & I36 & I40 & I48 & IZ & ID & IC & IST).
assert (U64 : forall a v, ois <= a -> a + 8 <= ois + 152 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
assert (U64b : forall a v, ois + 156 <= a -> a + 8 <= ois + 272 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact X]. }
unfold PM.iss_at, PM.iosb_at. cbn [PM.sm_g PM.sm_eg PM.sm_st] in *.
split; [apply U64; [lia|lia|exact H0]|]. split; [apply (L5.defined_grows M M' _ _ MG D)|].
split; [apply (PMFA.accA_agree M M' ois 120); [intros x Hx; apply SH1; lia| exact C]|].
split; [apply U64; [lia|lia|exact H16]|]. split; [apply U64; [lia|lia|exact H24]|]. split; [apply U64; [lia|lia|exact H32]|].
split; [apply U64; [lia|lia|exact H40]|]. split; [apply U64; [lia|lia|exact H48]|]. split; [apply U64; [lia|lia|exact H64]|].
split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (ois + 80)); [lia|lia| split; [intros i Hi; apply AG1; lia| intros x Hx; apply SH1; lia]| exact AGB| exact VS]|].
split; [apply U64; [lia|lia|exact H104]|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact H112]|].
split.
{ split; [apply U64; [lia|lia|exact I0]|]. split; [replace (ois + 120 + 32) with (ois + 152) by lia; exact C32|].
split; [apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact I36]|].
split; [apply U64b; [lia|lia|exact I40]|]. split; [apply U64b; [lia|lia|exact I48]|].
split; [apply (PMF.zeros_at_agree M M'); [intros i Hi; apply AG2; lia| exact IZ]|].
split; [apply (L5.defined_grows M M' _ _ MG ID)|].
split; [apply (PMFA.accA_agree M M' (ois + 120) 152); [intros x Hx; destruct (Z_lt_le_dec x (ois + 152)) as [X|X]; [apply SH1; lia|];
destruct (Z_lt_le_dec x (ois + 156)) as [Y|Y]; [apply SH3; lia| apply SH2; lia]| exact IC]|].
exact ST'. }
split; [exact E1| exact E2].
Qed.
Lemma iss_unread_whereA : ltac2:(TCodec.tc2 tcn__PmASrcKit "QM'U8yR0%211';y8%511%311p051'F'RH'RF&R;&S?&R6&RKr4r3r2r1%877654321'D'@&SE&SC+RA%22:1&RD%11:%6231&RC%11=+S8%92A1%;231%=261'B'Ar6(R:%13GFE%43O31r5%@11%E2I1%?13%F2KM%H221%J241%K281qYBQ91%?2Q:1qY8Q;1%A2Q<1qX4Q=1%C2Q>1%Q32E1p0Q51pZ0Q?1pZDQA1pY<QC1pR:QE1").
Proof. intros M ois str sm.
intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _ & _ & _ & E1 & E2).
destruct VS as (D & _ & H). destruct str as [n|c n p]; cbn [PM.vs_data PM.vs_size] in *.
- destruct H as (Hn & _). left. lia.
- destruct H as (_ & _ & _ & Hn & _). right. exists c, n, p. split; [reflexivity| lia].
Qed.
Lemma iss_size_ltA : ltac2:(TCodec.tc2 tcn__PmASrcKit "Q:'U8yR0%211';y8%511%311p051'F'RH'RF&R;&S?&R6&RKr4r3r2r1%877654321'@&SEz&SK&RC%118&RD%11:%5231%8271&SF&SJ+2+K%3221%5271%@271p0B1pZ0L1pZDN1pY<Q01pR:Q21").
Proof. intros M ois str sm.
intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _ & _ & _ & E1 & E2).
destruct VS as (D & _ & H). destruct str as [n|c n p]; cbn [PM.vs_data PM.vs_size] in *.
- destruct H as (Hn & _). lia.
- destruct H as (_ & _ & _ & Hn & Hc & _). lia.
Qed.
Lemma elem_of_InA : ltac2:(TCodec.tc2 tcn__PmASrcKit "?'F'9%112&SAr2r1%33621&U4'U5%119r3%45;9217p061pXH;1pZF>1").
Proof. intros x l. induction l as [|a l IH]; intros H; [destruct H|]. destruct H as [<-|H]; [constructor| constructor; apply IH; exact H]. Qed.
Lemma fst_neq_appA : ltac2:(TCodec.tc2 tcn__PmASrcKit "Q5'9'='F%2211%411'U3&E&8%1266&4r6r5%33921%74:;51%92<1&SA(<r4%24@@71r7%53A21r3%64DD51%83D14&C'A%13H7?%311p051p091p0@1pY2M1p6N1pY0O1p4Q01pXLO1pXJQ01").
Proof. intros l1 l2 B1 m1 B2 m2.
induction l1 as [|a l1 IH]; intros ND H1 H2; [destruct H1|]. cbn [app map] in ND. inversion ND as [|x l NI ND']. subst x l.
destruct H1 as [->|H1].
- cbn [fst] in NI. intros E. subst B2. apply NI. apply elem_of_InA. rewrite map_app. apply in_or_app. right. apply (in_map fst l2 (B1, m2) H2).
- apply IH; assumption.
Qed.
Lemma defined_dk : ltac2:(TCodec.tc2 tcn__PmASrcKit "R6'QA'QB'9'='F%2211%411&QF%611'U8yR0%211';y8%511%311p051&S=r:r9r8r7r6r5r4r3%9887654321'@&SEr1%2261&SF&SC%1298%3251%8251&Q=r=r<r;r2%57432GFE1p071pXFQ71z%A21E%>2GF&SJ+2+R0%3221%G251&QK%13Q1ON%23Q2Q1Q0p021p051p0<1p0?1p0Q11pY8QH1pWNQI1pR<Q>1pR:Q?1pYNQL1pZ2QM1pQ@QJ1pQHQM1pX0R31pQFR51").
Proof. intros L ar LB FF sp scr M M' a n.
intros DK CL Ha Hn D i Hi. replace (a + i) with (a + i) by lia. apply (DK (a + i)); [lia| apply CL; lia| apply D; lia].
Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Lemma mach_vis : ltac2:(TCodec.tc2 tcn__PmASrcKit "QM'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051'O&QHvHr7r6r5r4r3r2&QJr1%211%;8:9876541&S4&S?&R6%33219'@&QL&Q:&Q>%12@>%321@+RPP0+QV`P0%73321&R0+QW[WH+QoooPP0%34?721&QO+QW[X0+1%34C;21%A251%B2:1p0D1p0I1pY4Q61pR:Q81p2QD1pX6QB1pQJQD1pQ@QE1pQHQH1").
Proof. intros LB FF LK cr Aw M model.
intros HH BASE.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (_ & _ & VIMG & _).
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
pose proof (L5A.statics_facts L C M LYa ST) as (_ & CSB & CUAR & _).
split; [apply L5A.img_clear_mrestrict; destruct BASE as (IC & _); cbn [pa_rw_lo PMA.AD ADDR_A] in IC; exact IC|].
split.
- apply (proj2 (L5A.u64_at_vis _ M 1289464 2147450880 (VIMG 1289464 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CSB.
- apply (proj2 (L5A.u32_at_vis _ M 1289472 1 (VIMG 1289472 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CUAR.
Qed.
Lemma stk_vis : ltac2:(TCodec.tc2 tcn__PmASrcKit "R='9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051'O&QHvHr:r9r8r7r6r5&QJr4%211%;8:9876541&S<vSOr3%342961'@&SEz%2215%326;%5221&SC&SK&Q@%11<+XPPP0%4221+TP0%7221%821E%>21I&SJ+2+Q?%3221%C2N1&R1&S?&Q:&Q>%12Q6Q4%321Q6%D2Q5Q2%74621Q3%M291%N2?1p0J1p0Q11p0Q61pX@R11pYNR21pZ2R31pY4QF1pR:QH1p2R41pX6R21pQJR41pQ@R51pQHR81").
Proof. intros LB FF LK cr Aw M model sp scr fr.
intros HH ASTK Hf. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (_ & VIS & _).
split; [lia|]. split; [lia|].
apply (proj2 (L5A.writable_vis _ M (sp - fr) fr (VIS (sp - fr) fr ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M (sp - scr) scr); [exact SDEF| lia| lia]. lia. lia.
Qed.
Lemma src_vis : ltac2:(TCodec.tc2 tcn__PmASrcKit "T?'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051'O'RB&QHvHr<r;r:r9r8r7&QJr6%211%;8:9876541&RN%12;4&R@&S?&R6&RK&RL&S0%124=r5%887654A2=1&S<vSOr4%342F51&S1%12<G&Q:&Q>r=%221M%421O'@&SE+VbTP0r2%3221+SooooooofH%5231%7231'A&SG+8%2281z%53QO21'D&SC+QoonlP0+`PPPPPTP0%3221%B21@+Y8%62B1%E216%9241%H2;1%I2B1&R5r1&SD%>2JC%221D+QoooPP0%A221+Q4%83721&R1%14QG9Q1@&SK&Q@%11QA+XPPP0%4221%Q92E1%Q:2QDQ8r3%N21Q:%O2QKJ%Q>221&R3rBr@%QG221%431QM8p061p0;1pY8S91pWNS:1&RMrA%231QHQ7&Q?%11R7%QM21QK&Q<%QA231%R02Q<1%R2241%R3281%R42<1%R52K1%R62Q21%R72Q51%R82Q?1tRBS>R:1tY@SLR@1p0RC1p0RH1p0S21p0S51pYNT11pZ2T21pYLSD1pY<T41pX>T51pY4SH1pR:SJ1p2T61pX6T41pQJT61pQ@T71pQHT:1").
Proof. intros LB FF LK cr Aw M model fb ois s sp scr.
intros HH FOK PA ASTK os MV. destruct FOK as ((rs & Hf) & F1024). cbn [pa_frame PMA.AD ADDR_A] in *.
assert (AO : PMSPA.aobjA FF os 296).
{ exists (fb, 4, rs). split; [exact Hf|]. unfold os, PMSPA.o_src, PMSPA.o_p. cbn [ff_addr ff_class ff_bytes pa_off_p PMA.AD ADDR_A].
unfold ff_bytes. cbn. lia. }
assert (O8 : os mod 8 = 0).
{ unfold os, PMSPA.o_src, PMSPA.o_p. cbn [pa_off_p PMA.AD ADDR_A]. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite F1024, Z.add_0_r in Dm.
rewrite Dm. replace (1024 * (fb / 1024) + 464 + 24) with ((128 * (fb / 1024) + 61) * 8) by lia. apply Z_mod_mult. }
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model os 296 sp scr HH (PMKA.aobj_of_aobjA FF os 296 AO O8) ltac:(lia) ltac:(reflexivity))
as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
assert (ACC : PMSPA.accA M (os + 8) 288).
{ replace (os + 8) with (PMSPA.o_p PMA.AD fb + 32) by (unfold os, PMSPA.o_src; lia). exact (src_acc M _ ois s PA). }
split; [split; [lia| split; [exact O8| exact OBIG]]|].
split.
{ apply (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model (os + 8) 288 HH).
- destruct AO as (f & Hf' & X1 & X2). exists f. split; [exact Hf'|]. lia.
- replace (os + 8) with (os + 1 * 8) by lia. rewrite Z_mod_plus_full. exact O8.
- lia. - reflexivity. - exact ACC. }
split.
{ apply (proj2 (L5A.writable_vis _ M os 296 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]. }
split; [lia|]. split; [intros a n Ha Hn; eapply L5A.avis_sub; [exact OVIS| lia| lia]|]. split; [exact AO|].
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & _).
destruct (WF _ Hf) as (W1 & W2 & _). unfold ff_addr, ff_class in W1, W2. cbn in W1, W2. unfold ff_bytes in W2. change (64 * 2 ^ 4) with 1024 in W2.
unfold os, PMSPA.o_src, PMSPA.o_p. cbn [pa_off_p PMA.AD ADDR_A]. unfold FS_BYTES in *. split; lia.
Qed.
Lemma dep_img : ltac2:(TCodec.tc2 tcn__PmASrcKit "@'F&S3&R6r1%3221'@&SE+V]dl0r2%3221&SF+ValWD%2241%8241p0:1pWN?1").
Proof. intros a.
unfold PMST.dep, pm_foot, pm_initc. cbn [pa_errcat_guard pa_syscat_guard pa_loc_foot pa_atexit pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A app].
intros [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
- repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
- lia.
- repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
Lemma base_keep : ltac2:(TCodec.tc2 tcn__PmASrcKit "QF'9'='F%2211%411&QF%611&QN%811'U8yR0%211';y8%511%311p051&S>vJvSOr7r6r5r4r3r2r1%:9987654321'@&SE+RPP0%2215&SF+VbTP0%2281%7241&QM%12@<p031pWNQ51&S4&S?&R6%3321Dp011p061p0C1pR<O1pR:Q01pWLQ91pYNQ@1pZ2QA1pQ@Q>1pQHQA1").
Proof. intros LB FF sp scr W M M'.
intros EK OUT BASE. apply (PMKA.base_ok_keepA RSEGS PMA.AD L ar LB FF sp scr W M M' EK PMA.addrs_wf_A); [| |exact BASE].
- intros a D. pose proof (dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
split; [exact (PMA.ly_static L C LY a D)|]. apply OUT; lia.
- intros a Ha. cbn [pa_rw_lo PMA.AD ADDR_A] in Ha. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
split; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia| apply OUT; lia].
Qed.
Lemma fs_above_img : ltac2:(TCodec.tc2 tcn__PmASrcKit "Q9'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051&QI&QHvHr7r6r5r4r3r2r1%9887654321&SE+VbTP0&Q?vSO%211%5241p071pWJB1pR:D1p2Q01pX6N1pQJQ01pQ@Q11pQHQ41").
Proof. intros LB FF LK cr Aw M V.
intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & FSAPP & _ & FSIMG & _).
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG. unfold app_mem, FS_BYTES in *. lia.
Qed.
Lemma blk_img : ltac2:(TCodec.tc2 tcn__PmASrcKit "QE'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051&QI&QHvHr9r8r7r6r5r4r3%9887654321&SA(<r2%24LL51r:%53M21'D&SE&SC%12<;+RPP0%4221+VbTP0%621@%8231p0:1p0A1pXNQ:1pYFQ;1pWJN1pR:Q01p2Q<1pX6Q:1pQJQ<1pQ@Q=1pQHQ@1").
Proof. intros LB FF LK cr Aw M V q m.
intros HH Hq. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
destruct (WB _ Hq) as ((_ & BI & _) & _). cbn [fst snd] in BI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in BI. lia.
Qed.
Lemma blk_obj_apart : ltac2:(TCodec.tc2 tcn__PmASrcKit "QJ'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051&QI&QHvHr;r:r9r8r7r6r5%9887654321&SA(<r4%24LL51r<%53M21&RMr3%23461'D&SE&SC%12@?%321?%32@<%521C%7231p091p0=1p0D1pY8Q=1pY:Q>1pXNQ?1pYFQ@1pWJQ31pR:Q51p2QA1pX6Q?1pQJQA1pQ@QB1pQHQE1").
Proof. intros LB FF LK cr Aw M V q m o n.
intros HH Hq (f & Hf & X1 & X2).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
destruct (WB _ Hq) as (_ & _ & _ & _ & _ & _ & FSB). cbn [fst snd] in FSB.
destruct (WF f Hf) as (Y1 & Y2 & _). destruct FSB as [Z1|Z1]; [left; lia| right; lia].
Qed.
Lemma iss_vis : ltac2:(TCodec.tc2 tcn__PmASrcKit "T9'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051'O'RH'RF&QHvHr<r;r:r9r8r7&QJr6%211%;8:9876541&RN%12;4&R;&S?&R6&RK&RO%123<r5%77654@2<1&S<vSOr4%342E51%82:E&Q:&Q>r=%221K%421M'@&SE+VbTP0r2%3221+Sooooooog@%5231%7231'A&SG+8%2281z%53QN21'D&SC+QoonlP0+`PPPPPTP0%3221%B21@+X@%62B1%E216%9241%H2;1%I2B1&R5r1&SD%12JC+QoooPP0%@221+Q2%73621&R1%14QD8Q0?&SK&Q@%11Q?+XPPP0%4221%Q82D1%Q92QBQ7r3%M21Q9%N2QII%Q=221&R3rBr@%QF221%431QK8p061p0;1pY8S71pWNS81&RMrA%231QGQ6&S1%12R<RI%QL2Q81%QN241%QO281%R02G1%R12N1%R22Q11%R32Q:1tRBS8R51tY<SFR;1p0R=1p0RB1p0RK1p0RN1pYNSK1pZ2SL1pZ0S=1pZDS?1pX>SO1pY4SB1pR:SD1p2T01pX6SN1pQJT01pQ@T11pQHT41").
Proof. intros LB FF LK cr Aw M model fb str sm sp scr.
intros HH FOK IA ASTK ois MV. destruct FOK as ((rs & Hf) & F1024). cbn [pa_frame PMA.AD ADDR_A] in *.
assert (AO : PMSPA.aobjA FF ois 272).
{ exists (fb, 4, rs). split; [exact Hf|]. unfold ois, PMSPA.o_is. cbn [ff_addr ff_class ff_bytes pa_off_is PMA.AD ADDR_A].
unfold ff_bytes. cbn. lia. }
assert (O8 : ois mod 8 = 0).
{ unfold ois, PMSPA.o_is. cbn [pa_off_is PMA.AD ADDR_A]. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite F1024, Z.add_0_r in Dm.
rewrite Dm. replace (1024 * (fb / 1024) + 96) with ((128 * (fb / 1024) + 12) * 8) by lia. apply Z_mod_mult. }
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model ois 272 sp scr HH (PMKA.aobj_of_aobjA FF ois 272 AO O8) ltac:(lia) ltac:(reflexivity))
as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
assert (ACC : PMSPA.accA M ois 272).
{ destruct IA as (_ & _ & C0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS & _). destruct IOS as (_ & _ & _ & _ & _ & _ & _ & IC & _).
intros a Ha. destruct (Z_lt_le_dec a (ois + 120)) as [X|X]; [apply C0; lia| apply IC; lia]. }
split; [split; [lia| split; [exact O8| exact OBIG]]|].
split; [apply (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model ois 272 HH AO O8 ltac:(lia) ltac:(reflexivity) ACC)|].
split; [apply (proj2 (L5A.writable_vis _ M ois 272 OVIS ltac:(lia) ltac:(lia))); apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]|].
split; [lia|]. split; [intros a n Ha Hn; eapply L5A.avis_sub; [exact OVIS| lia| lia]|]. split; [exact AO|].
unfold ois, PMSPA.o_is, PMSPA.o_src, PMSPA.o_p. cbn [pa_off_is pa_off_p PMA.AD ADDR_A]. lia.
Qed.
Lemma blk_byte_vis : ltac2:(TCodec.tc2 tcn__PmASrcKit "SA'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051'O&QHvHr:r9r8r7r6r5&QJr4%211%;8:9876541&SA(<r3%24NN61r;%53O21&QK%13><:&RK%13A?>'A&SG+8%22C1z%53Q:21'@&SE%12JH&SF&SC%12ML%32L1%7251&Q:&Q>r<%221Q5%421H+TP0%=21Q6+1%<2Q81&SK&Q@vSO%211+XPPP0%5221%F271r1%Q331QA:'D+QoonlP0+`PPPPPTP0%I221%M21QF%N2?4%6221&R5&SD%12QKQ7+QoooPP0%Q1221%53>1G&Q?%11E%Q82I1&Q<%Q7231%Q;21R4%C241%Q>281%Q?2?1%Q@2G1%QA2J1%QB2Q41tRBRAQ71p0Q=1p0QF1p0QM1p0R01p0R31p0R:1pYBS51pXNS61pYFS71pY4RJ1pR:RL1p2S81pX6S61pQJS81pQ@S91pQHS<1").
Proof. intros LB FF LK cr Aw M model q m p.
intros HH Hq D ACC M8 Hp MV.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
destruct (WB _ Hq) as (BR & _ & _ & _ & _ & _ & FSB). cbn [fst snd] in *.
destruct BR as (B0 & B1 & B16 & B3 & B4 & (A0 & A1 & A2)). unfold BIGSHADOW_LO, BIGSHADOW_HI in A1.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (_ & _ & _ & _ & VBLK & _).
assert (Q8 : q mod 8 = 0) by (apply PMKA.mod16_8'; exact B16).
set (o := 8 * (p / 8)).
assert (Ho : o <= p < o + 8) by (unfold o; pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia).
assert (Hq8 : q <= o /\ o + 8 <= q + m).
{ pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. pose proof (Z.div_mod m 8 ltac:(lia)) as Dm. rewrite Q8 in Dq. rewrite M8 in Dm.
assert (L1 : q / 8 <= p / 8) by (apply Z.div_le_mono; lia).
assert (L2 : p / 8 < q / 8 + m / 8).
{ apply (Z.div_lt_upper_bound p 8 (q / 8 + m / 8)); lia. }
unfold o. lia. }
split; [lia|]. split; [lia|].
split; [apply (proj2 (L5A.defined_vis _ M p 1 (VBLK q m p 1 Hq ltac:(lia) ltac:(lia)))); apply (L5.defined_sub M q m); [exact D| lia| lia]|].
split; [destruct A1 as [X|X]; [right; lia| left; lia]|].
split.
{ replace (p / 8) with (o / 8) by (unfold o; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
pose proof (PMKA.blk_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model q m o 8 HH Hq ltac:(lia) ltac:(lia)
ltac:(unfold o; rewrite Z.mul_comm, Z_mod_mult; reflexivity) ltac:(lia) ltac:(reflexivity)) as Z8.
change (8 / 8) with 1 in Z8. apply Z8. intros a Ha. apply ACC. lia. }
destruct FSB as [X|X]; [left; lia| right; lia].
Qed.
Lemma frb_of : ltac2:(TCodec.tc2 tcn__PmASrcKit "QJ'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051&QI&QHvHr7r6r5r4r3r2r1%9887654321&SAr8%23H41'@&SEz&QC%11:%4231&SC&QD&QE%11?%311%5271&SJ+2+Q?%3221%?251%A2<1p0C1pX<Q<1p0H1pWJQ31pR:Q51p2QA1pX6Q?1pQJQA1pQ@QB1pQHQE1").
Proof. intros LB FF LK cr Aw M V.
intros HH f Hf. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & _).
destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. split; lia.
Qed.
Lemma brb_of : ltac2:(TCodec.tc2 tcn__PmASrcKit "QH'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051&QI&QHvHr7r6r5r4r3r2r1%9887654321&SAr9%23J41'@&SEz&8%13Q0Q0:%4231&SC&>%13Q4Q4>%3251&SJ+2+Q?%3221%=251%?2:1p0A1pX2Q<1p0F1pWJQ11pR:Q31p2Q?1pX6Q=1pQJQ?1pQ@Q@1pQHQC1").
Proof. intros LB FF LK cr Aw M V.
intros HH b Hb. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _ & _ & _ & _ & _ & _ & _ & (_ & _ & SPT & _) & _).
destruct (proj1 (WB b Hb)) as (X0 & _ & _ & _ & X4 & _). split; lia.
Qed.
Lemma aobj_fb : ltac2:(TCodec.tc2 tcn__PmASrcKit "L'9&QF%211'F&RNr4r3%3221&SE&SC+Q0%2261%4216%4287r5+oH%7221%9241&RMr7%2316?p041p0:1p0@1pY8E1pY:F1pX>G1pQ@I1").
Proof. intros FF fb o n.
intros ((rs & Hf) & _) H1 H2. exists (fb, 4, rs). split; [exact Hf|]. unfold ff_addr, ff_class. cbn. unfold ff_bytes. cbn. lia.
Qed.
Lemma src_piece_parser : ltac2:(TCodec.tc2 tcn__PmASrcKit "T:'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051&QI'RB&QHvHr?r>r=r<r;r:r8%9887654321&RN%1293&SB&RAr7%211rA%53Q021&S>vJvSOrBr5r4(6(<&SC&S1&R6%221F+X0%5221+Q8%84QAQA21(:%11QB%<3QC31%C9BA@E?>1Q1Q0&S:%12Q4Q3&R@&S?&RK&RL&S0%12AQ8%685B43Q<1Q8Q7&R0%E2DQ<+X8%H221&RE&R>%11Q?%311%84>QE51r@%N2MQF+X@%Q1221&R7%>4D521%Q32Q2QL+XH%Q6221%B4HQA1QL%Q72Q6:+Y0%Q:221%F4LQ@1R0&SE%C1R5%E11%321R6z%521R8%QB2DR:%I1QM%K11%QE21C%:241rFrD%Q72QG1rC&S2(R8%Q31R2%Q511%331R9Q1%52R51%QC8QBQOQAQ@:871p0<1p0B1p0E1p0J1p0O1p0Q41p0Q;1p0QE1p0QM1p0R01p0RE1p0RL1p0RO1pYNSI1pZ2SJ1pYJSK1pX8SL1pYLS>1pY<SN1pX>SO1pWJSB1pR@SD1pR>SE1p2T11pX6SO1pQJT11pQ@T21pQHT51").
Proof. intros LB FF LK cr Aw M2 M3 V fb ois s de' rem' sp scr.
intros HH FOK INC EK MG PA C1 C2 C3 C4 Q1 Q2 Q3.
unfold PMSPA.o_src, PMSPA.o_p in *. cbn [pa_off_p PMA.AD ADDR_A] in *.
pose proof FOK as ((rs & Hfb) & F1024).
pose proof (frb_of _ _ _ _ _ _ _ HH) as FRB. pose proof (brb_of _ _ _ _ _ _ _ HH) as BRB.
assert (AOS : PMSPA.aobjA FF (fb + 464 + 24) 296) by (apply (aobj_fb FF fb); [exact FOK| lia| lia]).
assert (WS : PMKA.wapp [(fb + 464 + 24 + 256, 40)]).
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & _).
destruct (WF _ Hfb) as (Y1 & Y2 & _). unfold ff_addr, ff_class, ff_bytes in Y1, Y2. cbn in Y1, Y2. unfold app_mem, FS_BYTES in FSAPP, Y2.
apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; destruct FSAPP as (F0 & [F1|F1] & F2); [left; lia| right; lia]| apply PMKA.wapp_nil]. }
assert (OUTO : forall i, ~ (fb + 464 + 24 + 256 <= i < fb + 464 + 24 + 296) -> L5.outside [(fb + 464 + 24 + 256, 40)] i).
{ intros i N r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
assert (OUTB : forall q m, In (q, m) LB -> forall i, q <= i < q + m -> L5.outside [(fb + 464 + 24 + 256, 40)] i).
{ intros q m Hq i Hi. apply OUTO. destruct (blk_obj_apart _ _ _ _ _ _ _ q m _ 296 HH Hq AOS) as [X|X]; lia. }
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PTB & PVEC & _).
assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB) by (apply INC; unfold PM.parser_own, PM.src_own; cbn; left; reflexivity).
assert (VIN : In (PM.p_b s, 32 * 2 ^ PM.p_k s) LB) by (apply INC; unfold PM.parser_own, PM.src_own, PM.vec_own; cbn; right; left; reflexivity).
apply (parser_src_fieldsA M2 M3 (fb + 464) ois s de' rem' PA).
- destruct (frb_of _ _ _ _ _ _ _ HH (fb, 4, rs) Hfb). unfold ff_addr in *. cbn in *. lia.
- destruct (frb_of _ _ _ _ _ _ _ HH (fb, 4, rs) Hfb). unfold ff_addr, ff_class, ff_bytes in *. cbn in *. lia.
- apply (PMKA.agA_obj L ar LB FF sp scr _ M2 M3 EK WS FRB (fb + 464) 280 ltac:(apply (aobj_fb FF fb); [exact FOK| lia| lia])). intros i Hi. apply OUTO. lia.
- apply (PMKA.agA_obj L ar LB FF sp scr _ M2 M3 EK WS FRB (fb + 464 + 320) 64 ltac:(apply (aobj_fb FF fb); [exact FOK| lia| lia])). intros i Hi. apply OUTO. lia.
- apply (PMKA.agsh_obj L ar LB FF sp scr _ M2 M3 EK WS FRB (fb + 464 + 280) 40 ltac:(apply (aobj_fb FF fb); [exact FOK| lia| lia])).
- destruct (BRB _ QIN). cbn [fst snd] in *. lia.
- destruct (BRB _ QIN). cbn [fst snd] in *. lia.
- apply (PMKA.agA_blk L ar LB FF sp scr _ M2 M3 EK WS BRB _ _ QIN). apply OUTB. exact QIN.
- destruct (BRB _ VIN). cbn [fst snd] in *. lia.
- destruct (BRB _ VIN). cbn [fst snd] in *. lia.
- apply (PMKA.agA_blk L ar LB FF sp scr _ M2 M3 EK WS BRB _ _ VIN). apply OUTB. exact VIN.
- intros c0 n0 p0 E.
assert (TIN : In (p0, c0) LB) by (apply INC; unfold PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own; rewrite E; cbn; right; right; left; reflexivity).
apply (PMKA.agA_blk L ar LB FF sp scr _ M2 M3 EK WS BRB _ _ TIN). apply OUTB. exact TIN.
- exact MG.
- replace (fb + 464 + 288) with (fb + 464 + 24 + 264) by lia. exact C1.
- replace (fb + 464 + 296) with (fb + 464 + 24 + 272) by lia. exact C2.
- replace (fb + 464 + 304) with (fb + 464 + 24 + 280) by lia. exact C3.
- replace (fb + 464 + 312) with (fb + 464 + 24 + 288) by lia. exact C4.
- exact Q1. - exact Q2. - exact Q3.
Qed.
Lemma src_piece_iss : ltac2:(TCodec.tc2 tcn__PmASrcKit "RC'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051&QI'RH'RF&QHvHr=r<r;r:r9r8r6%9887654321&RN%1293&SB&RG%116r?%43Q021&S>vJvSOr@r5r4(6(<&SC&S1&R6%221E+X0%5221+Q8%84QAQA21(:%11QB%<3QC31%C9BA@E?>1Q0O&R;&S?&RK&RO%12>Q3r7%675@4Q82Q41%42AQ7%877B6Q:1Q7Q6p031p0;1p0Q01p0Q61p0Q91pYNR41pZ2R51pZ0QF1pZDQH1pX>R81pWJQK1pR@QM1pR>QN1p2R:1pX6R81pQJR:1pQ@R;1pQHR>1").
Proof. intros LB FF LK cr Aw M2 M3 V fb str sm sp scr.
intros HH FOK INC EK IA.
unfold PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in *. cbn [pa_off_p pa_off_is PMA.AD ADDR_A] in *.
pose proof FOK as ((rs & Hfb) & F1024).
pose proof (frb_of _ _ _ _ _ _ _ HH) as FRB. pose proof (brb_of _ _ _ _ _ _ _ HH) as BRB.
assert (AOS : PMSPA.aobjA FF (fb + 464 + 24) 296) by (apply (aobj_fb FF fb); [exact FOK| lia| lia]).
assert (WS : PMKA.wapp [(fb + 464 + 24 + 256, 40)]).
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & _).
destruct (WF _ Hfb) as (Y1 & Y2 & _). unfold ff_addr, ff_class, ff_bytes in Y1, Y2. cbn in Y1, Y2. unfold app_mem, FS_BYTES in FSAPP, Y2.
apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; destruct FSAPP as (F0 & [F1|F1] & F2); [left; lia| right; lia]| apply PMKA.wapp_nil]. }
apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp scr _ M2 M3 EK WS FRB BRB (fb + 96) str sm ltac:(apply (aobj_fb FF fb); [exact FOK| lia| lia]) INC); [| |exact IA].
- intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
- intros c0 n0 p0 E i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. subst str.
assert (TIN : In (p0, c0) LB) by (apply INC; cbn; left; reflexivity).
destruct (blk_obj_apart _ _ _ _ _ _ _ p0 c0 _ 296 HH TIN AOS) as [X|X]; lia.
Qed.
Lemma ret_exit : ltac2:(TCodec.tc2 tcn__PmASrcKit "TG'S6&Q3y5'U8yR0%211%5241';y8%611%311p061'O&S8'9'='F%2211%411&QF%611&Q;yQ0%D11&QHvHr8r7r6r5r4r;&QJr:%211%;8:9876541&S;%1286'A%Q01@&M&S?&U7%12Q7>%4231(3r3%22H1%:3941'5&N%11E(7%?3421'Q2%Q821Q7%QA11&Q0%11M(<(Q1(U6z(?%33QN21+1%53R013y<%73165%93531+4%<4AQG21%K2A1%Q33A?1&S7rA&SIu1%211%Q52R=1%6251%Q72R=QF%Q<3R=21'@&SE%12GQK&SF&SJ+2+Q?%3221%52R11%9271&SGr9%2217%QJ3R@1Q2&QGrCr1%3221r>r2%R3221rBr@r?rF%R<1QN%RE8RD;5Q24321'S9&R2vS@%211&R4rIrHrG%4532A1RHrE%:4R?721p0<1p0C1p0G1pY6S@1r<rD%=5D821M%B4RG?1Hp051p0Q21p0Q71p0QB1p0QL1p0RA1p0RG1p0S31p0S61pWLSC1pYHSK1pYDSL1p2SK1pX6SI1pQJSK1pQ@SL1pQHSO1pQDT51pY4T71pR:T91pRDT?1pXBTF1").
Proof. intros fx R M model K LB FF LK cr Aw pc r W.
intros HH AM HF HE HD Rr Hr1 Hr2 KONT.
apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK cr Aw M model fx fx R pc R r (mrestrict (ahid Aw model) M) K HH AM
(PMK.ret_to RSEGS fx R _ pc W r HF HE HD Rr Hr1 Hr2) (fun _ X => X) (fun _ _ => eq_refl)).
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
assert (E : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1. apply KONT; assumption.
Qed.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Lemma img_shz_vis : ltac2:(TCodec.tc2 tcn__PmASrcKit "RN'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051'O&QHvHr9r8r7r6r5r4&QJr3%211%;8:9876541&SE+RPP0%2215&SC&SH+8%2219%42<1+VbTP0%9221'A&SG%12B7z%43Q921&SF%123F'D%>2=I%@2K1+T\X0%E221'@+T^W0%H21Q0+QUc]0%J271%5231+QUcb0%M21Q5+QVlZ0%O2<1%:231+QVmb0%Q221Q:%B231%C291%D2@1&R5&Q:&Q>r;%221QDr:%5221&SD%12QGQ9+QoooPP0%Q=221%;351QIp0=1p0Q31p0Q61p0Q<1p0QD1p0QH1pXDRC1pWNRD1pY4R71pR:R91p2RE1pX6RC1pQJRE1pQ@RF1pQHRI1").
Proof. intros LB FF LK cr Aw M model a g.
intros HH H1 H2 H8 Hg HP.
assert (AP : Forall (fun r => a + 8 * g <= fst r \/ snd r <= a) (icl_poison IL)).
{ rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
destruct (aic_img_shadow _ _ _ _ _ ICok LB FF LK cr Aw M _ HH a (8 * g) ltac:(rewrite (L5A.aly_img_lo L C LYa); lia)
ltac:(rewrite (L5A.aly_img_hi L C LYa); lia) ltac:(lia) AP) as (ZB & ALW).
assert (INS : forall j, 0 <= j < g -> in_shadow_of a (8 * g) (a / 8 + 2147450880 + j)).
{ intros j Hj. assert (SJ : a / 8 + 2147450880 + j = S (a + 8 * j)).
{ unfold S, SB. replace (a + 8 * j) with (j * 8 + a) by lia. rewrite Z.div_add_l by lia. lia. }
unfold in_shadow_of. rewrite SJ. unfold S. split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia. }
apply (proj2 (L5A.zeros_at_vis _ M _ g (L5A.avis_of_shadow_allowed Aw model a (8 * g) _ g ALW INS))).
intros j Hj. pose proof (ZB _ (INS j Hj)) as B. unfold byte_at in B. exact B.
Qed.
Lemma blk_apart : ltac2:(TCodec.tc2 tcn__PmASrcKit "R0'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051&QI&QHvHr;r:r9r8r7r6r5%9887654321&SA(<r4%24LL51r<%53M21r3%64Q0Q051r=%93Q121&C'A%13Q5@>%311'D&SE&SC%12FE%321E%32FE%521I%7231p091p0>1p0C1p0J1pY2QC1p6QD1pY0QE1p4QF1pWJQ91pR:Q;1p2QG1pX6QE1pQJQG1pQ@QH1pQHQK1").
Proof. intros LB FF LK cr Aw M V B1 m1 B2 m2.
intros HH H1 H2 NE. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
destruct (WB _ H1) as (_ & _ & _ & _ & AP & _). cbn [fst snd] in AP.
apply (L5C.blocks_apart_in B1 m1 (lb_remove B1 LB) B2 m2 AP). apply L5C.in_lb_remove_neq; [exact H2| intros E; apply NE; symmetry; exact E].
Qed.
Lemma lb_nodup : ltac2:(TCodec.tc2 tcn__PmASrcKit "Q:'9'='F%2211%411&QF%611&Q;'U8yR0%211';y8%511%311p051&QI&QHvHr7r6r5r4r3r2r1%9887654321'U3&E&8%12LLr8%44MN21%62O1p081pWJC1pR:E1p2Q11pX6O1pQJQ11pQ@Q21pQHQ51").
Proof. intros LB FF LK cr Aw M V.
intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _). exact ND.
Qed.
End WithHeap.
End PMASK.
