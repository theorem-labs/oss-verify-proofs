(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAa
PmModelFactsA PmStepA PmTxtKit2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmARsKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmTxtKit2.PMTK2."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["0Aw"; "1app"; "1list"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2or"; "3map"; "4Z"; "0FF"; "0HI"; "0LB"; "0LK"; "0LK'"]; ["5Model"; "0M"; "0M'"; "0MV"; "6mrestrict"; "7credit"; "8FS_BYTES"; "8ahid"; "8ar_fs"; "8ar_sptop"; "8ff_addr"; "8fframe"; "8ri_inv"; "8vml_of"; "9defined"; "9writable"]; [":avis"; ";zeros_at"; "<ADDR_A"; "=CHUNK"; "=p_b"; "=p_k"; "=p_src"; "=parser_at"; "=pst"; "=sr_qc"; "=vstr"; "=vstr_at"; ">agA"; ">agsh"; "?accA"; "?annA"]; ["?aobjA"; "?ffroomA"; "?frame_okA"; "?o_p"; "?o_tb"; "@with_tb"; "Aloaded_segments"; "BIn"; "Bincl"; "Cadd"; "Cdiv"; "Cle"; "Cmodulo"; "Cmul"; "Cpow"; "Csub"]; ["0a"; "0ar"; "0c"; "0cr"; "0fb"; "0h"; "0h'"; "0model"; "0n"; "0ois"; "0op"; "0p"; "0s"; "DNoDup"; "Ebv"; "0tb"]; ["0tg"]]).
Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMARSK.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmARsKit "SC'R>yR0%211'3y8%511%311p051':'Q8'Q:&Q7&QF&Q2&Q>&Q?r7r5r4r3%9887654321&QKzr6%3221&QI+\0%22;1&QN+2+R0%3221%;251&Q<r:r9r8+Z@%544321r;+[8%@261+H%:44921&Q=r<%E2<9%342815&Q9&Q6%11?%311%O2N1%41C%611&Q3%O221%Q421Jr?r>%;1E%=11%M44317&Q4%11C%Q<2Q;1r=%411&QM+Q0&Q5%115%Q<2Q;1%5241%QA271%QF21Q<rBrA%?1C%91D%QD2QC1%=2<1%QA46541&Q;%QK27Q?%25R9R791J&NrC%231<QNrD&QEr@%23?1Q2%RB8RAR@R?R>46A1p061p0:1p0>1p0F1p0Q11p0Q51p0Q;1p0QA1p0QG1p0QL1p0R21p0R91p0RB1p0RG1pU2S41pU0S31pTJS51pTDS71pTFS81pQ6S:1pQ4S;1")) (only parsing).
Variables (M M' : word -> option byte).
Variable op : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable tb : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable tg : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Lemma parser_tb_setA : ltac:(sec_stmt2 constr:(SECT) 7%nat 0%nat).
Proof.
intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
[AG1 SH1] [AG2 SH2] SH3 Hq Hq' AGQ Hb Hb' AGB TB' D'.
unfold PMTK2.with_tb, PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
assert (U64 : forall a v, op <= a -> a + 8 <= op + 336 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
assert (U32 : forall a v, op <= a -> a + 4 <= op + 336 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
assert (U8 : forall a v, op <= a -> a + 1 <= op + 336 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
split; [apply U64; [lia|lia|exact H0]|].
split; [exact D'|].
split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH1; lia| exact C24]|].
split; [apply U8; [lia|lia|exact H8]|]. split; [apply U8; [lia|lia|exact H9]|]. split; [apply U32; [lia|lia|exact H12]|].
split; [apply U8; [lia|lia|exact H16]|]. split; [apply U32; [lia|lia|exact H20]|].
split; [apply (PMFA.nullis_at_agreeA RSEGS PMA.AD M M' (op + 32)); [lia|lia| split; [intros i Hi; apply AG1; lia| intros x Hx; apply SH1; lia]| exact NI]|].
split; [apply (PMFA.src_fields_at_agreeA RSEGS M M' (op + 24) ois (ois + 16) (PM.p_src s)); [lia|lia|exact Hq|exact Hq'
| split; [intros i Hi; apply AG1; lia| intros x Hx; apply SH1; lia]| exact AGQ| exact SRC]|].
split; [apply U32; [lia|lia|exact H320]|].
split; [apply U64; [lia|lia|exact H328]|].
split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; destruct (Z_lt_le_dec x (op + 336)) as [X|X]; [apply SH1; lia|];
destruct (Z_lt_le_dec x (op + 360)) as [Y|Y]; [apply SH3; lia| apply SH2; lia]| exact C320]|].
split; [exact TB'|].
split; [apply (PMFA.vec_at_agreeA RSEGS M M' (op + 360)); [lia|lia|lia|lia| intros i Hi; apply AG2; lia| exact AGB| exact VEC]|].
split; [exact B1|]. split; [exact B2|]. exact B3.
Qed.
End S.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Lemma ffroom_incl : ltac2:(TCodec.tc2 tcn__PmARsKit "Q0':'2&K%211&QAr5r3r2%43321&QH%13834'R=&9&J&1%13=:9%44>@31%62A1&QKr7r8%3221%B323Ap021p071p0?1p0B1pQ0H1pNI1pHJ1pT>N1pT<O1").
Proof. intros h h' FF LK LK'.
intros FR I ND Hh k Hk. specialize (FR k Hk).
assert (CI : (ff_count k (FF ++ LK') <= ff_count k (FF ++ LK))%nat).
{ apply L5SAR.ff_count_incl.
- intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [X|X]; [left; exact X| right; apply I; exact X].
- apply (list_monad.list.NoDup_fmap_1 ff_addr). exact ND. }
lia.
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmARsKit "T6'2'5':%2211%411&K%611&E'R>yR0%211'3y8%511%311p051'@'Q8&Lv<r:r9r8r7r6r5&Mr4%211%;8:9876541&QB%12;4&Q7&QF&Q2&Q>&Q?&QC%124=r3%887654A2=1&QD%128B&D&G%12IG%321I'6&QK+VbTP0r2%3221+Soooooooo8%5231%7231'7&QL+8%2281z%53QJ21'8&QI+QoonlP0+`PPPPPTP0%3221%B21@+H%62B1%E216%9241%H2;1%I2B1&Q1r1&QJ%12JC+QoooPP0%@221+3%73621&O%14QA8Q0?&QO&IvR1%211+XPPP0%5221%Q92E1%Q:2QOQ8%M2QDQ9%N2R3I%Q=221&Q0r?r=%QE221%431R7QKp061p0:1pTBS31pT2S41&Q@r>%231QGQ6&H%11F%QL21QJ&F%Q@231%QO2Q;1%R1241%R2281%R32<1%R42J1%R52Q21%R62Q51%R72Q>1tQ8S8R91tU0SFR>1p0RA1p0RK1p0RN1pTJS;1pTDSK1pT:SL1pT@S?1pQ4SA1p2SM1pT8SK1pNSM1pHSN1pLT11")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable Aw : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable fb : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 9%nat 0%nat).
Lemma tb_vis : ltac:(sec_stmt2 constr:(SECT) 10%nat 0%nat).
Proof.
intros HH FOK PA tb MV. destruct FOK as ((rs & Hf) & F1024). cbn [pa_frame PMA.AD ADDR_A] in *.
assert (AO : PMSPA.aobjA FF tb 24).
{ exists (fb, 4, rs). split; [exact Hf|]. unfold tb, PMSPA.o_tb, PMSPA.o_p. cbn [ff_addr ff_class ff_bytes pa_off_p PMA.AD ADDR_A].
unfold ff_bytes. cbn. lia. }
assert (O8 : tb mod 8 = 0).
{ unfold tb, PMSPA.o_tb, PMSPA.o_p. cbn [pa_off_p PMA.AD ADDR_A]. pose proof (Z.div_mod fb 1024 ltac:(lia)) as Dm. rewrite F1024, Z.add_0_r in Dm.
rewrite Dm. replace (1024 * (fb / 1024) + 464 + 336) with ((128 * (fb / 1024) + 100) * 8) by lia. apply Z_mod_mult. }
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model tb 24 0 0 HH (PMKA.aobj_of_aobjA FF tb 24 AO O8) ltac:(lia) ltac:(reflexivity))
as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
assert (ACC : PMSPA.accA M tb 24).
{ pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB & _). destruct TB as (_ & TC & _). exact TC. }
split; [split; [lia| split; [exact O8| exact OBIG]]|].
split.
{ change 3 with (24 / 8). apply (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model tb 24 HH AO O8 ltac:(lia) ltac:(reflexivity) ACC). }
split.
{ apply (proj2 (L5A.writable_vis _ M tb 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]. }
split; [lia|]. split; [intros a n Ha Hn; eapply L5A.avis_sub; [exact OVIS| lia| lia]|]. split; [exact AO|].
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & _).
destruct (WF _ Hf) as (W1 & W2 & _). unfold ff_addr, ff_class in W1, W2. cbn in W1, W2. unfold ff_bytes in W2. change (64 * 2 ^ 4) with 1024 in W2.
unfold tb, PMSPA.o_tb, PMSPA.o_p. cbn [pa_off_p PMA.AD ADDR_A]. unfold FS_BYTES in *. split; lia.
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmARsKit "S>'2'5':%2211%411&K%611&E'R>yR0%211'3y8%511%311p051'@&Lv<r9r8r7r6r5r4&Mr3%211%;8:9876541&QG(4r2%24NN61r:%53O21&QK+J%221;&Q>%13B@?&D&G%12GE%321G'6+TP0%;21I&QI%12KJ&QN+2+Q?%3221%B251'7&QL+@%22Q41z%53QI21'8+QoonlP0+`PPPPPTP0%@221%M21Q;%N2A4%6221%G281%H2?1%I2G1&Q1r1&QJ+8%22QE1+QoooPP0%M221+1%83721&O&QF%241:QL4&Q0%Q:2QBQO%231QO7&QO&IvR1%211+XPPP0%5221%QH2Q;1%Q@281%QA2<1%QB2@1%QC2J1tQ8RAQE1p0QJ1p0QM1p0R11p0R81pT6S31pTHS41pT@RG1pQ4RI1p2S51pT8S31pNS51pHS61pLS91")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable Aw : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Lemma tbd_vis : ltac:(sec_stmt2 constr:(SECT) 9%nat 0%nat).
Proof.
intros HH Hin Hc CC MV.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
destruct (WB _ Hin) as ((B0 & B1 & B2 & B3 & B4 & B5) & _). cbn [fst snd] in B0, B1, B2, B3, B4, B5.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (_ & _ & _ & _ & VBLK & _).
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5.
assert (P8 : p mod 8 = 0) by (apply PMKA.mod16_8'; exact B2).
assert (VP : L5A.avis (ahid Aw model) p 1) by (apply (VBLK p c p 1 Hin); lia).
split; [split; [lia| split; [lia| split; [exact B2| destruct B5 as (_ & [X|X] & _); [right| left]; lia]]]|].
split.
{ change 1 with (8 / 8). apply (PMKA.blk_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model p c p 8 HH Hin ltac:(lia) ltac:(lia) P8 ltac:(lia) ltac:(reflexivity)).
intros x Hx. apply CC. lia. }
split.
{ apply (proj2 (L5A.writable_vis _ M p 1 VP ltac:(lia) ltac:(lia))).
destruct (WB _ Hin) as (_ & DEF & _). apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M p c p 1 DEF); lia| lia| lia]. }
split; [exact VP|]. lia.
Qed.
End S.
End WithHeap.
End PMARSK.
