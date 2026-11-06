(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0
L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb
PmModelFactsA PmStepAB0 PmStep.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBSrcRead1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModelFactsA.PMFA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1bool"; "1false"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0FF"; "0HI"]; ["0KS"; "0L0"; "0LB"; "0LK"; "4Model"; "0M"; "0M'"; "5credit"; "5in_block"; "6FS_BYTES"; "6S"; "6ahid"; "6ar_fs"; "6fframe"; "6in_fframe"; "6ri_inv"]; ["6vml_of"; "7defined"; "7u64_at"; "8ADDR_B"; "9CHUNK"; "9SRC"; "9VLong"; "9p_b"; "9p_k"; "9p_src"; "9p_tb"; "9parser_at"; "9pst"; "9sr_qc"; "9vstr"; ":agA"]; [":agsh"; ";accA"; ";annA"; ";aobjA"; ";with_src"; "<loaded_segments"; "=eqb"; ">In"; ">existsb"; ">forallb"; "?add"; "?le"; "?lt"; "?mul"; "?pow"; "0a"]; ["0ar"; "0c"; "0cr"; "0de'"; "0k"; "0ks"; "0m"; "0model"; "0n"; "0n1"; "0n2"; "0o"; "0ois"; "0op"; "0p"; "0q"]; ["0rem'"; "0s"; "@Z_to_bv"; "@bv"]]).
Local Ltac lia := L5FastLia.plia.
Module PMBSR1.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBSrcRead1 "U?'RCyR0%211'5y8%511%311p051'='Q<&Q;&QE&Q3&QA&QBr7r5r4r3%9887654321&QKzr6%3221&QJ+\0%22;1&QN+2+R0%3221%;251&Q?r:r9r8+XH%544321r;+Z0%@261+A%:44921r<+[8%E2<1+H%?44921&Q@r=%J2<>+S8%443921&Q1%135;M':'Q>&Q:r>%211(Q6r2r1%33Q=21%93851'9rCrBrA+Z@%Q>221%Q74541I%C35;QG%I476<QH%9221%:241p0<1pTNR51pTBR61pT4R71r?&Q=&Q9%11Q8%311&Q4%Q13621r@%61Q7%811%Q:4F315&Q7%11Q2%R92R81%31>&QM+Q0&Q8%11B%R82R71%5241%R=271%RB21R8rD%=1A%81B%R?2R>1%<2;1%R<45Q:41&Q2+Y0%RG2Q=1%N1Q<%Q011%54S7;31rE+Y8%RM2>1%94S;31Q1rF+Y@%S1261%=4S?31QGrG+YH%S5261%A4SC31QK%Q=1<%Q?11%S=21J%S>2S=K%S;2<@%QB19%QD11%S>21QA%SC241rKrJrI&QDrH(Q5%QL12%QN11%331EI%6251%T88T7T6T5T4:981p0<1p0B1p0D1p0H1p0M1p0Q21p0Q71p0Q>1p0QE1p0QO1p0R31p0R81p0R@1p0S:1p0S=1p0SC1p0SI1p0SO1p0T61p0T?1p0TD1pU2U01pT8U11pU4U11pTJU31pTLU41pQ>U61pQ<U71")) (only parsing).
Variables (M M' : word -> option byte).
Variable op : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable de' : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable rem' : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Lemma parser_src_tbA : ltac:(sec_stmt2 constr:(SECT) 7%nat 0%nat).
Proof.
intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho'
[AG1 SH1] [AG2 SH2] [AG3 SH3] SH4 DEF TBL DCQ SHQ Hb Hb' AGB C1 C2 C3 C4 Q1 Q2 Q3.
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & CC & C240).
unfold PMSPA.with_src, PM.parser_at, PM.src_fields_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.sr_qc PM.sr_de PM.sr_rem] in *.
assert (U64 : forall a v, op <= a -> a + 8 <= op + 280 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
assert (U32 : forall a v, op <= a -> a + 4 <= op + 280 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
assert (U8 : forall a v, op <= a -> a + 1 <= op + 280 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v).
{ intros a v Ha Hb0 X. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG1; lia| lia| lia| exact X]. }
split; [apply U64; [lia|lia|exact H0]|].
split; [exact DEF|].
split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH1; lia| exact C24]|].
split; [apply U8; [lia|lia|exact H8]|]. split; [apply U8; [lia|lia|exact H9]|]. split; [apply U32; [lia|lia|exact H12]|].
split; [apply U8; [lia|lia|exact H16]|]. split; [apply U32; [lia|lia|exact H20]|].
split; [apply (PMFA.nullis_at_agreeA RSEGS PMB.AD M M' (op + 32)); [lia|lia| split; [intros i Hi; apply AG1; lia| intros x Hx; apply SH1; lia]| exact NI]|].
split.
{ split; [apply U64; [lia|lia|exact F1]|]. split; [apply U64; [lia|lia|exact F2]|].
split; [intros i Hi; replace (op + 24 + 256 + i) with (op + (280 + i)) by lia; apply DEF; lia|].
split; [replace (op + 24 + 264) with (op + 288) by lia; exact C1|]. split; [replace (op + 24 + 272) with (op + 296) by lia; exact C2|].
split; [replace (op + 24 + 280) with (op + 304) by lia; exact C3|]. split; [replace (op + 24 + 288) with (op + 312) by lia; exact C4|].
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact G4|].
split; [exact DCQ|].
split; [apply (PMFA.accA_agree M M' _ _ SHQ CC)|].
apply (PMFA.accA_agree M M' (op + 24 + 240) 56); [intros x Hx; destruct (Z_lt_le_dec x (op + 280)) as [X|X]; [apply SH1; lia| apply SH4; lia]| exact C240]. }
split; [apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact H320]|].
split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact H328]|].
split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; destruct (Z_lt_le_dec x (op + 337)) as [X|X]; [apply SH2; lia| apply SH4; lia]| exact C320]|].
split.
{ destruct TB as (TD & TC & TH). split; [intros i Hi; replace (op + 336 + i) with (op + (336 + i)) by lia; apply DEF; lia|].
split; [apply (PMFA.accA_agree M M' (op + 336) 24); [intros x Hx; apply SH4; lia| exact TC]|].
destruct (PM.p_tb s) as [n|c n p] eqn:ET.
- destruct TH as (Hn & B0). split; [exact Hn|]. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG2; lia| lia| lia| exact B0].
- destruct TH as (W0 & W8 & W16 & Hn & Hc & He & DB & CB). destruct (TBL c n p eq_refl) as ([AGT _] & DT & SHT).
split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AGT; lia| lia| lia| exact W0]|].
split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AGT; lia| lia| lia| exact W8]|].
split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AGT; lia| lia| lia| exact W16]|].
split; [exact Hn|]. split; [exact Hc|]. split; [exact He|]. split; [exact DT|].
apply (PMFA.accA_agree M M' p c SHT CB). }
split; [apply (PMFA.vec_at_agreeA RSEGS M M' (op + 360)); [lia|lia|lia|lia| intros i Hi; apply AG3; lia| exact AGB| exact VEC]|].
split; [exact B1|]. split; [exact B2|]. exact B3.
Qed.
End S.
Lemma aobjA_client {BS ST} L ar LB FF sp scr o n a : PMSPA.aobjA FF o n -> o <= a < o + n -> aclient_g BS ST L ar LB FF sp scr a.
Proof.
intros (f & Hf & X1 & X2) Ha. unfold aclient_g. do 3 right. left. exists f. split; [exact Hf|]. split; [lia| intros X; lia].
Qed.
Lemma in_fframe_of_aobjA : ltac2:(TCodec.tc2 tcn__PmBSrcRead1 "J'3&M%211'=&QCr4r3r2%43321'9&QK%1264&QL&QJ%1298%3281%7251&Nr6%221=p041p0=1pT0C1pTBD1pTHE1pNG1").
Proof. intros FF o n a. intros (f & Hf & X1 & X2) Ha. exists f. split; [exact Hf|]. split; [lia| intros X; lia]. Qed.
Lemma in_block_of : ltac2:(TCodec.tc2 tcn__PmBSrcRead1 "M'3'7'=%2211%411&QG(6r3r2%347721r4%63821'9&QK%1246&QL&QJ%127:%32:1%7251&Hr6%221?p041p0=1pT0G1pT>H1pU0I1pQ4H1").
Proof. intros L0 q m a. intros Hq Ha. exists (q, m). split; [exact Hq| cbn [fst snd]; exact Ha]. Qed.
Lemma cl_of_bf {BS ST} L ar LB FF sp scr a : in_block LB a \/ in_fframe FF a -> aclient_g BS ST L ar LB FF sp scr a.
Proof. intros [X|X]; unfold aclient_g; [left; exact X| do 3 right; left; exact X]. Qed.
Lemma sub_in : ltac2:(TCodec.tc2 tcn__PmBSrcRead1 "J'3'4%211':'1&QI&QH&QFr1%211r3%53:21qT:;1%83<15(8%<3;21&QG%13@97r2r5%43C21p041pT:E1p081pT<F1pQ2G1").
Proof. intros KS ks. intros H k Hk. apply L5K.In_of_mem. rewrite forallb_forall in H. apply H. exact Hk. Qed.
Lemma defined_app : ltac2:(TCodec.tc2 tcn__PmBSrcRead1 "O'RCyR0%211'5y8%511%311p051'=&QKzr2%3221&Q1r5r4r3%43321r6&QJ%1265%83315r7%:3153p031p081p0>1pTFC1pTDD1pT0E1pQ<G1").
Proof. intros M a n1 n2.
intros H0 D1 D2 i Hi. destruct (Z_lt_le_dec i n1) as [X|X]; [apply D1; lia|].
replace (a + i) with (a + n1 + (i - n1)) by lia. apply D2. lia.
Qed.
Section VisK.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmBSrcRead1 "RO'3'7'=%2211%411&M%611&G'RCyR0%211'5y8%511%311p051'D&Ov?r9r8r7r6r5r4&Q0r3%211%;8:9876541'<':r2z%33O21'9&QK&LvR0%211%421=&QJ%12?:&I%3251%9231%;261';&QG(6r1%24Q@Q@C1r<%53QA21%B2FN%>2ON%?2H6%E221%G241%H261qT>QI1%>2QJ1qU0QK1%@2QL1%Q22B1%Q32O1%N2Q:@&QL%12B=%Q2231'1&K&RB%12QOQ9%33QFQD1(2%Q=3621&J%11Q>%72R51%93QLQJ1%QB3;16%Q?261p0>1pT0RA1p0D1p0QI1pTBRD1pTNRE1pT@R81pQ<R:1p2RF1pT6RD1pQ8RF1pNRG1pQ6RJ1")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Lemma vis_scan : ltac:(sec_stmt2 constr:(SECT) 9%nat 0%nat).
Proof.
intros HH LOC a Ha.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr A M model HH) as VP. cbv zeta in VP.
destruct VP as (_ & _ & _ & VFS & VB & VBS & VFSS & _).
destruct LOC as [E|[(X1 & X2)|(q & m & Hq & X1 & X2)]].
- exfalso. lia.
- split.
+ pose proof (VFS a 1 ltac:(lia) ltac:(lia) 0 ltac:(lia)) as V. rewrite Z.add_0_r in V. exact V.
+ assert (IS : forall i, 0 <= i < 1 -> in_shadow_of (ar_fs ar) FS_BYTES (S a + i)).
{ intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r. unfold in_shadow_of. split; apply PMKB.S_mono; lia. }
pose proof (VFSS (S a) 1 IS 0 ltac:(lia)) as V. rewrite Z.add_0_r in V. exact V.
- split.
+ pose proof (VB q m a 1 Hq ltac:(lia) ltac:(lia) 0 ltac:(lia)) as V. rewrite Z.add_0_r in V. exact V.
+ assert (IS : forall i, 0 <= i < 1 -> in_shadow_of q m (S a + i)).
{ intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r. unfold in_shadow_of. split; apply PMKB.S_mono; lia. }
pose proof (VBS q m (S a) 1 Hq IS 0 ltac:(lia)) as V. rewrite Z.add_0_r in V. exact V.
Qed.
End S.
End VisK.
End PMBSR1.
