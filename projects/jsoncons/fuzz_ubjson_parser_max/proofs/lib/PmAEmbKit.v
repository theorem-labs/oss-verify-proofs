(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA
L5Defs L5Core L5CoreKit L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PmModel PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa
PmModelFactsA PmStep PmStepA.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAEmbKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsA.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAEmbKit.PMAEK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0B"; "1None"; "1Some"; "1app"; "1cons"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2not"; "2or"; "3lt"]; ["4Z"; "0FF"; "0HI"; "0L"; "0LB"; "0LBX"; "0LBz"; "0LK"; "5Segment"; "6Model"; "0M"; "0M'"; "7credit"; "8S"; "8aclient"; "8ahid"]; ["8ar_sptop"; "8ff_addr"; "8ff_bytes"; "8ff_class"; "8fframe"; "8in_shadow_of"; "8ri_inv"; "8vml"; "8vml_of"; "9ann_shadow"; ":defined"; ";avis"; "<argp"; "=pstate"; "=pstate_at"; ">aobjA"]; ["?rdn"; "@astk"; "AIn"; "Anth_error"; "Badd"; "Bdiv"; "Ble"; "Blt"; "Bmodulo"; "Bof_nat"; "Bpow"; "Bsub"; "0V"; "0a"; "0ar"; "0b"]; ["0bs"; "0c"; "0cr"; "0d"; "0f"; "0i"; "0j"; "0m"; "0model"; "0n"; "0o"; "0p"; "0q"; "0s"; "0scr"; "0scr'"]; ["0scz"; "0segs"; "0sp"; "0sp'"; "0spz"; "CZ_to_bv"; "Cbv"; "0u"; "0v"; "0x"]]).
Module PMAEK.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition argp (top : Z) (FF : list fframe) (sp v p n : Z) : Prop :=
(PMSPA.aobjA FF p n \/ (sp <= p /\ p + n <= top)) /\ (p + n <= v \/ v + 24 <= p).
Section Kit.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmAEmbKit "S<'6':'@%2211%411&Q4%611&L'RFyR0%211'8y8%511%311p051&Q7&Q6vBr9r8r7r6r5r4r3%9887654321&QB(9r2%24LL51r:%53M21';&QF+TP0%221<&QGz%221>&QD%12A@&QK&Q0vQN%211+XPPP0%5221%>271&QJ+2+Q?%3221%C2<1'<&QH+@%22Q11%43QH1D'>+RPP0%K2D1+VbTP0%M21Q7%5231+QoonlP0+`PPPPPTP0%K221%Q221Q<%Q32L4%;221&Q:%13QBQ@Q?r1r;%Q@3R621%Q42QFQE&Q1%11QA%Q=231&Q2&Q3%11QE%311%Q<261%QC21QO%K271p0<1pT:RC1%QH2A1%QI2D1%QJ2K1%QK2Q21%QL2Q81%QM2Q>1%QN2QH1%QO2QL1p0R11p0R81pT@S11pTJS21pSJRE1pQFRG1p2S31pT6S11pQ@S31pQ4S41pQ:S71")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable Aw : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable V : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable q : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable m : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Lemma blk_facts : ltac:(sec_stmt2 constr:(SECT) 9%nat 0%nat).
Proof.
intros HH Hin. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
destruct (WB (q, m) Hin) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & QD & _ & _ & _ & QF & _). cbn [fst snd] in *.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Q1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Q2|]. split; [lia|]. split; [lia|]. split; [exact QD|].
intros f Hf. apply QF. apply in_or_app. left. exact Hf.
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmAEmbKit "SO'6':'@%2211%411&Q4%611&L'RFyR0%211'8y8%511%311p051&Q7&Q6vBr<r;r:r9r8r7r6%9887654321&QAvQNr5%342751&QFz%2218&Q<&Q0%118r>r4%5632@>:1';&QG%12:=+8%=2?1%5231+VbTP0%@21G&QD%12IH&QJ+2+Q?%3221%G251'>+QoonlP0+`PPPPPTP0%:221%L21Q3%M2;4%6221%O2=Q7+H%@2Q91%Q221Q9%;241%Q42Q>Q;&QK+XPPP0%22Q21%Q82F1%A251&QB(9r2r1%34R;R;21rC%63R<21%Q02QKQJr3%QC221%Q3228%QE21QO%N231p071pT@RE1pTJRF1%QJ2QI8%QA29R4%QC221%QM2;QG&NvCrFrE%QA2R>R4%574R632QLA1p071p091pU0S31pU8S41pT<S51%R02@1%R12Q11%R22Q81%R32Q>1%R42QF1%R52QN1p0R11p0R81p0R?1p0RC1p0RH1pTDSA1pTHSB1pUBSC1pTNSD1pU6SE1pSJS81pQFS:1p2SF1pT6SD1pQ@SF1pQ4SG1pQ:SJ1")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable Aw : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable V : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable scr : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SECT) 9%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SECT) 10%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SECT) 11%nat 0%nat).
Lemma arg_facts : ltac:(sec_stmt2 constr:(SECT) 12%nat 0%nat).
Proof.
intros HH ASTK SC0 (PL & PV) Hn. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL, FSIMG.
assert (FS0 : 0x691000 <= ar_fs ar) by (destruct FSAPP as (FA0 & _ & _); destruct FSIMG as [FI|FI]; lia).
destruct PL as [(f & Hf & X1 & X2)|(X1 & X2)].
- pose proof (WF f Hf) as (F1 & F2 & _ & F4 & _). unfold FS_BYTES in F1, F2.
assert (HB : 0 < ff_bytes (ff_class f) <= 1024).
{ destruct F4 as [E|[E|[E|[E|[E|[]]]]]]; rewrite <- E;
[change (ff_bytes 0) with 64 | change (ff_bytes 1) with 128 | change (ff_bytes 2) with 256 | change (ff_bytes 3) with 512 | change (ff_bytes 4) with 1024]; lia. }
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact PV|]. split; [right; lia|].
split. { intros q m Hin. destruct (WB (q, m) Hin) as (_ & _ & _ & _ & _ & QF & _). cbn [fst snd] in QF.
destruct (QF f ltac:(apply in_or_app; left; exact Hf)) as [Y|Y]; lia. }
intros i sp' scr' Hi Hs. unfold aclient, aclient_g. right; right; right; left. exists f. split; [exact Hf| lia].
- split; [lia|]. split; [lia|]. split; [lia|]. split; [exact PV|]. split; [left; lia|].
split. { intros q m Hin. destruct (WB (q, m) Hin) as ((_ & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q4. lia. }
intros i sp' scr' Hi Hs. apply L5SAR.stack_client; lia.
Qed.
End S.
Lemma ann_agree : ltac2:(TCodec.tc2 tcn__PmAEmbKit "QE'RFyR0%211'8y8%511%311p051'@';&QFzr1%3221&QG&QEr2+8%3221%5271%;271'<r6&RE&QD&Mr5%211%421<%62L1%811r7%113%<3K31p0>1pT>K1r3%K2J1r4%M213&Q9r8%241D@4%342<EAp021p061p091p0<1pT4Q81pU@Q91pT0Q:1pQHQ<1pQFQ=1").
Proof. intros M M' b u c.
intros AG U0 U1 (Z0 & P). split.
- intros j Hj. unfold byte_at. rewrite AG; [apply Z0; exact Hj|]. split; [lia|]. apply (Z.lt_le_trans _ (u / 8)); [lia| apply Z.div_le_mono; lia].
- intros j Hj. unfold byte_at. rewrite AG; [apply P; exact Hj| lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma sh_apart : ltac2:(TCodec.tc2 tcn__PmAEmbKit "Q8'@'<&QHr3+8%3221z%63721&QGr4%2241&QFr6%2271r5%4291'>r8%:261&QDr7%2241%;21:%7251&=&Q5r9&M%118%433<1%611p081p0A1p0D1p0H1p0L1p0M1pUDQ51pT4Q61pT0Q71").
Proof. intros b c x. unfold in_shadow_of, S, SB. intros. Lia.lia. Qed.
Lemma sh_in : ltac2:(TCodec.tc2 tcn__PmAEmbKit "Q2'@'<&QHr3+8%3221z%63721&QFr5%2241';r4%5271&QG&QE%127<%3251%7251&Q5r7r6&QD&M%114%321@%73651p091p0B1p0F1p0G1pT>O1pT4Q01pT0Q11").
Proof. intros b c j. unfold in_shadow_of, S, SB. intros. Lia.lia. Qed.
Lemma sh_idx : ltac2:(TCodec.tc2 tcn__PmAEmbKit "I'@'<&QHr2+8%3221z%63721&QD&QEr4r3%4221%4219+QoooPP0%7221&M%117%927>%;221%C3D51p0>1p0?1pT8G1pT0H1").
Proof. intros b d. unfold S, SB. intros. Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma in_shadow_range : ltac2:(TCodec.tc2 tcn__PmAEmbKit "O'@&QFzr3%3221&QDr4%2214&QJ+2+Q?%3221%;251&Q5r5%2319<';+QoooPP0%A21<&QG+Q<%=2<1%A251%42A1%8261p0:1p0>1p0G1pSLL1pT4M1pT0N1").
Proof. intros b c a. unfold in_shadow_of, S, SB. intros. Lia.lia. Qed.
Lemma frame_sh_client : ltac2:(TCodec.tc2 tcn__PmAEmbKit "Q6'6&Q4%211'@':%1222%611&Q?r7r6r5%43321';&QF%1264&QG&QD%1298%3281%7251&NvCvQNr9r4r3&M%11B%8776B5431p0:1p0C1pU2L1pU:M1pQ>K1pUDO1pTDQ01pTFQ11pQ4Q31").
Proof. intros FF o n x LBz spz scz.
intros (f & Hf & X1 & X2) Hx. unfold aclient, aclient_g. right; right; right; right; right; left. exists f. split; [exact Hf|].
unfold in_shadow_of, S, SB. Lia.lia.
Qed.
Lemma stack_sh_client : ltac2:(TCodec.tc2 tcn__PmAEmbKit "Q7'6&Q4%211'@':%1222%611';&QF&QK&Q0vQN%211+XPPP0%5221r4%8221&QG&QJ+2+Q?%3221%5271%@271&NvCr6r3r2&Mr5%211%877EA6541p0:1pU2O1pU:Q01pQ>N1pUDQ21pQ4Q41").
Proof. intros FF x LBz spz scz. intros Hx. unfold aclient, aclient_g. right; right; right; right; left. unfold in_shadow_of, S, SB. Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma arg_client : ltac2:(TCodec.tc2 tcn__PmAEmbKit "R7'6':'@%2211%411&Q4%611&L'RFyR0%211'8y8%511%311p051&Q7&Q6vBr<r;r:r9r8r7r6%9887654321&QAvQNr5%342751&QFz%2218&Q<&Q0%118r>r4%5632@>:1&QG%129<&NvCr3rCr2r1&M%11L%877F65431pU2QA1pU:QB1pQ>QA1p0=1p0@1p0G1p0K1p0Q01pTDQI1pTHQJ1pUBQK1pTNQL1pU6QM1pSJQ@1pQFQB1p2QN1pT6QL1pQ@QN1pQ4QO1pQ:R21").
Proof. intros LB FF LK cr Aw M V sp scr v p n.
intros HH ASTK SC0 [[AO|[X1 X2]] _] Hn LBz spz scz.
- apply (frame_sh_client FF p n p); [exact AO|]. destruct AO as (f & _ & Y1 & Y2). pose proof (proj1 ASTK) as _. Lia.lia.
- pose proof ASTK as (A16 & SLO & SHI & SPT & _). apply stack_sh_client. Lia.lia.
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmAEmbKit "R8'6':'@%2211%411&Q4%611&L'RFyR0%211'8y8%511%311p051'I&Q6vBr<r;r:r9r8r7&Q8r6%211%;8:9876541&QAvQNr5%342961&QFz%2219&Q<&Q0%118r>r4%5632B?:1&QG%129<';&Q;&Or=%221L%431IG&M%11K+1%83521%:251p0<1p0?1p0F1p0J1p0O1pTDQJ1pTHQK1pUBQL1pTNQM1pU6QN1pTBQA1pQFQC1p2QO1pT6QM1pQ@QO1pQ4R01pQ:R31")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable Aw : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable sp : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable scr : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Variable v : ltac:(sec_ty2 constr:(SECT) 9%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SECT) 10%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SECT) 11%nat 0%nat).
Lemma arg_vis : ltac:(sec_stmt2 constr:(SECT) 12%nat 0%nat).
Proof.
intros HH ASTK SC0 [PL _] Hn. pose proof ASTK as (A16 & SLO & SHI & SPT & _).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
destruct PL as [AO|[X1 X2]].
- destruct AO as (f & Hf & Y1 & Y2). pose proof (WF f Hf) as (F1 & F2 & _).
split; [apply VFS; Lia.lia|]. apply VFSSH. intros i Hi. replace i with 0 by Lia.lia. rewrite Z.add_0_r.
unfold in_shadow_of, S, SB. unfold FS_BYTES in *. clear - F1 F2 Y1 Y2 Hn.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
- split; [apply VIS; Lia.lia|]. apply VSTSH. intros i Hi. replace i with 0 by Lia.lia. rewrite Z.add_0_r.
unfold in_shadow_of, S, SB. clear - X1 X2 SLO SHI SPT Hn SC0. Lia.lia.
Qed.
End S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma own_facts : ltac2:(TCodec.tc2 tcn__PmAEmbKit "R?'@'6':%1233%311&Q4%511&L'RFyR0%211'8y8%511%311p051&Q7&Q6vB(5(9r9r8%34GG21r7%63F21r6r5r4r3r2r1%?8>7654321';&QB%?4Q3Q354r:%33Q221'>&QF&QDr=r<%3221%521?%52@?%7215%9231p0;1pT@QA1pTJQB1&4%13Q?NL%C3Q@F1r;%?2=1&Q1%11K%C231&Q2&Q3%11O%311%G261%I21F%K271p0=1pT:QN1%Q32B1p0Q51pSJQF1pQFQH1p2R41pT6R21pQ@R41pQ4R51pQ<R81pT4R=1pT0R>1").
Proof. intros b c LBX FF LK cr Aw M V.
intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
destruct (WB (b, c) ltac:(left; reflexivity)) as (_ & _ & _ & _ & BA & FA & _). cbn [fst snd lb_remove] in BA, FA. rewrite Z.eqb_refl in BA.
split; [intros q m Hin; destruct (BA (q, m) Hin) as [X|X]; cbn [fst snd] in X; lia| exact FA].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmAEmbKit "R1'@'6':%1233%311&Q4%511&L'RFyR0%211'8y8%511%311p051&Q7&Q6vB(5(9r9r8%34GG21r7%63F21r6r5r4r3r2r1%?8>7654321&NvCvQNr;r:%574321879&=';&QFr>%221?&QG&QDr=%2251%42D1%9261%;11p0=1pU2QD1pU:QE1pSLQF1p0G1pSJQ81pQFQ:1p2QF1pT6QD1pQ@QF1pQ4QG1pQ<QJ1pT4QO1pT0R01")) (only parsing).
Variable b : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable LBX : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable Aw : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable V : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Lemma own_notclient : ltac:(sec_stmt2 constr:(SECT) 9%nat 0%nat).
Proof.
intros HH a spz scz Hc Ha. pose proof (own_facts b c LBX FF LK cr Aw M V HH) as (BA & FA).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
destruct (WB (b, c) ltac:(left; reflexivity)) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in *.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Q1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- destruct Hc as ((q & m) & Hin & X). cbn [fst snd] in X. destruct (BA q m Hin); lia.
- lia.
- rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Hc. lia.
- destruct Hc as (f & Hf & X & _). destruct (FA f ltac:(apply in_or_app; left; exact Hf)); lia.
- unfold in_shadow_of, S, SB in Hc. lia.
- destruct Hc as (f & Hf & X). unfold in_shadow_of, S, SB in X. destruct (WF f Hf) as (F1 & F2 & _).
unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, F1, F2. lia.
- destruct Hc as ((q & m) & Hin & X). cbn [fst snd] in X. unfold in_shadow_of, S, SB in X.
destruct (proj1 (WB (q, m) ltac:(right; exact Hin))) as (Y0 & _ & _ & _ & _ & Y5). cbn [fst snd] in *. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y5. lia.
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmAEmbKit "R2'@'6':%1233%311&Q4%511&L'RFyR0%211'8y8%511%311p051&Q7&Q6vB(5(9r9r8%34GG21r7%63F21r6r5r4r3r2r1%?8>7654321'<&QH+8%22?1z%53Q621&NvCvQNr<r;%574321>=?&=&Q5r?r>%3321E%511p071pU2QD1pU:QE1pSLQF1p0A1p0H1pSJQ91pQFQ;1p2QG1pT6QE1pQ@QG1pQ4QH1pQ<QK1pT4R01pT0R11")) (only parsing).
Variable b : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable c : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable LBX : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable Aw : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SECT) 7%nat 0%nat).
Variable V : ltac:(sec_ty2 constr:(SECT) 8%nat 0%nat).
Lemma own_sh_notclient : ltac:(sec_stmt2 constr:(SECT) 9%nat 0%nat).
Proof.
intros HH C8 a spz scz Hc Ha. pose proof (own_facts b c LBX FF LK cr Aw M V HH) as (BA & FA).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
destruct (WB (b, c) ltac:(left; reflexivity)) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in *.
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
assert (SR : 2147450880 <= a < 2147450880 + 2 ^ 44) by (apply (in_shadow_range b c a); [lia| lia| exact Ha]).
unfold in_shadow_of, S, SB in Ha.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- destruct Hc as ((q & m) & Hin & X). cbn [fst snd] in X.
destruct (proj1 (WB (q, m) ltac:(right; exact Hin))) as (Y0 & _ & _ & _ & _ & Y5). cbn [fst snd] in *. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y5. clear - X Y5 SR. lia.
- clear - Hc SR CB2. lia.
- rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Hc. clear - Hc SR. lia.
- destruct Hc as (f & Hf & X & _). destruct (WF f Hf) as (F1 & F2 & _). unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, F1, F2. clear - X F1 F2 FSAPP SR. lia.
- unfold in_shadow_of, S, SB in Hc. clear - Hc Ha Q3 Q4 Q0 CB2. lia.
- destruct Hc as (f & Hf & X). unfold in_shadow_of, S, SB in X. destruct (WF f Hf) as (F1 & F2 & F3 & F4 & _).
destruct (FA f ltac:(apply in_or_app; left; exact Hf)) as [Y|Y].
+ assert (E8 : ff_addr f mod 8 = 0).
{ destruct F4 as [E|[E|[E|[E|[E|[]]]]]]; rewrite <- E in F3;
[change (ff_bytes 0) with 64 in F3 | change (ff_bytes 1) with 128 in F3 | change (ff_bytes 2) with 256 in F3 | change (ff_bytes 3) with 512 in F3 | change (ff_bytes 4) with 1024 in F3];
clear - F3; lia. }
clear - X Ha Y E8 C8 Q2 Q0. lia.
+ assert (E8 : ff_bytes (ff_class f) mod 8 = 0 /\ ff_addr f mod 8 = 0).
{ destruct F4 as [E|[E|[E|[E|[E|[]]]]]]; rewrite <- E in *;
[change (ff_bytes 0) with 64 in * | change (ff_bytes 1) with 128 in * | change (ff_bytes 2) with 256 in * | change (ff_bytes 3) with 512 in * | change (ff_bytes 4) with 1024 in *];
clear - F3; lia. }
clear - X Ha Y E8 C8 Q2 Q0. lia.
- destruct Hc as ((q & m) & Hin & X). cbn [fst snd] in X. unfold in_shadow_of, S, SB in X.
destruct (proj1 (WB (q, m) ltac:(right; exact Hin))) as (Y0 & _ & Y2 & _). cbn [fst snd] in *.
destruct (BA q m Hin) as [Z1|Z1]; clear - X Ha Z1 Y2 Q2 C8 Y0 Q0; lia.
Qed.
End S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma arg_fresh_apart : ltac2:(TCodec.tc2 tcn__PmAEmbKit "R@'RFyR0%211'8y8%511%311p051'6&Q4%211'@&QAvQNr:r7r6%544321&QFz%2215&Q<&Q0%11:r;r9r5%66432<;1&QBr1&4r=r<%33H21%63I51'>&QD%12FE&Q1r2%211%G241&Q2&Q3%115%311%:261%M21Q0%=271p0?1pT:Q91%?2Q3I&QK+XPPP0%22O1%Q5241&QGr8%22Q71%G2Q=Q2%Q:213%I24Q>%Q<21Q@%L231p061p0:1p0@1p0Q81p0Q@1p0QD1pT@QK1p4QL1pTDQM1pTHQN1pUBQO1pTNR01pU6R11pQ@R31pQ4R41pQFR81").
Proof. intros M FF LK sp scr v p n B m.
intros ASTK SC0 [[(f & Hf & X1 & X2)|(X1 & X2)] _] FA BC Hn.
- destruct (FA f ltac:(apply in_or_app; left; exact Hf)) as [Y|Y]; [right; lia| left; lia].
- pose proof ASTK as (A16 & SLO & _). right. lia.
Qed.
Lemma rdn_shift : ltac2:(TCodec.tc2 tcn__PmAEmbKit "QN'6'H%211'RFyR0%211'8y8%511%311p051'7'@';&QFzr1%3221&QG&QIr4%211%4261%:261&='<r7&RE&QDr2%22:1%42K1%611(2%11J%:3J31%<11r6r3%;21:%=2Q41%411%A3Q11:%N271p0E1pT<Q11%Q>1Q6%Q911&Q@r5%G2Q>E%34I21O%I2Q@>%54K@1Q1%M3731p0:1pT0Q<1pSLQ=1pTDQ?1pQHQA1pQFQB1pU4QK1").
Proof. intros segs M M'.
induction n as [|n IH]; intros a b HH; [reflexivity|].
cbn [rdn]. destruct (HH 0 ltac:(lia)) as (D0 & E0). replace (a + 0) with a in D0, E0 by lia. replace (b + 0) with b in E0 by lia. rewrite E0.
destruct (M (Z_to_bv 64 a)) as [x|] eqn:Ea; [|exfalso; apply D0; reflexivity].
rewrite !L5C.add1_lit. rewrite (IH (a + 1) (b + 1)); [reflexivity|].
intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. replace (b + 1 + i) with (b + (i + 1)) by lia. apply HH. lia.
Qed.
Lemma rdn_nth : ltac2:(TCodec.tc2 tcn__PmAEmbKit "QL'6'H%211'RFyR0%211'8y8%511%311p051'7'@%=15'<%912&Q@r5r4&REr2%22A1r3%746521(3r1%22=1%=3<41&?%124<&=r7&QD&QI%11>%32B1%A2Q01%611(2%11O%J3O31%;11r8r6%;1F%=221%K2Q:1%511&QC%13Q9Q0K%Q43Q931p0:1p0G1pT<Q:1p0K1pT2Q:1pSLQ<1pTDQ>1pQFQ@1pU4QI1").
Proof. intros segs M.
induction n as [|n IH]; intros a bs E i Hi D; [lia|].
cbn [rdn] in E. destruct (M (Z_to_bv 64 a)) as [x|] eqn:Ea.
- rewrite L5C.add1_lit in E. destruct (rdn segs M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate E].
injection E as <-. destruct i as [|i].
+ cbn. rewrite Z.add_0_r. exact Ea.
+ cbn [nth_error]. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest Er i); [lia|].
replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. exact D.
- destruct i as [|i]; [rewrite Z.add_0_r in D; exfalso; apply D; exact Ea|].
destruct (seg_rom segs (Z_to_bv 64 a)) as [y|]; [|discriminate E]. rewrite L5C.add1_lit in E.
destruct (rdn segs M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate E].
injection E as <-. cbn [nth_error]. replace (a + Z.of_nat (Datatypes.S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) rest Er i); [lia|].
replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. exact D.
Qed.
Lemma pstate_copy : ltac2:(TCodec.tc2 tcn__PmAEmbKit "QJ'6'H%211'RFyR0%211'8y8%511%311p051'@'Q=';&QFzr1%3221&QG+Q0%2241%8241&='<r7&RE&QDr5r2%3221%52J1%711(2%11I%;3I31%=11r6r4%<21:%>2Q31%411%B3Q01:%M271p0F1pT<Q11&Q>%14F:9Br8r3%442=<1p041p071pTLQ81pT0Q:1pSLQ;1pQHQ=1pQFQ>1pU4QG1").
Proof. intros segs M M' a b s.
intros HH (P0 & P8 & P16 & P24). unfold PM.pstate_at, L5.u32_at, L5.u64_at, L5.u8_at in *.
assert (SH : forall d (w : nat), 0 <= d -> d + Z.of_nat w <= 32 -> rdn segs M' (Z_to_bv 64 (b + d)) w = rdn segs M (Z_to_bv 64 (a + d)) w).
{ intros d w H1 H2. apply rdn_shift. intros i Hi. replace (a + d + i) with (a + (d + i)) by lia. replace (b + d + i) with (b + (d + i)) by lia. apply HH. lia. }
split; [rewrite <- (Z.add_0_r b), SH, Z.add_0_r by (cbn; lia); exact P0|].
split; [rewrite SH by (cbn; lia); exact P8|]. split; [rewrite SH by (cbn; lia); exact P16|]. rewrite SH by (cbn; lia); exact P24.
Qed.
End Kit.
End PMAEK.
