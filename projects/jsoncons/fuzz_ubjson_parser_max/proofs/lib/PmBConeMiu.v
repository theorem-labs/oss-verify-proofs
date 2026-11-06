(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmSpecsBX PmModelFactsA PmStep PmStepAB0 PmStepB2 PmCertKitG PmBIss1 PmBEmbKit PmAEmbF PmBConeP2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan Require Import L5CoreBB0.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBConeMiu () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBEmbKit.PMBEK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsBX.PMBX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw'"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "3Z"; "0FF"; "0H"]; ["0HI"; "0K"; "0L"; "0LBX"; "0LK"; "0LK'"; "4Model"; "4event"; "5bvmap"; "0M"; "0M'"; "0M1"; "0M1v"; "0R"; "0R'"; "6mrestrict"]; ["7credit"; "7regs_preserved"; "8S"; "8ar_sptop"; "8byte_at"; "8fframe"; "8model_rt"; "8ri_inv"; "8shadow_zero"; "8vml_of"; ":u32_at"; ":u8_at"; "9SCFG"; ";avis"; "<zeros_at"; "=argp"]; [">ADDR_B"; "?PS"; "?pstate"; "?vec_at"; "?vec_own"; "@accA"; "@annA"; "@aobjA"; "@cfg"; "@entryA"; "@pm_scr"; "Acone_miu_spec"; "BFPState"; "Bgetr"; "Csrealizes"; "Dahpres"]; ["Damodel_ok"; "Eloaded_segments"; "0SCFG_P"; "Fincl"; "Gadd"; "Gdiv"; "Gle"; "Glt"; "Gmodulo"; "Gmul"; "Gof_nat"; "Gpow"; "Gsub"; "0a"; "0ar"; "0b"]; ["0c"; "0cr"; "0fx"; "0fx'"; "0i"; "0j"; "0k"; "0m"; "0model"; "0model'"; "0n"; "0p"; "0p1"; "0p2"; "0p3"; "0r"]; ["0sp"; "HZ_to_bv"; "Hbv"; "0stk"; "0t"; "0v"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
| solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
| solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
| solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PMBCOMIU.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma stack_zeros12 : ltac2:(TCodec.tc2 tcn__PmBConeMiu "Q6'S2yR0%211'8y8%511%311p051'=&Q8r2&R<r1+\P0%3221+Q`0%73621'<&R8+@%22:1z%53>21&Q>r4&R4&R5r3+8%3221+Qoono`0%6221+`0%:3921p0<1p0C1pV2L1pQDN1").
Proof. intros M sp.
intros SZ S16 i Hi. pose proof (SZ (1024 + i) ltac:(Lia.lia)) as X. unfold byte_at, S, SB in X.
replace (sp / 8 + 2147450368 + i) with ((sp - 12288) / 8 + 2147450880 + (1024 + i)) by Lia.lia. exact X.
Qed.
Lemma zsh1 : ltac2:(TCodec.tc2 tcn__PmBConeMiu "M'S2yR0%211'8y8%511%311p051'=&Q4r2&Q2r1%211z%63521&Q>r3&R4&R5+8%22;1+QoooPP0%5221+1%93821p0;1pUHC1pQDE1").
Proof. intros M p. intros X i Hi. replace i with 0 by Lia.lia. rewrite Z.add_0_r. unfold byte_at, S, SB in X. exact X. Qed.
Lemma shadow_low : ltac2:(TCodec.tc2 tcn__PmBConeMiu "Q5'=&R6zr3%3221&R4r4%2214&R;+2+Q?%3221%;251';&R7&R5+8%22;1%42?1%62?1+QoooPP0&Q2r6%211%C21B%H251+Q<%C2B1%G281%?251%A251p0<1p0D1p0M1pU<Q21pU2Q31pU0Q41").
Proof. intros b c j. unfold S, SB. intros. Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma vis_u8 : ltac2:(TCodec.tc2 tcn__PmBConeMiu "Q?'S2yR0%211'3p021'8y8%711%311p071'='<&Or5r4%3221r3%63821&Q=r6+1%33251&R6z%221:&R7&R;+2+QO%3221%52A1&Q;&R1r7%3421?Er9%54413Ap031p081p0?1p0C1p0H1pV<Q01pTLQ11pQJQ31pQHQ41pQ0Q:1").
Proof. intros H M1 M1v a v. intros E AV H0 H1 X. rewrite <- E in X. exact (proj1 (L5A.u8_at_vis H M1 a v AV ltac:(Lia.lia) ltac:(Lia.lia)) X). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma S_range : ltac2:(TCodec.tc2 tcn__PmBConeMiu "J'=';&R6zr1%3221&R7&R;+2+Q?%3221%5271%;271+QoooPP0&Q2r2%211%?241&R4+Q<%=2<1%3281%@261%F261p0<1pV>I1").
Proof. intros x. unfold S, SB. intros. Lia.lia. Qed.
Lemma S_add8 : ltac2:(TCodec.tc2 tcn__PmBConeMiu "@'='<&R4&Q2r2%211r1%5221&R9+8%2214%9271%911%<3=61pU<>1pTL?1").
Proof. intros a j. unfold S. Lia.lia. Qed.
Lemma stk_sh_idx : ltac2:(TCodec.tc2 tcn__PmBConeMiu "Q5'='<&R8r2+@%3221z%63721';&R6%1247&R7+`0%22:1%6241&R4&R5r4+8%3221+Qoono`0%6221r3%8221&Q2&R<+TP0%22:1&R9%12;7%?231%711%O3Q091p0C1p0K1pU:Q31pV2Q41").
Proof. intros sp i. unfold S, SB. intros. Lia.lia. Qed.
Lemma d32 : ltac2:(TCodec.tc2 tcn__PmBConeMiu "='='<&R5&R9+Q0r1%3221+8%6221+4%7215%:3;31pV><1").
Proof. intros x. Lia.lia. Qed.
Lemma d32b : ltac2:(TCodec.tc2 tcn__PmBConeMiu "@'='<&R5&R4&R9+Q0r1%3221%5213+8%8221+4%8216%:212%=3>41pV>?1").
Proof. intros x. Lia.lia. Qed.
Lemma pow2k : ltac2:(TCodec.tc2 tcn__PmBConeMiu "D'=';&R6zr1%3221+;%5231%7231+1&R;+2r2%3221%<251+RP0%>231%@231p0:1pU>C1").
Proof. intros k. intros Hk. split; [pose proof (Z.pow_pos_nonneg 2 k ltac:(Lia.lia) ltac:(Lia.lia)); Lia.lia|]. change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT.
Let LYa := PMB.ly_as0 L C LY.
Theorem fast : ltac2:(TCodec.tc2 tcn__PmBConeMiu "XD'QL&Hy5'S2yR0%211%5241'8y8%611%311p061'F'6'G%211!pV>21':'=%2211%811&Q5%:11&Q0'QB%=11&Q7v@&2&QDr;r:%3221rA%63?21r@r?r=r>rD&Q9rC%211%A8@9876541&R0%1296(7%11Q2%911&QI&Q@vBvR>rHrGz%7865432JI1'<&QMrI&S1&R:u:%211%42QO1%7261%62QOO%:3QO21&QGrE+H%332Q61&R8rB+8%3221%C3QJ1E&QErK%231Q69&QC&R1&QFrL%483721Q=Q;;QC&R7&5%12QO>%K11&R;+2%221QB%7241rOu;%Q211%Q42RO1%Q7241%Q93RN1Q0rQ0u<%Q811%Q:2S51%Q=241%Q?3S41Q6rQ1u=%Q>11%Q@2S;1%QC241%QE3S:1Q<+4%Q82R71%QH3RO1QJ&Q4rQ3&Q2%11Q@%4331QOrQ4%6313R1rQ5%8315R3&Q?&Q3%11R9rQ2rJrN%664321R<B%765?QDQ5R=C+1%967=QAQ1R?1&Q:rQ9%24QF1QIRBrQ:%44QH1QKRD&Q;rQ;%24QK1QNRG';&R6%12RHR1+O%QH2QG1%QM2R41%6241+X0%R02R71%9271&Q1rQFr5%3221rQ>rQ=rQ<(4(QA%14Q7Q9Q=S9%SC1T9%43T:21%T73T;H1%RD8RCRGRB;9871r6rQ?%RJ321S1&QOrQErQD&QJ%11SE(9rQ@%24TMTM1S9%T21TM%C3TN21rQHr7%<9T1T0;:G8321&Q6%1243&R3%13U35?%23U6@6r8%T?21TLrQC%U02C1rQJ%U33U<21rQIr9r<%TK1U5%U:8U954U5Q<321'QN&Q<vR2%211&QHrQA%26SJU7U51U69rQL%84SL521p0:1p0D1p0G1p0I1p0L1p0O1p0Q=1p0QA1p0QL1p4V31pQ<V21pUDV>1pQFV@1pQNVF1pU8VM1rQB+egZ0%F6T>2E1QAQI%K4T?H1R5p051p0R<1p0R@1p0RA1p0RI1p0RM1p0S01p0S41p0S71p0S91p0SA1p0SD1p0SG1p0SM1p0SN1p0T21p0T91p0T@1p0TG1p0U01p0U61p0U:1p0U@1p0UE1p0V11p0V:1p0V>1p0VA1pV:W;1pUFW<1pU@W=1pUNW>1pULW?1pUJW@1pV0WA1pV2WB1pV8W<1pU>WD1pU0WE1pV<WF1pU4WB1p2WF1pQ:WE1pNWF1pQ8WI1pQ4WN1pUBX41pQDX61pQLX<1pU6XC1").
Proof.
intros fx R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n t HH AM K0 ENT A10 AOV V8 ACCV VEC LEN A11 A12 A13 P14 P24 SP1 SP2 SP3 AG1 AG2 AG3 U1 U2 U3 RM RN RT KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
destruct VEC as (VB & VE & VC & Kr & LENk & B16 & BDEF & BACC & BANN & BST).
set (len := Z.of_nat (length stk)) in *.
set (LB := PM.vec_own b k ++ LBX) in *.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
assert (BIN : In (b, 32 * 2 ^ k) LB) by (left; reflexivity).
destruct (PMBEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b (32 * 2 ^ k) HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _ & Bq5 & Bq6 & _ & Bq8).
pose proof (pow2k k Kr) as P2K.
pose proof (PMKB.aobj_of_aobjA FF v 24 AOV V8) as AOB.
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
destruct (PMBEK.arg_facts L ar C HI LY HIok LB FF LK cr Aw M _ sp 12288 v p1 4 HH ASTK ltac:(lia) AG1 ltac:(lia)) as (Pa0 & Pa1 & Pa2 & Pa3 & Pa4 & Pa5 & Pa6).
destruct (PMBEK.arg_facts L ar C HI LY HIok LB FF LK cr Aw M _ sp 12288 v p2 4 HH ASTK ltac:(lia) AG2 ltac:(lia)) as (Pb0 & Pb1 & Pb2 & Pb3 & Pb4 & Pb5 & Pb6).
destruct (PMBEK.arg_facts L ar C HI LY HIok LB FF LK cr Aw M _ sp 12288 v p3 1 HH ASTK ltac:(lia) AG3 ltac:(lia)) as (Pc0 & Pc1 & Pc2 & Pc3 & Pc4 & Pc5 & Pc6).
pose proof (Pa5 b (32 * 2 ^ k) BIN) as PaB. pose proof (Pb5 b (32 * 2 ^ k) BIN) as PbB. pose proof (Pc5 b (32 * 2 ^ k) BIN) as PcB.
assert (VBLK : v + 24 <= b \/ b + 32 * 2 ^ k <= v).
{ destruct AOV as (f & Hf & Y1 & Y2). destruct (Bq8 f Hf) as [Y|Y]; [right; lia| left; lia]. }
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
assert (X0 : L5.img_clear MV 1232896 1269760) by (apply L5A.img_clear_mrestrict; exact GOT).
assert (X1 : L5.u64_at RSEGS MV 1296952 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1296952 2147450880 (VIMG 1296952 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
assert (X2 : L5.u32_at RSEGS MV 1296960 1) by (apply (proj2 (L5A.u32_at_vis H M 1296960 1 (VIMG 1296960 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
{ apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
assert (X4 : L5KA.zeros_at MV (sp / 8 + 2147450368) 512).
{ intros i Hi. unfold MV. rewrite (AsanAcct.mrestrict_visible H M). apply (stack_zeros12 M sp STKSH A16). exact Hi.
assert (AV : L5A.avis H (sp / 8 + 2147450368 + i) 1).
{ apply (VSTSH (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
{ exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
assert (X6 : L5.u64_at RSEGS MV v b) by (apply (proj2 (L5A.u64_at_vis H M v b ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VB).
assert (X7 : L5.u64_at RSEGS MV (v + 8) (b + 32 * len)) by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VE).
assert (X8 : L5.u64_at RSEGS MV (v + 16) (b + 32 * 2 ^ k)) by (apply (proj2 (L5A.u64_at_vis H M (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VC).
cfeed P (PMBCOP2.bcuA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 37%nat => 32 * len | 38%nat => m | 39%nat => n | 41%nat => b + 32 * 2 ^ k | 52%nat => p3 | 53%nat => t | _ => 0 end)) ltac:(first [assumption | unfold PMBCOP2.aligned; lia | lia]).
destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & fR1 & fR2 & fR8 & fR9 & fR10 & fR11 & fR12 & fR13 & fR14 & fR15 & fR18 & fR19
& T80 & T72 & T48 & T56 & T64 & T40 & T32 & T24 & T16 & T8).
set (W1 := fun a => sp - 96 <= a < sp - 96 + 96).
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xadd40 R1 0x7b3f4 M1v W1 K HH AM MS1 MG1).
{ intros a Ha N. apply FZ1; [exact Ha| exact N]. }
{ intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
pose proof AM1 as (Mh1 & MI1).
assert (SH01 : forall x, 0 <= x < 2 ^ 64 -> x < sp - 96 -> M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x)) by (intros x Hx Hx'; apply FR1; [exact Hx| unfold W1; lia]).
pose proof (HAJ.aex_annotate _ _ _ _ _ EXT) as ANN. unfold HAJ.annotate_spec in ANN.
cbn [PMB.EXT HAJ.ec_ann_pc HAJ.ec_ann_scr paa_annotate PMB.AAD AADDR_A] in ANN. rewrite (L5A.aly_segs L C LYa) in ANN.
apply (ANN fx1 R1 M1 model1 LB FF LK cr Aw K b (32 * 2 ^ k) (32 * len) (32 * len + 32)); clear ANN.
{ exact HH1. }
{ exact Mh1. }
{ exact MI1. }
{ rewrite L5K.rl10. exact fR10. }
{ rewrite L5K.rl11. exact fR11. }
{ rewrite L5K.rl12. exact fR12. }
{ rewrite L5K.rl13, fR13. f_equal. lia. }
{ exact BIN. }
{ exact B16. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ apply (PMBEK.ann_agree M M1 b (32 * len) (32 * 2 ^ k)); [| lia| lia| exact BANN].
intros j Hj. pose proof (shadow_low b (32 * 2 ^ k) j ltac:(lia) ltac:(lia) Hj) as SL. apply SH01; lia. }
{ rewrite L5K.rl4, (KS1 4%nat) by inl. exact Rtp. }
{ rewrite L5K.rl1, fR1. vm_compute. reflexivity. }
{ rewrite L5K.rl2, fR2, L5.unsigned_lit by lia.
apply (L5SAR.astack_ok_of_astk L ar C LYa M M1 sp 12288 80 2304 ASTK MGM1); [lia| lia| lia|].
replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
{ exact K0. }
intros fx2 R2 M2 model2 Aw2 RP2 ANN2 KEEP2 DSH2 SCR2 MRT2 INC2 MI2 HH2.
rewrite L5K.rl2, fR2, L5.unsigned_lit in KEEP2, SCR2 by lia. rewrite L5K.rl1, fR1.
assert (AM2 : L5CA.amodel_ok Aw2 model2) by (split; [rewrite (L5LZ.model_rt_halted model1 model2 MRT2); exact Mh1| exact MI2]).
assert (CS2 : forall k0, In k0 L5SAR.cs_all -> getr R2 (reg k0) = getr R1 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R1 R2 k0 RP2 Hk)).
assert (T20 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 2384 <= a < sp) -> ~ in_shadow_of b (32 * 2 ^ k) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha Hc N1 N2. rewrite (KEEP2 a Ha ltac:(apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]) N2). apply FR1; [exact Ha| unfold W1; lia]. }
assert (ASTK2 : L5CA.astk ar M2 sp 12288).
{ apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw M M1 M2 _ sp 12288 (sp - 80) 2304 HH ASTK MGM1).
- intros a Ha Hs Hns. apply KEEP2; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
intros X. pose proof (PMBEK.in_shadow_range b (32 * 2 ^ k) a ltac:(lia) ltac:(lia) X). lia.
- exact SCR2.
- lia. - lia. - lia. }
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 v 24 sp 12288 HH2 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF2 & OVIS2 & _).
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
assert (Y0 : L5.img_clear MV2 1232896 1269760) by (apply L5A.img_clear_mrestrict; exact GOT2).
assert (Y1 : L5.u64_at RSEGS MV2 1296952 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1296952 2147450880 (VIMG2 1296952 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
assert (Y2 : L5.u32_at RSEGS MV2 1296960 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1296960 1 (VIMG2 1296960 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
assert (Y3 : L5.writable RSEGS MV2 (sp - 4096) 4096).
{ apply (proj2 (L5A.writable_vis H2 M2 (sp - 4096) 4096 (VIS2 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5SAR.astk_writable ar M2 sp 12288); [exact ASTK2| lia| lia| lia]. }
assert (STKSH2 : shadow_zero M2 (sp - 12288) 1536).
{ intros j Hj. pose proof (S_add8 (sp - 12288) j) as E.
pose proof (S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
unfold byte_at. rewrite E. rewrite T20; [rewrite <- E; apply STKSH; exact Hj| lia| apply (PMBEK.stack_sh_client L ar FF); lia| lia|].
apply (PMBEK.sh_apart b (32 * 2 ^ k) (sp - 12288 + 8 * j)); lia. }
assert (Y4 : L5KA.zeros_at MV2 (sp / 8 + 2147450368) 512).
{ intros i Hi. unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2). apply (stack_zeros12 M2 sp STKSH2 A16). exact Hi.
assert (AV : L5A.avis H2 (sp / 8 + 2147450368 + i) 1).
{ apply (VSTSH2 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
assert (ACCV2 : PMSPA.accA M2 v 24).
{ apply (PMFA.accA_agree M M2 v 24); [| exact ACCV]. intros x Hx. pose proof (S_range x ltac:(lia)) as SRx. apply T20; [lia| | lia|].
- exact (PMBEK.frame_sh_client L ar FF v 24 x LB 0 0 AOV Hx).
- apply (PMBEK.sh_apart b (32 * 2 ^ k) x); lia. }
assert (Y5 : L5KA.zeros_at MV2 (v / 8 + 2147450880) 3).
{ exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 v 24 HH2 AOV V8 ltac:(lia) ltac:(reflexivity) ACCV2). }
assert (TV : forall a, v <= a < v + 24 -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha. apply T20; [lia| apply (L5SAR.obj_client L ar LB FF 0 0 v 24 a AOB); lia| lia|].
intros X. pose proof (PMBEK.in_shadow_range b (32 * 2 ^ k) a ltac:(lia) ltac:(lia) X). lia. }
assert (Y6 : L5.writable RSEGS MV2 v 24).
{ apply (proj2 (L5A.writable_vis H2 M2 v 24 OVIS2 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF2. lia. lia. }
assert (Y7 : L5.u64_at RSEGS MV2 v b).
{ apply (proj2 (L5A.u64_at_vis H2 M2 v b ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact VB]. }
assert (Y8 : L5.u64_at RSEGS MV2 (v + 8) (b + 32 * len)).
{ apply (proj2 (L5A.u64_at_vis H2 M2 (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact VE]. }
assert (Y9 : L5.u64_at RSEGS MV2 (v + 16) (b + 32 * 2 ^ k)).
{ apply (proj2 (L5A.u64_at_vis H2 M2 (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact VC]. }
destruct (PMBEK.arg_vis L ar C HI LY HIok LB FF LK cr Aw2 M2 model2 sp 12288 v p1 4 HH2 ASTK2 ltac:(lia) AG1 ltac:(lia)) as (AV1 & AVS1).
destruct (PMBEK.arg_vis L ar C HI LY HIok LB FF LK cr Aw2 M2 model2 sp 12288 v p2 4 HH2 ASTK2 ltac:(lia) AG2 ltac:(lia)) as (AV2 & AVS2).
destruct (PMBEK.arg_vis L ar C HI LY HIok LB FF LK cr Aw2 M2 model2 sp 12288 v p3 1 HH2 ASTK2 ltac:(lia) AG3 ltac:(lia)) as (AV3 & AVS3).
assert (TPn : forall w p x, 0 < w -> (6893568 <= p /\ p + w <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= p \/ p + w <= 2147446784)
/\ (sp <= p \/ p + w <= ahl_ceil ar)) -> (forall i sp' scr', 0 <= i < w -> sp' <= sp -> aclient L ar LB FF sp' scr' (p + i)) ->
(p + w <= b \/ b + 32 * 2 ^ k <= p) -> p <= x < p + w -> M2 (Z_to_bv 64 x) = M (Z_to_bv 64 x)).
{ intros w p x Hw (Q0 & Q1 & Q2 & Q3) CLp Bp Hx. apply T20; [lia| replace x with (p + (x - p)) by lia; apply CLp; lia| lia|].
intros X. pose proof (PMBEK.in_shadow_range b (32 * 2 ^ k) x ltac:(lia) ltac:(lia) X). lia. }
assert (TP : forall p q x, PMBEK.argp (ar_sptop ar) FF sp v p 4 -> (6893568 <= p /\ p + 4 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= p \/ p + 4 <= 2147446784)
/\ (sp <= p \/ p + 4 <= ahl_ceil ar)) -> (forall i sp' scr', 0 <= i < 4 -> sp' <= sp -> aclient L ar LB FF sp' scr' (p + i)) ->
(p + 4 <= b \/ b + 32 * 2 ^ k <= p) -> q = p -> p <= x < p + 4 -> M2 (Z_to_bv 64 x) = M (Z_to_bv 64 x)).
{ intros p q x AP (Q0 & Q1 & Q2 & Q3) CLp Bp Eq Hx. apply T20; [lia| replace x with (p + (x - p)) by lia; apply CLp; lia| lia|].
intros X. pose proof (PMBEK.in_shadow_range b (32 * 2 ^ k) x ltac:(lia) ltac:(lia) X). lia. }
assert (TPS : forall p, PMBEK.argp (ar_sptop ar) FF sp v p 4 -> (p + 4 <= b \/ b + 32 * 2 ^ k <= p) -> 0 <= p < 2 ^ 47 -> byte_at M (S p) 0 -> byte_at M2 (S p) 0).
{ intros p AP Bp Hp X. pose proof (S_range p Hp) as SRp. unfold byte_at in *. rewrite T20; [exact X| lia| | lia|].
- exact (PMBEK.arg_client L ar HI LB FF LK cr Aw M _ sp 12288 v p 4 HH ASTK ltac:(lia) AP ltac:(lia) LB 0 0).
- apply (PMBEK.sh_apart b (32 * 2 ^ k) p); lia. }
assert (Y10 : L5.u32_at RSEGS MV2 p1 m).
{ apply (proj2 (L5A.u32_at_vis H2 M2 p1 m AV1 ltac:(lia) ltac:(lia))).
apply (PMF.u32_at_agree RSEGS M M2); [intros i Hi; apply (TP p1 p1 i AG1 (conj Pa0 (conj Pa1 (conj Pa2 Pa4))) Pa6 PaB eq_refl Hi)| lia| lia| exact U1]. }
assert (Y11 : L5.u32_at RSEGS MV2 p2 n).
{ apply (proj2 (L5A.u32_at_vis H2 M2 p2 n AV2 ltac:(lia) ltac:(lia))).
apply (PMF.u32_at_agree RSEGS M M2); [intros i Hi; apply (TP p2 p2 i AG2 (conj Pb0 (conj Pb1 (conj Pb2 Pb4))) Pb6 PbB eq_refl Hi)| lia| lia| exact U2]. }
assert (TPS1 : forall w p sv, 0 < w <= 8 -> PMBEK.argp (ar_sptop ar) FF sp v p w -> (p + w <= b \/ b + 32 * 2 ^ k <= p) -> 0 <= p < 2 ^ 47 -> byte_at M (S p) sv -> byte_at M2 (S p) sv).
{ intros w p sv Hw AP Bp Hp X. pose proof (S_range p Hp) as SRp. unfold byte_at in *. rewrite T20; [exact X| lia| | lia|].
- exact (PMBEK.arg_client L ar HI LB FF LK cr Aw M _ sp 12288 v p w HH ASTK ltac:(lia) AP ltac:(lia) LB 0 0).
- apply (PMBEK.sh_apart b (32 * 2 ^ k) p); lia. }
assert (Y10c : L5.u8_at RSEGS MV2 p3 t).
{ apply (proj2 (L5A.u8_at_vis H2 M2 p3 t AV3 ltac:(lia) ltac:(lia))).
apply (L5C.u8_at_agree RSEGS M M2); [intros i Hi; apply (TPn 1 p3 i ltac:(lia) (conj Pc0 (conj Pc1 (conj Pc2 Pc4))) Pc6 PcB Hi)| lia| lia| exact U3]. }
assert (Y12 : L5KA.zeros_at MV2 (p1 / 8 + 2147450880) 1).
{ apply zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact (TPS p1 AG1 PaB ltac:(lia) SP1)|].
pose proof (AVS1 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
assert (Y13 : L5KA.zeros_at MV2 (p2 / 8 + 2147450880) 1).
{ apply zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact (TPS p2 AG2 PbB ltac:(lia) SP2)|].
pose proof (AVS2 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
assert (Y13c : L5KA.zeros_at MV2 (p3 / 8 + 2147450880) 1).
{ apply zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact (TPS1 1 p3 0 ltac:(lia) AG3 PcB ltac:(lia) SP3)|].
pose proof (AVS3 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
assert (TS : forall a v0, sp - 80 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
{ intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H2 M2 a v0 (VIS2 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply KEEP2; [lia| apply L5SAR.stack_client; lia|]| lia| lia|].
- intros XS. pose proof (PMBEK.in_shadow_range b (32 * 2 ^ k) i ltac:(lia) ltac:(lia) XS). lia.
- apply (PMBIS1.vis_u64 _ _ _ _ _ VIS1); [apply VIS; lia| lia| lia| exact X]. }
pose proof (TS (sp - 8) _ ltac:(lia) ltac:(lia) T8) as Z8.
pose proof (TS (sp - 16) _ ltac:(lia) ltac:(lia) T16) as Z16.
pose proof (TS (sp - 24) _ ltac:(lia) ltac:(lia) T24) as Z24.
pose proof (TS (sp - 32) _ ltac:(lia) ltac:(lia) T32) as Z32.
pose proof (TS (sp - 40) _ ltac:(lia) ltac:(lia) T40) as Z40.
pose proof (TS (sp - 48) _ ltac:(lia) ltac:(lia) T48) as Z48.
pose proof (TS (sp - 56) _ ltac:(lia) ltac:(lia) T56) as Z56.
pose proof (TS (sp - 64) _ ltac:(lia) ltac:(lia) T64) as Z64.
pose proof (TS (sp - 72) _ ltac:(lia) ltac:(lia) T72) as Z72.
pose proof (TS (sp - 80) _ ltac:(lia) ltac:(lia) T80) as Z80.
assert (BDEF2 : L5.defined M2 b (32 * 2 ^ k)).
{ intros i Hi. rewrite KEEP2; [apply (L5.defined_grows M M1 _ _ MGM1 BDEF i Hi)| lia| |].
- unfold aclient, aclient_g. left. exists (b, 32 * 2 ^ k). split; [exact BIN| cbn [fst snd]; lia].
- intros X. pose proof (PMBEK.in_shadow_range b (32 * 2 ^ k) (b + i) ltac:(lia) ltac:(lia) X). lia. }
assert (Y14 : L5KA.zeros_at MV2 ((b + 32 * len) / 8 + 2147450880) 4).
{ rewrite (PMBEK.sh_idx b (32 * len)) by lia. rewrite d32. destruct ANN2 as (ZA & _). rewrite d32b in ZA. intros i Hi.
assert (AV : L5A.avis H2 (S b + 4 * len + i) 1).
{ apply (VBSH2 b (32 * 2 ^ k) _ 1 BIN). intros j Hj. replace (S b + 4 * len + i + j) with (S b + (4 * len + i + j)) by lia.
apply PMBEK.sh_in; [lia| lia| lia|]. rewrite d32. lia. }
unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2).
- replace (S b + 4 * len + i) with (S b + (4 * len + i)) by lia. apply ZA. lia.
- pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
assert (Y15 : L5.writable RSEGS MV2 (b + 32 * len) 32).
{ apply (proj2 (L5A.writable_vis H2 M2 (b + 32 * len) 32 (VBLK2 b (32 * 2 ^ k) (b + 32 * len) 32 BIN ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 b (32 * 2 ^ k)); [exact BDEF2| lia| lia]| lia| lia]. }
assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 80)) by (rewrite CS2 by inl; exact fR2).
assert (J8 : getr R2 (reg 8) = Z_to_bv 64 (p3)) by (rewrite CS2 by inl; exact fR8).
assert (J9 : getr R2 (reg 9) = Z_to_bv 64 (p2)) by (rewrite CS2 by inl; exact fR9).
assert (J18 : getr R2 (reg 18) = Z_to_bv 64 (p1)) by (rewrite CS2 by inl; exact fR18).
assert (J19 : getr R2 (reg 19) = Z_to_bv 64 (2147450880)) by (rewrite CS2 by inl; exact fR19).
pose proof (PMBIS1.bvu (getr R (reg 1))) as UR1. pose proof (PMBIS1.bvu (getr R (reg 8))) as UR8. pose proof (PMBIS1.bvu (getr R (reg 9))) as UR9. pose proof (PMBIS1.bvu (getr R (reg 18))) as UR18. pose proof (PMBIS1.bvu (getr R (reg 19))) as UR19.
cfeed P (PMBCOP2.bcuB_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 37%nat => 32 * len | 38%nat => m | 39%nat => n | 41%nat => b + 32 * 2 ^ k | 52%nat => p3 | 53%nat => t | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | _ => 0 end)) ltac:(first [assumption | unfold PMBCOP2.aligned; lia | lia]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & gR1 & gR2 & gR8 & gR9 & gR10 & gR11 & gR12 & gR13 & gR14 & gR15 & gR18 & gR19
& G8 & G24 & G16 & G8b & G0).
assert (R3ra : getr R3 (reg 1) = Z_to_bv 64 r) by (rewrite gR1, Z_to_bv_bv_unsigned; exact Rra).
pose proof (PMK.ret_to RSEGS fx3 R3 M3v 0xade84 (ltac:(oW' 0xade84%Z)) r (ltac:(oF' 0xade84%Z)) eq_refl (ltac:(oD' 0xade84%Z)) R3ra ltac:(lia) Hr2) as MS4.
set (W3 := fun a => (b + 32 * len + 0 <= a < b + 32 * len + 0 + 32) \/ (sp - 80 <= a < sp - 80 + 16) \/ (sp - 56 <= a < sp - 56 + 8) \/ (v + 8 <= a < v + 8 + 8)).
apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 fx2 fx3 R2 0xac858 R3 r M3v W3 K HH2 AM2 ltac:(eapply msteps_trans; [exact MS3| exact MS4]) MG3).
{ intros a Ha N. apply FZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; left; exact X| intros X; apply N; right; right; right; exact X]. }
{ intros a Ha [Wa|[Wa|[Wa|Wa]]].
- split; [|lia]. unfold aclientw, aclient_g. left. exists (b, 32 * 2 ^ k). split; [exact BIN| cbn [fst snd]; lia].
- split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
- split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
- split; [apply (L5SAR.obj_client L ar LB FF 0 0 v 24 a AOB); lia| lia]. }
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
apply (KONT fx3 R3 M3 model3 LK Aw2).
- apply L5SAR.preserved_by_index. intros k0 Hk.
assert (CH : forall k', In k' [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg k') = getr R (reg k')).
{ intros k' Hk'. assert (Y : In k' PMBCOP2.KS_bcuB /\ In k' L5SAR.cs_all /\ In k' PMBCOP2.KS_bcuA)
by (destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; (split; [inl| split; inl])).
destruct Y as (Yk1 & Yk2 & Yk3). rewrite (KS3 k' Yk1), (CS2 k' Yk2), (KS1 k' Yk3). reflexivity. }
unfold L5SAR.cs_all in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]].
+ rewrite gR2. exact (eq_sym Rsp).
+ apply CH; inl.
+ apply CH; inl.
+ rewrite gR8, Z_to_bv_bv_unsigned; reflexivity.
+ rewrite gR9, Z_to_bv_bv_unsigned; reflexivity.
+ rewrite gR18, Z_to_bv_bv_unsigned; reflexivity.
+ rewrite gR19, Z_to_bv_bv_unsigned; reflexivity.
+ apply CH; inl.
+ apply CH; inl.
+ apply CH; inl.
+ apply CH; inl.
+ apply CH; inl.
+ apply CH; inl.
+ apply CH; inl.
+ apply CH; inl.
-
assert (TW3 : forall a, 0 <= a < 2 ^ 64 -> ~ W3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) by exact FR3.
assert (TB : forall a, b <= a < b + 32 * len -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha. rewrite TW3; [| lia| unfold W3; lia]. apply T20; [lia| | lia|].
- unfold aclient, aclient_g. left. exists (b, 32 * 2 ^ k). split; [exact BIN| cbn [fst snd]; lia].
- intros X. pose proof (PMBEK.in_shadow_range b (32 * 2 ^ k) a ltac:(lia) ltac:(lia) X). lia. }
assert (TSH : forall j, 0 <= j < (32 * 2 ^ k) / 8 -> M3 (Z_to_bv 64 (S b + j)) = M2 (Z_to_bv 64 (S b + j))).
{ intros j Hj. pose proof (shadow_low b (32 * 2 ^ k) j ltac:(lia) ltac:(lia) Hj) as SL. apply TW3; [lia| unfold W3; intros [XW|XW]; [destruct Bq6 as [YW|YW]; lia| destruct OBIG as [YW|YW]; lia]]. }
unfold PM.vec_at. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. fold len.
split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; rewrite TW3; [apply TV; lia| lia| unfold W3; lia]| lia| lia| exact VB]. }
split. { replace (b + 32 * (len + 1)) with (b + 32 * len + 32) by lia.
apply (PMBIS1.vis_u64 _ _ _ _ _ VIS3); [eapply L5A.avis_sub; [exact OVIS2| lia| lia]| lia| lia| exact G8]. }
split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; rewrite TW3; [apply TV; lia| lia| unfold W3; lia]| lia| lia| exact VC]. }
split; [lia|]. split; [lia|]. split; [exact B16|].
split; [apply (L5.defined_grows M2 M3 _ _ MGM3); exact BDEF2|].
destruct ANN2 as (ZA2 & PA2).
split. { unfold PMSPA.accA. apply (PMFA.accA_agree M2 M3 b (32 * (len + 1))).
- intros x Hx. pose proof (S_range x ltac:(lia)) as SRx. apply TW3; [lia| unfold W3; intros [XW|XW]; [destruct Bq6 as [YW|YW]; lia| destruct OBIG as [YW|YW]; lia]].
- unfold PMSPA.accA. apply (L5CB.aacc_of_zero M2 b ((32 * len + 32) / 8) b (32 * (len + 1)) ZA2); [lia| lia| lia| rewrite d32b; lia]. }
split. { apply (PMBEK.ann_agree M2 M3 b (32 * (len + 1)) (32 * 2 ^ k)); [exact TSH| lia| lia|].
replace (32 * (len + 1)) with (32 * len + 32) by lia. split; [exact ZA2| exact PA2]. }
intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [Hl|Hl].
+ rewrite app_nth1 by exact Hl. apply (PMF.pstate_at_agree RSEGS M M3); [lia| lia| | apply BST; exact Hl].
intros x Hx. apply TB. split; [lia|]. assert (Z.of_nat i + 1 <= len) by (unfold len; lia). lia.
+ assert (Ei : i = length stk) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. fold len.
assert (AVB : forall a n0, b <= a -> a + n0 <= b + 32 * 2 ^ k -> L5A.avis H2 a n0) by (intros a n0 Ya1 Ya2; apply (VBLK2 b (32 * 2 ^ k) a n0 BIN); lia).
unfold PM.pstate_at. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx].
split; [apply (PMBIS1.vis_u32 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact G0]|].
split; [apply (PMBIS1.vis_u64 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact G8b]|].
split; [apply (vis_u8 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact G16]|].
apply (PMBIS1.vis_u64 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact G24].
- apply (PMFA.accA_agree M2 M3 v 24); [| exact ACCV2]. intros x Hx. pose proof (S_range x ltac:(lia)) as SRx. apply FR3; [lia| unfold W3; intros [XW|XW]; [destruct Bq6 as [YW|YW]; lia| destruct OBIG as [YW|YW]; lia]].
- apply (L5SAR.ahpres_of L ar LBX FF sp 12288 _ M M3).
+ intros a (Ha & Hc & Ho).
assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, 32 * 2 ^ k)] FF sp 12288 a Hc)).
assert (NB : ~ (b <= a < b + 32 * 2 ^ k)) by (exact (PMBEK.own_notclient L ar C HI LY HIok b (32 * 2 ^ k) LBX FF LK cr Aw M _ HH a sp 12288 Hc)).
assert (NS : ~ in_shadow_of b (32 * 2 ^ k) a) by (exact (PMBEK.own_sh_notclient L ar C HI LY HIok b (32 * 2 ^ k) LBX FF LK cr Aw M _ HH ltac:(lia) a sp 12288 Hc)).
assert (NV : ~ (v <= a < v + 24)) by (intros X; apply (Ho (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]).
destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT HcB) as [Z1|Z1].
* rewrite FR3; [| exact Ha| unfold W3; lia]. rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 80) 2304 a HcB); intros x Hx; lia| exact NS].
apply FR1; [exact Ha| unfold W1; lia].
* rewrite FR3; [| exact Ha| unfold W3; lia]. rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 80) 2304 a HcB); intros x Hx; lia| exact NS].
apply FR1; [exact Ha| unfold W1; lia].
+ pose proof ASTK2 as (_ & _ & _ & _ & SD2 & _). apply (L5.defined_grows M2 M3 _ _ MGM3). exact SD2.
+ intros a Ha Hc HM. apply MGM3.
assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, 32 * 2 ^ k)] FF sp 12288 a Hc)).
assert (NS : ~ in_shadow_of b (32 * 2 ^ k) a) by (exact (PMBEK.own_sh_notclient L ar C HI LY HIok b (32 * 2 ^ k) LBX FF LK cr Aw M _ HH ltac:(lia) a sp 12288 Hc)).
rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 80) 2304 a HcB); intros x Hx; lia| exact NS].
apply MGM1. exact HM.
- apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
- intros x Hx. exact Hx.
- exact INC2.
- exact AM3.
- exact HH3.
Qed.
Theorem cone_miu_ok : ltac2:(TCodec.tc2 tcn__PmBConeMiu "6&QKvR2vBvR>v@%544321").
Proof.
unfold PMBX.cone_miu_spec, PMSBX.cone_spec_at.
intros fx R M model K LBX FF LK Aw cr v b k stk c sp r HH AM K0 ENT FRS A10 AOV V8 ACCV VEC LEN CELLS KONT.
destruct CELLS as (p1 & p2 & p3 & m & n & t & A11 & A12 & A13 & P14 & P24 & AC1 & AC2 & AC3 & AG1 & AG2 & AG3 & SB1 & SB2 & SB3 & U1 & U2 & U3 & RM & RN & RT & ->).
exact (fast fx R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n t HH AM K0 ENT A10 AOV V8 ACCV VEC LEN A11 A12 A13 P14 P24 SB1 SB2 SB3 AG1 AG2 AG3 U1 U2 U3 RM RN RT KONT).
Qed.
End Stage.
End PMBCOMIU.
