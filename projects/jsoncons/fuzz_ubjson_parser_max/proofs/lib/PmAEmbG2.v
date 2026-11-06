(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa PmModelFactsA PmStep PmStepA PmStepA2 PmCertKitG PmAIss1 PmAEmbKit PmAEmbP1 PmAEmbP3 PmAEmbF PmAEmbG1 PmAEmbGStmts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan Require Import L5CoreB.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAEmbG2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAEmbGStmts.PMAEGS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0Aw"; "0Aw'"; "0Aw6"; "0B"; "1app"; "1cons"; "1length"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "3Z"; "0FF"]; ["0HI"; "0K"; "0L"; "0LBX"; "0LK"; "0LK'"; "4Model"; "4event"; "5bvmap"; "0M"; "0M'"; "0M6"; "0R"; "0R'"; "0R6"; "6credit"]; ["6regs_preserved"; "7adebit"; "7fframe"; "7model_rt"; "7ri_inv"; "7vml_of"; "8SCFG"; "9gmid"; ":ADDR_A"; ";PS"; ";pstate"; ";vec_at"; ";vec_own"; "<accA"; "<annA"; "<aobjA"]; ["<cfg"; "<entryA"; "<pm_scr"; "=opdel_spec"; ">FPState"; "?srealizes"; "@ahpres"; "@amodel_ok"; "Aloaded_segments"; "0SCFG_P"; "Bincl"; "Cadd"; "Cle"; "Clt"; "Cmodulo"; "Cmul"]; ["Cof_nat"; "Cpow"; "0ar"; "0b"; "0b'"; "0cr"; "0fx'"; "0fx6"; "0k"; "0m"; "0model"; "0model'"; "0model6"; "0n"; "0p1"; "0p2"]; ["0r"; "0sp"; "Dbv"; "0stk"; "0v"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
| solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
| solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
| solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PMAEBG2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac amod := match goal with H : ?x mod ?m = 0 |- ?x mod ?m = 0 => exact H end.
Ltac ftac := lazymatch goal with |- PMAEBP1.aligned _ _ => unfold PMAEBP1.aligned; first [amod | lia] | |- PMAEBP3.aligned _ _ => unfold PMAEBP3.aligned; first [amod | lia] end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.
Theorem grow2 : ltac2:(TCodec.tc2 tcn__PmAEmbG2 "VO&QCvQIvBvR2v@%544321'QD&Hy5'RByR0%211%5241'9y8%611%311p061'F'7'G%211!pU<21';'>%2211%811&Q2%:11&O'Q:%=11&Q4&4&Q<r>r=%3221rD%63>21rCrBr@rArG&Q5rF%211%@8Q=9876541(8%11O%511&QA&Q8rJrIr<z%685QIQH43F21&Q?+H%23?D1'=&QN+8%22I1%43Q:19&R0&6%12Q7J%311&R1+2%221Q0%<3QB41'<&QL%12DQ5+:%32Q71%5231%52HQ7&QM+Q?%=2<1%32Q;1%;251&Q7rQ1rQ0rOrMrLrKrHrEr?r;r:%<IS2S1S0;:9876Q=Q<5QGQE4QMQJQHQI3R0QOQ;21&Q0rQ9r6%3221&Q;&QH&Q=&Q>r2&QK+1%22E1rN(5(Q9%14QLEQJQJ%R31RF%43RG21%RE3RH61%?8>=<AO;81r7rQ2%@321QN&QFrQ8rQ7&QB%11R6(:rQ3%24S:S:1R6%RB1S:%C3S;21rQ;r8%<9T6T5;:Q=8321&Q3%1243&QJ%13S@5?%23SC@6&QGr9%221Q>rQ6%Q421Q3%S@241rQ=%SC3SK21rQ<&Q1&QO+Q0%RB2RA8%3221%53TJQF1%S?1S4%SM8TJ98QL2QKSI1'QE&Q6%11U0&Q@rQ4%26QJSIR31T0SOrQ?%74QL521p091p0H1p0L1p0N1p0Q11p0Q41p0QB1p0QF1p0R71pT:TG1p4TF1pQ<TE1pTHU11pQFU31pQLU91pT>U@1+e_W8%F6R>ERG1TDTC%J4R?H1ROp041p0RG1p0S51p0S61p0S=1p0SD1p0SM1p0T31p0T71p0T?1p0TC1p6U:1pTJUD1pQHUF1pQNUL1p8U@1pTLUA1pTDUB1pU0UC1pTNUD1pU2UE1pU4UF1pU8U@1pTBUH1pT8UI1pU:UJ1pT<UF1p2UJ1pQ:UI1pQ0UJ1pQ8UM1pQ4V21pTFV81pQDV:1pQJV@1pT@VG1p0VI1").
Proof.
intros DEL fx6 R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 m n B R6 M6 model6 Aw6 HH K0 ENT AOV V8 LEN Kr RP1 RP2 MID KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK0 & STKSH0). pose proof RAok as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
unfold PMAEGS.gmid, PMAEGS.SZ in MID.
destruct MID as (J2 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & JCS & W8 & W16 & W24 & W32 & W40 & W48 & W56 & W64 & W120 & W128 & W136 & W144 & W152
& W104 & W96 & W88 & W80 & W72 & WVB & WVE & WVC & ACCV6 & Q0 & Q4 & Q16 & Q5 & Q1 & bB & VBf & BDEF6 & QSH6 & BST6 & SLOT6
& HH6 & AM6 & MRT6 & IA6 & ASTK & STKSH & CHAIN6 & DK6).
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM6 as (Mh6 & MI6).
assert (KC : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
pose proof (PMAEBG1.pow2k10 k ltac:(lia)) as P2K. pose proof (PMAEBG1.pow2s k ltac:(lia)) as P2S.
remember (32 * 2 ^ k) as SZ eqn:ESZ.
set (LB := PM.vec_own b k ++ LBX) in *. set (LB2 := (B, 2 * SZ) :: LB) in *. set (cr2 := adebit L cr (2 * SZ)) in *.
assert (BIN : In (b, SZ) LB) by (left; unfold PM.vec_own; rewrite ESZ; reflexivity).
assert (BIN2 : In (B, 2 * SZ) LB2) by (left; reflexivity). assert (BIN2b : In (b, SZ) LB2) by (right; exact BIN).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & CB1 & CB2 & STOP & _).
destruct (PMAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b SZ HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & B16 & Bq5 & Bq6 & _ & Bq8).
pose proof (PMKA.aobj_of_aobjA FF v 24 AOV V8) as AOB.
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB2 FF LK cr2 Aw6 M6 model6 v 24 sp 12288 HH6 AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB2 FF LK cr2 Aw6 M6 model6 HH6) as (HOFF6 & VIS6 & VIMG6 & VFS6 & VBLK6 & VBSH6 & VFSSH6 & VSTSH6).
set (H6 := ahid Aw6 model6) in *. set (MV6 := mrestrict H6 M6) in *.
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as ST6. rewrite (L5A.aly_segs L C LYa) in ST6.
pose proof (L5A.statics_facts L C M6 LYa ST6) as (GOT6 & CSB6 & CUAR6 & _).
assert (X0 : L5.img_clear MV6 1228800 1261568) by (apply L5A.img_clear_mrestrict; exact GOT6).
assert (X1 : L5.u64_at RSEGS MV6 1289464 2147450880) by (apply (proj2 (L5A.u64_at_vis H6 M6 1289464 2147450880 (VIMG6 1289464 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB6).
assert (X2 : L5.u32_at RSEGS MV6 1289472 1) by (apply (proj2 (L5A.u32_at_vis H6 M6 1289472 1 (VIMG6 1289472 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR6).
assert (X3 : L5.writable RSEGS MV6 (sp - 4096) 4096).
{ apply (proj2 (L5A.writable_vis H6 M6 (sp - 4096) 4096 (VIS6 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5SAR.astk_writable ar M6 sp 12288); [exact ASTK| lia| lia| lia]. }
assert (X4 : L5KA.zeros_at MV6 (sp / 8 + 2147450368) 512).
{ intros i Hi. unfold MV6. rewrite (AsanAcct.mrestrict_visible H6 M6). apply (PMAEBF.stack_zeros12 M6 sp STKSH A16). exact Hi.
assert (AV : L5A.avis H6 (sp / 8 + 2147450368 + i) 1).
{ apply (VSTSH6 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
assert (X5 : L5KA.zeros_at MV6 (v / 8 + 2147450880) 3).
{ exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB2 FF LK cr2 Aw6 M6 model6 v 24 HH6 AOV V8 ltac:(lia) ltac:(reflexivity) ACCV6). }
assert (X6 : L5.writable RSEGS MV6 v 24).
{ apply (proj2 (L5A.writable_vis H6 M6 v 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
assert (VV : forall a v0, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M6 a v0 -> L5.u64_at RSEGS MV6 a v0).
{ intros a v0 H1 H2 X. apply (proj2 (L5A.u64_at_vis H6 M6 a v0 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))). exact X. }
assert (VS : forall a v0, sp - 4096 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M6 a v0 -> L5.u64_at RSEGS MV6 a v0).
{ intros a v0 H1 H2 X. apply (proj2 (L5A.u64_at_vis H6 M6 a v0 (VIS6 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
apply VV in WVB; [| lia| lia]. apply VV in WVE; [| lia| lia]. apply VV in WVC; [| lia| lia].
apply VS in W8; [| lia| lia].
apply VS in W16; [| lia| lia].
apply VS in W24; [| lia| lia].
apply VS in W32; [| lia| lia].
apply VS in W40; [| lia| lia].
apply VS in W48; [| lia| lia].
apply VS in W56; [| lia| lia].
apply VS in W64; [| lia| lia].
apply VS in W72; [| lia| lia].
apply VS in W80; [| lia| lia].
apply VS in W88; [| lia| lia].
apply VS in W96; [| lia| lia].
apply VS in W104; [| lia| lia].
apply VS in W120; [| lia| lia].
apply VS in W128; [| lia| lia].
apply VS in W136; [| lia| lia].
apply VS in W144; [| lia| lia].
apply VS in W152; [| lia| lia].
pose proof (PMAIS1.bvu (getr R (reg 1))) as UR1. pose proof (PMAIS1.bvu (getr R (reg 8))) as UR8. pose proof (PMAIS1.bvu (getr R (reg 9))) as UR9.
pose proof (PMAIS1.bvu (getr R (reg 18))) as UR18. pose proof (PMAIS1.bvu (getr R (reg 19))) as UR19. pose proof (PMAIS1.bvu (getr R (reg 20))) as UR20.
pose proof (PMAIS1.bvu (getr R (reg 21))) as UR21. pose proof (PMAIS1.bvu (getr R (reg 22))) as UR22.
assert (PI : exists fx7 R7 M7v, mem_grows MV6 M7v
/\ (forall a : word, ~ ((sp - 176) <= bv_unsigned a < (sp - 176) + 176) -> ~ ((v + 0) <= bv_unsigned a < (v + 0) + 24) -> M7v a = MV6 a)
/\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((sp - 176) <= i < (sp - 176) + 176) -> ~ ((v + 0) <= i < (v + 0) + 24) -> M7v (Z_to_bv 64 i) = MV6 (Z_to_bv 64 i))
/\ (msteps RSEGS (st fx6 R6 0xabce8 MV6) (st fx7 R7 0x7b124 M7v)
/\ (forall x, In x PMAEBP3.KS_aebI0 -> getr R7 (reg x) = getr R6 (reg x))
/\ getr R7 (reg 1) = Z_to_bv 64 704340 /\ getr R7 (reg 2) = Z_to_bv 64 (sp - 128) /\ getr R7 (reg 8) = Z_to_bv 64 (v + 8)
/\ getr R7 (reg 10) = Z_to_bv 64 B /\ getr R7 (reg 11) = Z_to_bv 64 (B + 2 * SZ) /\ getr R7 (reg 12) = Z_to_bv 64 (B + 2 * SZ)
/\ getr R7 (reg 13) = Z_to_bv 64 (B + (SZ + 32)) /\ getr R7 (reg 14) = Z_to_bv 64 ((v + 16) / 8)
/\ getr R7 (reg 18) = Z_to_bv 64 p2 /\ getr R7 (reg 19) = Z_to_bv 64 p1
/\ L5.u64_at RSEGS M7v (sp - 128) (v + 8) /\ L5.u64_at RSEGS M7v (sp - 120) 702524 /\ L5.u64_at RSEGS M7v (sp - 104) b
/\ L5.u64_at RSEGS M7v (sp - 80) (b + SZ) /\ L5.u64_at RSEGS M7v (v + 16) (B + 2 * SZ) /\ L5.u64_at RSEGS M7v (sp - 88) b
/\ L5.u64_at RSEGS M7v (v + 8) (B + (SZ + 32)) /\ L5.u64_at RSEGS M7v (sp - 96) b /\ L5.u64_at RSEGS M7v v B
/\ L5.u64_at RSEGS M7v (sp - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M7v (sp - 16) (bv_unsigned (getr R (reg 8)))
/\ L5.u64_at RSEGS M7v (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M7v (sp - 32) (bv_unsigned (getr R (reg 18)))
/\ L5.u64_at RSEGS M7v (sp - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M7v (sp - 48) (bv_unsigned (getr R (reg 20)))
/\ L5.u64_at RSEGS M7v (sp - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M7v (sp - 64) (bv_unsigned (getr R (reg 22)))
/\ L5.u64_at RSEGS M7v (sp - 72) v)).
{ clear KONT.
destruct KC as [Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|Ek]]]]]]]]]]; subst k; subst SZ.
- change (32 * 2 ^ 0 + 32) with 64 in W88. change (2 * (32 * 2 ^ 0)) with 64 in W80. change (32 * 2 ^ 0) with 32 in J20, W96, WVE, WVC. cfeed P (PMAEBP3.aebI0_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
- change (32 * 2 ^ 1 + 32) with 96 in W88. change (2 * (32 * 2 ^ 1)) with 128 in W80. change (32 * 2 ^ 1) with 64 in J20, W96, WVE, WVC. cfeed P (PMAEBP3.aebI1_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
- change (32 * 2 ^ 2 + 32) with 160 in W88. change (2 * (32 * 2 ^ 2)) with 256 in W80. change (32 * 2 ^ 2) with 128 in J20, W96, WVE, WVC. cfeed P (PMAEBP3.aebI2_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
- change (32 * 2 ^ 3 + 32) with 288 in W88. change (2 * (32 * 2 ^ 3)) with 512 in W80. change (32 * 2 ^ 3) with 256 in J20, W96, WVE, WVC. cfeed P (PMAEBP3.aebI3_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
- change (32 * 2 ^ 4 + 32) with 544 in W88. change (2 * (32 * 2 ^ 4)) with 1024 in W80. change (32 * 2 ^ 4) with 512 in J20, W96, WVE, WVC. cfeed P (PMAEBP3.aebI4_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
- change (32 * 2 ^ 5 + 32) with 1056 in W88. change (2 * (32 * 2 ^ 5)) with 2048 in W80. change (32 * 2 ^ 5) with 1024 in J20, W96, WVE, WVC. cfeed P (PMAEBP3.aebI5_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
- change (32 * 2 ^ 6 + 32) with 2080 in W88. change (2 * (32 * 2 ^ 6)) with 4096 in W80. change (32 * 2 ^ 6) with 2048 in J20, W96, WVE, WVC. cfeed P (PMAEBP3.aebI6_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
- change (32 * 2 ^ 7 + 32) with 4128 in W88. change (2 * (32 * 2 ^ 7)) with 8192 in W80. change (32 * 2 ^ 7) with 4096 in J20, W96, WVE, WVC. cfeed P (PMAEBP3.aebI7_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
- change (32 * 2 ^ 8 + 32) with 8224 in W88. change (2 * (32 * 2 ^ 8)) with 16384 in W80. change (32 * 2 ^ 8) with 8192 in J20, W96, WVE, WVC. cfeed P (PMAEBP3.aebI8_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
- change (32 * 2 ^ 9 + 32) with 16416 in W88. change (2 * (32 * 2 ^ 9)) with 32768 in W80. change (32 * 2 ^ 9) with 16384 in J20, W96, WVE, WVC. cfeed P (PMAEBP3.aebI9_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
- change (32 * 2 ^ 10 + 32) with 32800 in W88. change (2 * (32 * 2 ^ 10)) with 65536 in W80. change (32 * 2 ^ 10) with 32768 in J20, W96, WVE, WVC. cfeed P (PMAEBP3.aebI10_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P. }
clear KC X0 X1 X2 X3 X4 X5 X6 VV VS WVB WVE WVC W8 W16 W24 W32 W40 W48 W56 W64 W72 W80 W88 W96 W104 W120 W128 W136 W144 W152.
destruct PI as (fx7 & R7 & M7v & MG7 & _ & FZ7 & MS7 & KS7 & iR1 & iR2 & iR8 & iR10 & iR11 & iR12 & iR13 & iR14 & iR18 & iR19
& I128 & I120 & I104 & I80 & I16v & I88 & I8v & I96 & I0v & I8 & I16 & I24 & I32 & I40 & I48 & I56 & I64 & I72).
set (W7 := fun a => (sp - 176 <= a < sp - 176 + 176) \/ (v + 0 <= a < v + 0 + 24)).
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok LB2 FF LK cr2 Aw6 M6 model6 fx6 fx7 R6 0xabce8 R7 0x7b124 M7v W7 K HH6 AM6 MS7 MG7).
{ intros a Ha N. apply FZ7; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
{ intros a Ha [Wa|Wa].
- split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
- split; [apply (L5SAR.obj_client L ar LB2 FF 0 0 v 24 a AOB); lia| lia]. }
intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7 VV7.
pose proof AM7 as (Mh7 & MI7).
assert (ASTK7 : L5CA.astk ar M7 sp 12288) by (apply (L5SAR.astk_grows ar M6 M7 sp 12288 ASTK MGM7)).
assert (QSH7 : shadow_zero M7 B (2 * SZ / 8)).
{ intros j Hj. pose proof (PMAEBF.shadow_low B (2 * SZ) j ltac:(lia) ltac:(lia) Hj) as SL. unfold byte_at.
rewrite FR7; [apply QSH6; exact Hj| lia| unfold W7; intros [XW|XW]; [lia| destruct OBIG as [YW|YW]; lia]]. }
pose proof (HAJ.aex_annotate _ _ _ _ _ EXT) as ANN. unfold HAJ.annotate_spec in ANN.
cbn [PMA.EXT HAJ.ec_ann_pc HAJ.ec_ann_scr paa_annotate PMA.AAD AADDR_A] in ANN. rewrite (L5A.aly_segs L C LYa) in ANN.
apply (ANN fx7 R7 M7 model7 LB2 FF LK cr2 Aw6 K B (2 * SZ) (2 * SZ) (SZ + 32)); clear ANN.
{ exact HH7. }
{ exact Mh7. }
{ exact MI7. }
{ rewrite L5K.rl10. exact iR10. }
{ rewrite L5K.rl11. exact iR11. }
{ rewrite L5K.rl12. exact iR12. }
{ rewrite L5K.rl13. exact iR13. }
{ exact BIN2. }
{ exact Q16. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ split; [exact QSH7| intros j Hj; lia]. }
{ rewrite L5K.rl4, (KS7 4%nat) by inl. rewrite JCS by (right; left; reflexivity). exact Rtp. }
{ rewrite L5K.rl1, iR1. vm_compute. reflexivity. }
{ rewrite L5K.rl2, iR2, L5.unsigned_lit by lia.
apply (L5SAR.astack_ok_of_astk L ar C LYa M7 M7 sp 12288 128 2304 ASTK7 (fun x X => X)); [lia| lia| lia|].
replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
{ exact K0. }
intros fx8 R8 M8 model8 Aw8 RP8 ANN8 KEEP8 DSH8 SCR8 MRT8 INC8 MI8 HH8.
rewrite L5K.rl2, iR2, L5.unsigned_lit in KEEP8, SCR8 by lia. rewrite L5K.rl1, iR1.
assert (AM8 : L5CA.amodel_ok Aw8 model8) by (split; [rewrite (L5LZ.model_rt_halted model7 model8 MRT8); exact Mh7| exact MI8]).
assert (CS8 : forall k0, In k0 L5SAR.cs_all -> getr R8 (reg k0) = getr R7 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R7 R8 k0 RP8 Hk)).
assert (ASTK8 : L5CA.astk ar M8 sp 12288).
{ apply (L5SAR.astk_after_eq L ar C HI HIok LB2 FF LK cr2 Aw6 M7 M7 M8 _ sp 12288 (sp - 128) 2304 HH7 ASTK7 (fun x X => X)).
- intros a Ha Hs Hns. apply KEEP8; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
intros X. pose proof (PMAEK.in_shadow_range B (2 * SZ) a ltac:(lia) ltac:(lia) X). lia.
- exact SCR8.
- lia. - lia. - lia. }
assert (T87 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB2 FF 0 0 a -> ~ (sp - 2432 <= a < sp - 128) -> ~ in_shadow_of B (2 * SZ) a -> M8 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
{ intros a Ha Hc N1 N2. apply KEEP8; [exact Ha| apply (L5SAR.aclient_narrow L ar LB2 FF 0 0); [exact Hc| lia]| exact N2]. }
remember (2 ^ (k + 1)) as NC eqn:ENC.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB2 FF LK cr2 Aw8 M8 model8 HH8) as (HOFF8 & VIS8 & VIMG8 & VFS8 & VBLK8 & VBSH8 & VFSSH8 & VSTSH8).
set (H8 := ahid Aw8 model8) in *. set (MV8 := mrestrict H8 M8) in *.
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB2 FF LK cr2 Aw8 M8 model8 v 24 sp 12288 HH8 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF8 & OVIS8 & _).
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH8) as ST8. rewrite (L5A.aly_segs L C LYa) in ST8.
pose proof (L5A.statics_facts L C M8 LYa ST8) as (GOT8 & CSB8 & CUAR8 & _).
assert (Y0 : L5.img_clear MV8 1228800 1261568) by (apply L5A.img_clear_mrestrict; exact GOT8).
assert (Y1 : L5.u64_at RSEGS MV8 1289464 2147450880) by (apply (proj2 (L5A.u64_at_vis H8 M8 1289464 2147450880 (VIMG8 1289464 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB8).
assert (Y2 : L5.u32_at RSEGS MV8 1289472 1) by (apply (proj2 (L5A.u32_at_vis H8 M8 1289472 1 (VIMG8 1289472 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR8).
assert (Y3 : L5.writable RSEGS MV8 (sp - 4096) 4096).
{ apply (proj2 (L5A.writable_vis H8 M8 (sp - 4096) 4096 (VIS8 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5SAR.astk_writable ar M8 sp 12288); [exact ASTK8| lia| lia| lia]. }
assert (STKSH8 : shadow_zero M8 (sp - 12288) 1536).
{ intros j Hj. pose proof (PMAEBF.S_add8 (sp - 12288) j) as E. pose proof (PMAEBF.S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
unfold byte_at. rewrite E. rewrite T87; [| lia| apply (PMAEK.stack_sh_client L ar FF); lia| lia| apply (PMAEK.sh_apart B (2 * SZ)); lia].
rewrite FR7; [rewrite <- E; apply STKSH; exact Hj| lia| unfold W7; intros [XW|XW]; [lia| destruct OBIG as [YW|YW]; lia]]. }
assert (Y4 : L5KA.zeros_at MV8 (sp / 8 + 2147450368) 512).
{ intros i Hi. unfold MV8. rewrite (AsanAcct.mrestrict_visible H8 M8). apply (PMAEBF.stack_zeros12 M8 sp STKSH8 A16). exact Hi.
assert (AV : L5A.avis H8 (sp / 8 + 2147450368 + i) 1).
{ apply (VSTSH8 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
assert (ACCV8 : PMSPA.accA M8 v 24).
{ apply (PMFA.accA_agree M6 M8 v 24); [| exact ACCV6]. intros x Hx. pose proof (PMAEBF.S_range x ltac:(lia)) as SRx.
rewrite T87; [| lia| exact (PMAEK.frame_sh_client L ar FF v 24 x LB2 0 0 AOV Hx)| lia| apply (PMAEK.sh_apart B (2 * SZ) x); lia].
apply FR7; [lia| unfold W7; intros [XW|XW]; [lia| destruct OBIG as [YW|YW]; lia]]. }
assert (Y5 : L5KA.zeros_at MV8 (v / 8 + 2147450880) 3).
{ exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB2 FF LK cr2 Aw8 M8 model8 v 24 HH8 AOV V8 ltac:(lia) ltac:(reflexivity) ACCV8). }
assert (Y6 : L5.writable RSEGS MV8 v 24).
{ apply (proj2 (L5A.writable_vis H8 M8 v 24 OVIS8 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF8. lia. lia. }
assert (TV8 : forall a, v <= a < v + 24 -> M8 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
{ intros a Ha. apply T87; [lia| apply (L5SAR.obj_client L ar LB2 FF 0 0 v 24 a AOB); lia| lia|].
intros X. pose proof (PMAEK.in_shadow_range B (2 * SZ) a ltac:(lia) ltac:(lia) X). destruct OBIG as [YW|YW]; lia. }
assert (TS8 : forall a v0, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M7v a v0 -> L5.u64_at RSEGS MV8 a v0).
{ intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H8 M8 a v0 (VIS8 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.u64_at_agree RSEGS M7); [intros i Hi; apply T87; [lia| apply L5SAR.stack_client; lia| lia| intros XS; pose proof (PMAEK.in_shadow_range B (2 * SZ) i ltac:(lia) ltac:(lia) XS); lia]| lia| lia|].
apply (PMAIS1.vis_u64 _ _ _ _ _ VIS7); [apply VIS6; lia| lia| lia| exact X]. }
assert (TV8' : forall a v0, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M7v a v0 -> L5.u64_at RSEGS MV8 a v0).
{ intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H8 M8 a v0 ltac:(eapply L5A.avis_sub; [exact OVIS8| lia| lia]) ltac:(lia) ltac:(lia))).
apply (L5C.u64_at_agree RSEGS M7); [intros i Hi; apply TV8; lia| lia| lia|].
apply (PMAIS1.vis_u64 _ _ _ _ _ VIS7); [eapply L5A.avis_sub; [exact OVIS| lia| lia]| lia| lia| exact X]. }
pose proof (TS8 (sp - 8) _ ltac:(lia) ltac:(lia) I8) as V8x.
pose proof (TS8 (sp - 16) _ ltac:(lia) ltac:(lia) I16) as V16x.
pose proof (TS8 (sp - 24) _ ltac:(lia) ltac:(lia) I24) as V24x.
pose proof (TS8 (sp - 32) _ ltac:(lia) ltac:(lia) I32) as V32x.
pose proof (TS8 (sp - 40) _ ltac:(lia) ltac:(lia) I40) as V40x.
pose proof (TS8 (sp - 48) _ ltac:(lia) ltac:(lia) I48) as V48x.
pose proof (TS8 (sp - 56) _ ltac:(lia) ltac:(lia) I56) as V56x.
pose proof (TS8 (sp - 64) _ ltac:(lia) ltac:(lia) I64) as V64x.
pose proof (TS8 (sp - 72) _ ltac:(lia) ltac:(lia) I72) as V72x.
pose proof (TS8 (sp - 80) _ ltac:(lia) ltac:(lia) I80) as V80x.
pose proof (TS8 (sp - 88) _ ltac:(lia) ltac:(lia) I88) as V88x.
pose proof (TS8 (sp - 96) _ ltac:(lia) ltac:(lia) I96) as V96x.
pose proof (TS8 (sp - 104) _ ltac:(lia) ltac:(lia) I104) as V104x.
pose proof (TS8 (sp - 120) _ ltac:(lia) ltac:(lia) I120) as V120x.
pose proof (TS8 (sp - 128) _ ltac:(lia) ltac:(lia) I128) as V128x.
pose proof (TV8' v _ ltac:(lia) ltac:(lia) I0v) as VV0.
replace (B + (SZ + 32)) with (B + SZ + 32) in I8v by lia. pose proof (TV8' (v + 8) _ ltac:(lia) ltac:(lia) I8v) as VV8.
replace (B + 2 * SZ) with (B + 32 * NC) in I16v by lia. pose proof (TV8' (v + 16) _ ltac:(lia) ltac:(lia) I16v) as VV16.
assert (L2 : getr R8 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite CS8 by inl; exact iR2).
assert (L8 : getr R8 (reg 8) = Z_to_bv 64 (v + 8)) by (rewrite CS8 by inl; exact iR8).
assert (L9 : getr R8 (reg 9) = Z_to_bv 64 v) by (rewrite CS8 by inl; rewrite (KS7 9%nat) by inl; exact J9).
assert (L18 : getr R8 (reg 18) = Z_to_bv 64 p2) by (rewrite CS8 by inl; exact iR18).
assert (L19 : getr R8 (reg 19) = Z_to_bv 64 p1) by (rewrite CS8 by inl; exact iR19).
assert (L20 : getr R8 (reg 20) = Z_to_bv 64 SZ) by (rewrite CS8 by inl; rewrite (KS7 20%nat) by inl; exact J20).
assert (L21 : getr R8 (reg 21) = Z_to_bv 64 ((v + 8) / 8 + 2147450880)) by (rewrite CS8 by inl; rewrite (KS7 21%nat) by inl; exact J21).
assert (L22 : getr R8 (reg 22) = Z_to_bv 64 2147450880) by (rewrite CS8 by inl; rewrite (KS7 22%nat) by inl; exact J22).
cfeed P (PMAEBP1.aebJ_conc fx8 R8 MV8 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 37%nat => SZ | 40%nat => B | 42%nat => NC | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [ftac | assumption | lia]).
destruct P as (fx9 & R9 & M9v & MG9 & _ & FZ9 & MS9 & KS9 & jR1 & jR2 & jR9 & jR10 & jR11 & jR12 & jR13 & jR14 & jR15
& J8c & J16c & J24c & J32c & J40c & J48c & J56c & J64c & J104c & J96c & J88c & J80c & J72c).
clear Y0 Y1 Y2 Y3 Y4 Y5 Y6 TS8 TV8' VV0 VV8 VV16 V8x V16x V24x V32x V40x V48x V56x V64x V72x V80x V88x V96x V104x V120x V128x.
set (W9 := fun a => sp - 176 <= a < sp - 176 + 176).
apply (L5SAR.apiece L ar C HI LYa HIok LB2 FF LK cr2 Aw8 M8 model8 fx8 fx9 R8 0xabf54 R9 0xcea58 M9v W9 K HH8 AM8 MS9 MG9).
{ intros a Ha N. apply FZ9; [exact Ha| exact N]. }
{ intros a Ha Wa. unfold W9 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
intros M9 model9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9 VV9.
assert (ASTK9 : L5CA.astk ar M9 sp 12288) by (apply (L5SAR.astk_grows ar M8 M9 sp 12288 ASTK8 MGM9)).
unfold PMA.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in DEL. cbn [pa_opdel PMA.AD ADDR_A] in DEL.
apply (DEL fx9 R9 M9 model9 K LB2 FF LK Aw8 cr2 b SZ (sp - 112) 702544 HH9 AM9 K0).
{ exact BIN2b. }
{ rewrite L5K.rl10. exact jR10. }
{ rewrite L5K.rl1. exact jR1. }
{ split; [lia| reflexivity]. }
{ rewrite L5K.rl2. exact jR2. }
{ rewrite L5K.rl4, (KS9 4%nat) by inl. rewrite CS8 by inl. rewrite (KS7 4%nat) by inl. rewrite JCS by (right; left; reflexivity). exact Rtp. }
{ unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR. apply (L5SAR.astk_sub ar M9 M9 sp 12288 112 4096 ASTK9 (fun x X => X)); [lia| lia| lia|].
replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
intros fx10 R10 M10 model10 Aw10 RP10 HP10 MRT10 IA10 AM10 HH10.
unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HP10.
assert (ELB : lb_remove b LB2 = (B, 2 * SZ) :: LBX).
{ unfold LB2, LB, PM.vec_own. cbn [lb_remove fst app]. rewrite (proj2 (Z.eqb_neq B b)) by lia. rewrite Z.eqb_refl. reflexivity. }
rewrite ELB in HP10, HH10.
assert (CS10 : forall k0, In k0 L5SAR.cs_all -> getr R10 (reg k0) = getr R9 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R9 R10 k0 RP10 Hk)).
assert (KEEP10 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar ((B, 2 * SZ) :: LBX) FF (sp - 112) 4096 a -> M10 (Z_to_bv 64 a) = M9 (Z_to_bv 64 a)).
{ intros a Ha Hc. apply (proj1 HP10). split; [exact Ha|]. split; [exact Hc| intros rg []]. }
assert (ASTK10 : L5CA.astk ar M10 sp 12288).
{ apply (PMKA.astk_after_ahpres L ar ((B, 2 * SZ) :: LBX) FF M9 M10 sp 12288 (sp - 112) 4096 [] ASTK9 HP10); lia. }
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr2 Aw10 M10 model10 HH10) as (HOFF10 & VIS10 & VIMG10 & VFS10 & VBLK10 & VBSH10 & VFSSH10 & VSTSH10).
set (H10 := ahid Aw10 model10) in *. set (MV10 := mrestrict H10 M10) in *.
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr2 Aw10 M10 model10 v 24 sp 12288 HH10 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF10 & OVIS10 & _).
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH10) as ST10. rewrite (L5A.aly_segs L C LYa) in ST10.
pose proof (L5A.statics_facts L C M10 LYa ST10) as (GOT10 & CSB10 & CUAR10 & _).
assert (Z0' : L5.img_clear MV10 1228800 1261568) by (apply L5A.img_clear_mrestrict; exact GOT10).
assert (Z1' : L5.u64_at RSEGS MV10 1289464 2147450880) by (apply (proj2 (L5A.u64_at_vis H10 M10 1289464 2147450880 (VIMG10 1289464 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB10).
assert (Z2' : L5.u32_at RSEGS MV10 1289472 1) by (apply (proj2 (L5A.u32_at_vis H10 M10 1289472 1 (VIMG10 1289472 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR10).
assert (Z3' : L5.writable RSEGS MV10 (sp - 4096) 4096).
{ apply (proj2 (L5A.writable_vis H10 M10 (sp - 4096) 4096 (VIS10 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5SAR.astk_writable ar M10 sp 12288); [exact ASTK10| lia| lia| lia]. }
assert (CLs : forall a LBz, aclient L ar LBX FF 0 0 a -> In (B, 2 * SZ) LBz -> incl LBX LBz -> aclient L ar LBz FF 0 0 a).
{ intros a LBz Hc _ Hi. destruct Hc as [(q & Hq & Xq)|Hc]; [left; exists q; split; [apply Hi; exact Hq| exact Xq]|].
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|(q & Hq & Xq)]]]]]; [right; left; exact Hc| right; right; left; exact Hc| right; right; right; left; exact Hc
| right; right; right; right; left; exact Hc| right; right; right; right; right; left; exact Hc|].
do 6 right. exists q. split; [apply Hi; exact Hq| exact Xq]. }
assert (T9_10 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar ((B, 2 * SZ) :: LBX) FF 0 0 a -> ~ (sp - 4208 <= a < sp - 112) -> M10 (Z_to_bv 64 a) = M9 (Z_to_bv 64 a)).
{ intros a Ha Hc N. apply KEEP10; [exact Ha| apply (L5SAR.aclient_narrow L ar _ FF 0 0); [exact Hc| lia]]. }
assert (STKSH10 : shadow_zero M10 (sp - 12288) 1536).
{ intros j Hj. pose proof (PMAEBF.S_add8 (sp - 12288) j) as E. pose proof (PMAEBF.S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
unfold byte_at. rewrite E. rewrite T9_10; [| lia| apply (PMAEK.stack_sh_client L ar FF); lia| lia]. rewrite FR9; [| lia| unfold W9; lia]. rewrite <- E. apply STKSH8. exact Hj. }
assert (Z5' : L5KA.zeros_at MV10 (v / 8 + 2147450880) 3).
{ assert (ACC10 : PMSPA.accA M10 v 24).
{ apply (PMFA.accA_agree M8 M10 v 24); [| exact ACCV8]. intros x Hx. pose proof (PMAEBF.S_range x ltac:(lia)) as SRx.
rewrite T9_10; [| lia| exact (PMAEK.frame_sh_client L ar FF v 24 x _ 0 0 AOV Hx)| lia]. apply FR9; [lia| unfold W9; lia]. }
exact (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr2 Aw10 M10 model10 v 24 HH10 AOV V8 ltac:(lia) ltac:(reflexivity) ACC10). }
assert (Z4' : L5KA.zeros_at MV10 (sp / 8 + 2147450368) 512).
{ intros i Hi. unfold MV10. rewrite (AsanAcct.mrestrict_visible H10 M10). apply (PMAEBF.stack_zeros12 M10 sp STKSH10 A16). exact Hi.
assert (AV : L5A.avis H10 (sp / 8 + 2147450368 + i) 1).
{ apply (VSTSH10 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
assert (Z6' : L5.writable RSEGS MV10 v 24).
{ apply (proj2 (L5A.writable_vis H10 M10 v 24 OVIS10 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF10. lia. lia. }
assert (TV10 : forall a, v <= a < v + 24 -> M10 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
{ intros a Ha. rewrite T9_10; [| lia| apply (L5SAR.obj_client L ar _ FF 0 0 v 24 a AOB); lia| lia]. rewrite FR9; [| lia| unfold W9; lia]. apply TV8. lia. }
assert (Z7' : L5.u64_at RSEGS MV10 (v + 8) (B + SZ + 32)).
{ apply (proj2 (L5A.u64_at_vis H10 M10 (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS10| lia| lia]) ltac:(lia) ltac:(lia))).
apply (L5C.u64_at_agree RSEGS M7); [intros i Hi; apply TV10; lia| lia| lia|].
apply (PMAIS1.vis_u64 _ _ _ _ _ VIS7); [eapply L5A.avis_sub; [exact OVIS| lia| lia]| lia| lia| exact I8v]. }
assert (TS10 : forall a v0, sp - 112 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M9v a v0 -> L5.u64_at RSEGS MV10 a v0).
{ intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H10 M10 a v0 (VIS10 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.u64_at_agree RSEGS M9); [intros i Hi; apply T9_10; [lia| apply L5SAR.stack_client; lia| lia]| lia| lia|].
apply (PMAIS1.vis_u64 _ _ _ _ _ VIS9); [apply VIS8; lia| lia| lia| exact X]. }
pose proof (TS10 (sp - 8) _ ltac:(lia) ltac:(lia) J8c) as K8x.
pose proof (TS10 (sp - 16) _ ltac:(lia) ltac:(lia) J16c) as K16x.
pose proof (TS10 (sp - 24) _ ltac:(lia) ltac:(lia) J24c) as K24x.
pose proof (TS10 (sp - 32) _ ltac:(lia) ltac:(lia) J32c) as K32x.
pose proof (TS10 (sp - 40) _ ltac:(lia) ltac:(lia) J40c) as K40x.
pose proof (TS10 (sp - 48) _ ltac:(lia) ltac:(lia) J48c) as K48x.
pose proof (TS10 (sp - 56) _ ltac:(lia) ltac:(lia) J56c) as K56x.
pose proof (TS10 (sp - 64) _ ltac:(lia) ltac:(lia) J64c) as K64x.
assert (N2 : getr R10 (reg 2) = Z_to_bv 64 (sp - 112)) by (rewrite CS10 by inl; exact jR2).
assert (N8 : getr R10 (reg 8) = Z_to_bv 64 (v + 8)) by (rewrite CS10 by inl; rewrite (KS9 8%nat) by inl; exact L8).
assert (N9 : getr R10 (reg 9) = Z_to_bv 64 (B + SZ + 32)) by (rewrite CS10 by inl; exact jR9).
assert (N21 : getr R10 (reg 21) = Z_to_bv 64 ((v + 8) / 8 + 2147450880)) by (rewrite CS10 by inl; rewrite (KS9 21%nat) by inl; exact L21).
assert (N22 : getr R10 (reg 22) = Z_to_bv 64 2147450880) by (rewrite CS10 by inl; rewrite (KS9 22%nat) by inl; exact L22).
cfeed P (PMAEBP1.aebK_conc fx10 R10 MV10 (fun j => match j with 2%nat => sp | 33%nat => v | 41%nat => B + SZ + 32 | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) ltac:(first [ftac | assumption | lia]).
destruct P as (fx11 & R11 & M11v & MG11 & _ & FZ11 & MS11 & KS11 & kR1 & kR2 & kR8 & kR9 & kR10 & kR18 & kR19 & kR20 & kR21 & kR22 & K8v).
assert (R11ra : getr R11 (reg 1) = Z_to_bv 64 r) by (rewrite kR1, Z_to_bv_bv_unsigned; exact Rra).
pose proof (PMK.ret_to RSEGS fx11 R11 M11v 0xab884 (ltac:(oW' 0xab884%Z)) r (ltac:(oF' 0xab884%Z)) eq_refl (ltac:(oD' 0xab884%Z)) R11ra ltac:(lia) Hr2) as MS12.
set (W11 := fun a => v + 8 <= a < v + 8 + 8).
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr2 Aw10 M10 model10 fx10 fx11 R10 0xab850 R11 r M11v W11 K HH10 AM10 ltac:(eapply msteps_trans; [exact MS11| exact MS12]) MG11).
{ intros a Ha N. apply FZ11; [exact Ha| exact N]. }
{ intros a Ha Wa. unfold W11 in Wa. split; [apply (L5SAR.obj_client L ar _ FF 0 0 v 24 a AOB); lia| lia]. }
intros M11 model11 HH11 AM11 MRT11 HID11 VIS11 MGM11 FR11 VV11.
assert (TB11 : forall a, B <= a < B + 2 * SZ -> M11 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
{ intros a Ha. assert (CB : forall LBz, In (B, 2 * SZ) LBz -> aclient L ar LBz FF 0 0 a) by (intros LBz Hin; unfold aclient, aclient_g; left; exists (B, 2 * SZ); split; [exact Hin| cbn [fst snd]; lia]).
rewrite FR11; [| lia| unfold W11; lia]. rewrite T9_10; [| lia| apply CB; left; reflexivity| lia]. rewrite FR9; [| lia| unfold W9; lia].
rewrite T87; [| lia| apply CB; exact BIN2| lia|]. 2:{ intros X. pose proof (PMAEK.in_shadow_range B (2 * SZ) a ltac:(lia) ltac:(lia) X). destruct Q5 as (_ & [YW|YW] & _); lia. }
apply FR7; [lia| unfold W7; lia]. }
assert (SH11 : forall j, 0 <= j < 2 * SZ / 8 -> M11 (Z_to_bv 64 (S B + j)) = M8 (Z_to_bv 64 (S B + j))).
{ intros j Hj. pose proof (PMAEBF.shadow_low B (2 * SZ) j ltac:(lia) ltac:(lia) Hj) as SL.
rewrite FR11; [| lia| unfold W11; destruct OBIG as [YW|YW]; lia]. rewrite T9_10; [| lia| | lia]. 2:{ unfold aclient, aclient_g. do 6 right. exists (B, 2 * SZ). split; [left; reflexivity| cbn [fst snd]; apply PMAEK.sh_in; lia]. }
apply FR9; [lia| unfold W9; lia]. }
assert (TV11 : forall a, v <= a < v + 8 \/ v + 16 <= a < v + 24 -> M11 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
{ intros a Ha. rewrite FR11; [| lia| unfold W11; lia]. apply TV10. lia. }
apply (KONT fx11 R11 M11 model11 LK Aw10 B).
- apply L5SAR.preserved_by_index. intros k0 Hk.
assert (CH : forall k', In k' [3; 4; 23; 24; 25; 26; 27]%nat -> getr R11 (reg k') = getr R (reg k')).
{ intros k' Hk'. assert (Y : In k' PMAEBP1.KS_aebK /\ In k' L5SAR.cs_all /\ In k' PMAEBP1.KS_aebJ /\ In k' PMAEBP3.KS_aebI0)
by (destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; (split; [inl| split; [inl| split; inl]])).
destruct Y as (Yk1 & Yk2 & Yk3 & Yk4). rewrite (KS11 k' Yk1), (CS10 k' Yk2), (KS9 k' Yk3), (CS8 k' Yk2), (KS7 k' Yk4). apply JCS. exact Hk'. }
unfold L5SAR.cs_all in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hk]]]]]]]]]].
+ rewrite kR2. exact (eq_sym Rsp).
+ apply CH; left; reflexivity.
+ apply CH; right; left; reflexivity.
+ rewrite kR8, Z_to_bv_bv_unsigned; reflexivity.
+ rewrite kR9, Z_to_bv_bv_unsigned; reflexivity.
+ rewrite kR18, Z_to_bv_bv_unsigned; reflexivity.
+ rewrite kR19, Z_to_bv_bv_unsigned; reflexivity.
+ rewrite kR20, Z_to_bv_bv_unsigned; reflexivity.
+ rewrite kR21, Z_to_bv_bv_unsigned; reflexivity.
+ rewrite kR22, Z_to_bv_bv_unsigned; reflexivity.
+ apply CH; right; right; exact Hk.
- unfold PM.vec_at. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
rewrite <- ENC. replace (32 * NC) with (2 * SZ) by lia.
split. { apply (L5C.u64_at_agree RSEGS M7 M11); [intros i Hi; apply TV11; lia| lia| lia|].
apply (PMAIS1.vis_u64 _ _ _ _ _ VIS7); [eapply L5A.avis_sub; [exact OVIS| lia| lia]| lia| lia| exact I0v]. }
split. { replace (B + 32 * (Z.of_nat (length stk) + 1)) with (B + SZ + 32) by lia.
apply (PMAIS1.vis_u64 _ _ _ _ _ VIS11); [eapply L5A.avis_sub; [exact OVIS10| lia| lia]| lia| lia| exact K8v]. }
split. { apply (L5C.u64_at_agree RSEGS M7 M11); [intros i Hi; apply TV11; lia| lia| lia|].
replace (B + 2 * SZ) with (B + 32 * NC) by lia.
apply (PMAIS1.vis_u64 _ _ _ _ _ VIS7); [eapply L5A.avis_sub; [exact OVIS| lia| lia]| lia| lia| exact I16v]. }
split; [lia|]. split; [lia|]. split; [exact Q16|].
split. { intros i Hi. rewrite TB11 by lia. apply BDEF6. exact Hi. }
destruct ANN8 as (ZA8 & PA8).
split. { unfold PMSPA.accA. apply (PMFA.accA_agree M8 M11 B (32 * (Z.of_nat (length stk) + 1))).
- intros x Hx. assert (Sx : exists j, S x = S B + j /\ 0 <= j < 2 * SZ / 8).
{ exists (S x - S B). split; [lia|]. unfold S, SB. clear - Hx LEN P2K ESZ Q16 Q0. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
destruct Sx as (j & Ej & Hj). rewrite Ej. apply SH11. exact Hj.
- unfold PMSPA.accA. apply (L5CB.aacc_of_zero M8 B ((SZ + 32) / 8) B _ ZA8); [lia| lia| lia|].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
rewrite ESZ. replace (32 * 2 ^ k + 32) with (32 * (2 ^ k + 1)) by lia. rewrite PMAEBF.d32. lia. }
split. { replace (32 * (Z.of_nat (length stk) + 1)) with (SZ + 32) by lia.
apply (PMAEK.ann_agree M8 M11 B (SZ + 32) (2 * SZ)); [intros j Hj; apply SH11; exact Hj| lia| lia| split; [exact ZA8| exact PA8]]. }
intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [Hl|Hl].
+ rewrite app_nth1 by exact Hl. apply (PMF.pstate_at_agree RSEGS M6 M11); [lia| lia| | apply BST6; exact Hl].
intros x Hx. apply TB11. assert (Z.of_nat i + 1 <= Z.of_nat (length stk)) by lia. lia.
+ assert (Ei : i = length stk) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
replace (B + 32 * Z.of_nat (length stk)) with (B + SZ) by lia.
apply (PMF.pstate_at_agree RSEGS M6 M11); [lia| lia| intros x Hx; apply TB11; lia| exact SLOT6].
- apply (PMFA.accA_agree M8 M11 v 24); [| exact ACCV8]. intros x Hx. pose proof (PMAEBF.S_range x ltac:(lia)) as SRx.
rewrite FR11; [| lia| unfold W11; destruct OBIG as [YW|YW]; lia]. rewrite T9_10; [| lia| exact (PMAEK.frame_sh_client L ar FF v 24 x _ 0 0 AOV Hx)| lia].
apply FR9; [lia| unfold W9; lia].
- apply (L5SAR.ahpres_of L ar LBX FF sp 12288 _ M M11).
+ intros a (Ha & Hc & Ho).
assert (NV : ~ (v <= a < v + 24)) by (intros X; apply (Ho (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]).
assert (Hc0 : aclient L ar LBX FF 0 0 a) by exact (L5SAR.aclient_00 L ar LBX FF sp 12288 a Hc).
assert (HcB : aclient L ar LB FF 0 0 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, 32 * 2 ^ k)] FF 0 0 a Hc0)).
assert (NW : ~ (sp - 12288 <= a < sp)).
{ destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT ltac:(apply (L5SAR.aclient_appb L ar LBX [(b, 32 * 2 ^ k)] FF sp 12288 a Hc))) as [Z1|Z1]; lia. }
assert (NS : ~ in_shadow_of B (2 * SZ) a) by (exact (PMAEK.own_sh_notclient L ar C HI LY HIok B (2 * SZ) LB FF LK cr2 Aw6 M6 _ HH6 ltac:(lia) a 0 0 HcB)).
rewrite FR11; [| exact Ha| unfold W11; lia]. rewrite T9_10; [| exact Ha| apply (CLs a _ Hc0); [left; reflexivity| intros x Hx; right; exact Hx]| lia].
rewrite FR9; [| exact Ha| unfold W9; lia]. rewrite T87; [| exact Ha| apply (L5SAR.aclient_consb L ar LB FF (B, 2 * SZ) 0 0 a HcB)| lia| exact NS].
rewrite FR7; [| exact Ha| unfold W7; lia]. apply CHAIN6; [exact Ha| exact Hc0| exact NW| exact NV].
+ pose proof ASTK10 as (_ & _ & _ & _ & SD10 & _). apply (L5.defined_grows M10 M11 _ _ MGM11). exact SD10.
+ intros a Ha Hc HM.
assert (Hc0 : aclient L ar LBX FF 0 0 a) by exact (L5SAR.aclient_00 L ar LBX FF sp 12288 a Hc).
assert (HcB : aclient L ar LB FF 0 0 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, 32 * 2 ^ k)] FF 0 0 a Hc0)).
assert (NW : ~ (sp - 12288 <= a < sp)).
{ destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT ltac:(apply (L5SAR.aclient_appb L ar LBX [(b, 32 * 2 ^ k)] FF sp 12288 a Hc))) as [Z1|Z1]; lia. }
assert (NS : ~ in_shadow_of B (2 * SZ) a) by (exact (PMAEK.own_sh_notclient L ar C HI LY HIok B (2 * SZ) LB FF LK cr2 Aw6 M6 _ HH6 ltac:(lia) a 0 0 HcB)).
apply MGM11. rewrite T9_10; [| exact Ha| apply (CLs a _ Hc0); [left; reflexivity| intros x Hx; right; exact Hx]| lia].
apply MGM9. rewrite T87; [| exact Ha| apply (L5SAR.aclient_consb L ar LB FF (B, 2 * SZ) 0 0 a HcB)| lia| exact NS].
apply MGM7. exact (DK6 a Ha Hc0 HM).
- apply (L5LZ.model_rt_trans model model10 model11); [|exact MRT11]. apply (L5LZ.model_rt_trans model model9 model10); [|exact MRT10].
apply (L5LZ.model_rt_trans model model8 model9); [|exact MRT9]. apply (L5LZ.model_rt_trans model model7 model8); [|exact MRT8].
apply (L5LZ.model_rt_trans model model6 model7); [exact MRT6| exact MRT7].
- intros x Hx. exact Hx.
- intros x Hx. apply IA10. apply INC8. apply IA6. exact Hx.
- exact AM11.
- unfold PM.vec_own. cbn [app]. rewrite <- ENC. replace (32 * NC) with (2 * SZ) by lia. exact HH11.
Qed.
End Stage.
End PMAEBG2.
