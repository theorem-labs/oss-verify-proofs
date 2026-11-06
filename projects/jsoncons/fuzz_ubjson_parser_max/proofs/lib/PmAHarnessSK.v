(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsA
L5CoreA L5StepAR L5CoreBR L5ADetailHR L5AFrameKR HeapIfaceAJx PmLayout PmLayoutA PmModel PmModelFactsA PmStatics PmStaticsA PmSpecsA PmSpecsAa PmStepA
PmAHarnessStmts PmAHarnessKit.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAHarnessSK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAHarnessStmts.PMHAS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5AFrameKR.L5AFKR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreA.L5CA."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0Ac"; "0BX"; "1cons"; "1list"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "3Z"; "0F"; "0FF"; "0HI"; "0L"; "0LB"]; ["0LK"; "0LKc"; "4Model"; "5bvmap"; "0M"; "0Mc"; "0R"; "0Rc"; "6credit"; "7fframe"; "7shadow_zero"; "8ra_ok"; "9rinvH"; "9tfrk"; ":ADDR_A"; ";entryA"]; [";ffroomA"; ";ffrsA"; ";frame_okA"; ";pm_scr"; "<getr"; "=binv"; ">astk"; "?add"; "?div"; "?le"; "?modulo"; "?of_nat"; "?sub"; "0V2"; "0W"; "0ar"]; ["0cls"; "0crc"; "0h"; "0model"; "0modelc"; "0r"; "@Z_to_bv"; "@bv"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module PMHASK.
Import L5A. Import L5CA. Import L5SAR. Import PMHAS.
Abbreviation RSEGS := Asan.M.loaded_segments.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Stage.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (R : bvmap 5 word)
(V2 cls F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr : credit) (W : list L5.range).
Hypothesis G : L5AFKR.gctx L ar HI LB FF LK A (V2 + cls) 36864 (V2 - 128) (V2 - 128) (V2 + cls) (tocell (V2 + cls)) (tfrk (V2 + cls) R) F fl 4 LK2 M2 model2 cr.
Hypothesis CLS : cls = 0 \/ cls = 16.
Hypothesis V2R : 140735332487360 <= V2 <= 140737488355328.
Hypothesis V2S : V2 + cls <= 140737488355328.
Hypothesis V2A : V2 mod 32 = 0.
Hypothesis GP : getr R (reg 3) = Z_to_bv 64 (pa_gp PMA.AD).
Hypothesis TP : getr R (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis FFRS : forall f, In f FF -> V2 + cls + 32 <= ff_rs f.
Hypothesis ROOM : forall LKc, incl LKc LK -> NoDup (map ff_addr ((F, 4, V2 - 128 + 32) :: FF ++ LKc)) -> PMSPA.ffroomA 11 ((F, 4, V2 - 128 + 32) :: FF) LKc.
Hypothesis STKSH : shadow_zero M (V2 + cls - 36864) 4608.
Hypothesis WAPP : PMKA.wapp W.
Local Notation Bv := (L5AFKR.binv L ar HI M model LB FF LK A (V2 + cls) 36864 (V2 - 128) (tfrk (V2 + cls) R) F 4).
Local Notation FF' := ((F, 4, V2 - 128 + 32) :: FF).
Lemma callee_stack : ltac2:(TCodec.tc2 tcn__PmAHarnessSK "R<'4'7':%2211%411'QGyR0%211'5y8%511%311p051'B&I%?11&H&Q5v>vQ?v=vDvQCv?v<v@v0&Q7vQ=vQ@%3221+QTP0&Q<+T0%2261&MvF%2271v;+4vQ>r7r6r5r4r3r2%NFMLKJIHGFEA@=:987654321'8&Q9z%2215+;%4271%6231&Q6r8&Q3%11=%44Q83I1&J%M2K3&Q8+8%2261%53941%B271p0=1p0E1pS6R31p4R21pS4QG1pQ4QI1pS:QL1pQ<QN1p6R71").
Proof. intros BX Mc modelc LKc crc Ac h.
intros BI Hh. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
unfold PMSPA.pm_scr.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (AL1 : (V2 + cls - 36864) mod 8 = 0) by (clear - CLS V2A; lia).
assert (AL2 : (V2 - 128 - (12288 + 2048 * h)) mod 8 = 0) by (clear - V2A; lia).
assert (AL3 : (V2 + cls - (128 + cls)) mod 16 = 0) by (clear - V2A; lia).
assert (DV : (12288 + 2048 * h) / 8 = 1536 + 256 * h) by (clear; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
rewrite DV. split.
- replace (V2 - 128) with ((V2 + cls) - (128 + cls)) by (clear; lia).
apply (L5SAR.astk_sub ar Mc Mc (V2 + cls) 36864 (128 + cls) (12288 + 2048 * h) B6 (fun _ X => X)); [clear - CLS; lia| clear - Hh; lia| clear - CLS Hh; lia| exact AL3].
- apply (PMKA.shadow_zero_sub Mc (V2 + cls - 36864) 4608); [exact AL1| exact AL2| clear - CLS Hh; lia| clear - CLS Hh; lia| clear - Hh; lia|].
apply (PMKA.stksh_keepA L ar LB FF (V2 + cls) 36864 W M Mc B7 WAPP); [clear - SLO SPT; lia| clear - SLO SPT; lia| clear - V2S CLS; lia| exact AL1| lia| exact STKSH].
Qed.
Lemma callee_entry : ltac2:(TCodec.tc2 tcn__PmAHarnessSK "RJ'4'7':%2211%411'QGyR0%211'5y8%511%311p051'B&I%?11&H&Cy5%221<&Q5v>vQ?v=vDvQCv?v<v@v0&Q7vQ=vQ@%3221+QTP0&Q<+T0%2261&MvF%2271v;+4vQ>r9r8r7r6r5r4%NFMLKJIHGFEA@=:987654321&L%15=3ED;'9&Q4&QF&Q;u1%211%42Q91%62<1%62QG<%93QG21&K%11@'8&Q9z%221D+;%42F1%6231&O&Nr=%382QFQEN1Q6MLp051p0=1p0@1p0K1p0N1pS6R?1pS<R@1pQ@R01p4R@1pS4R51pQ4R71pS:R:1pQ<R<1p6RE1").
Proof. intros BX Mc modelc LKc crc Ac Rc r h.
intros BI RI R1 RA Hh. pose proof RI as (X2 & X8 & X9 & X18 & X19 & X20 & X24 & X25 & X3 & X4 & X27).
destruct (callee_stack BX Mc modelc LKc crc Ac h BI Hh) as (AS & SZ).
split; [rewrite L5K.rl1; exact R1|]. split; [exact RA|]. split; [rewrite L5K.rl2; exact X2|].
split; [rewrite L5K.rl3, X3; exact GP|]. split; [rewrite L5K.rl4, X4; exact TP|]. split; [exact AS| exact SZ].
Qed.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmAHarnessSK "R6'4'7':%2211%411'QGyR0%211'5y8%511%311p051'B&I%?11&H&Q5v>vQ?v=vDvQCv?v<v@v0&Q7vQ=vQ@%3221+QTP0&Q<+T0%2261&MvF%2271v;+4vQ>r7r6r5r4r3r2%NFMLKJIHGFEA@=:987654321&Q9+;%2241&Q0(3%QD2QBQC(6%14QEQEA@+Q0%N2G1%44QGQH31%7361Q3%93?1Bp0;1p0?1pS6QM1p4QL1pS4QA1pQ4QC1pS:QF1pQ<QH1p6R11")) (only parsing).
Variable BX : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable Mc : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable modelc : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable LKc : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable crc : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable Ac : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Variable h : ltac:(sec_ty2 constr:(SECT) 6%nat 0%nat).
Lemma callee_room : ltac:(sec_stmt2 constr:(SECT) 7%nat 0%nat).
Proof.
intros BI Hh. pose proof BI as (B1 & B2 & B3 & B4 & B5 & _).
assert (NDF : NoDup (map ff_addr (FF' ++ LKc))).
{ pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
intros k0 Hk0. specialize (ROOM LKc B5 NDF k0 Hk0). lia.
Qed.
End S.
Lemma callee_rs : ltac2:(TCodec.tc2 tcn__PmAHarnessSK "E&Q1(3'7':%2211%3212(6v;+4%346621&Q7&Q<vQ=+T0%3221+Q0%6221%;4=>81v<%B3>21%D216").
Proof. intros f [<-|Hf]; [cbn [ff_rs fst snd]; lia| specialize (FFRS f Hf); clear - Hf FFRS CLS; lia]. Qed.
Lemma callee_frame : ltac2:(TCodec.tc2 tcn__PmAHarnessSK "L'9':&Q:v;+QP0%3221z%73621&Q2(3'7%12::%221;(6+4%24>><1&Q7&Q<vQ=+T0%3221+Q0%6221%:4<F81v<%@3=21%B21Gp0D1").
Proof. intros H. split; [exists (V2 - 128 + 32); left; reflexivity| exact H]. Qed.
Lemma own_shz : ltac2:(TCodec.tc2 tcn__PmAHarnessSK "QJ'4'7':%2211%411'QGyR0%211'5y8%511%311p051'B&I%?11&H&Q5v>vQ?v=vDvQCv?v<v@v0&Q7vQ=vQ@%3221+QTP0&Q<+T0%2261&MvF%2271v;+4vQ>r6r5r4r3r2r1%NFMLKJIHGFEA@=:987654321&J+@%239@1p041p4Q@1pS4Q51pQ4Q71pS:Q:1pQ<Q<1p6QE1").
Proof. intros BX Mc modelc LKc crc Ac.
intros BI. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (AL1 : (V2 + cls - 36864) mod 8 = 0) by (clear - CLS V2A; lia).
assert (AL2 : (V2 - 128) mod 8 = 0) by (clear - V2A; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
apply (PMKA.shadow_zero_sub Mc (V2 + cls - 36864) 4608); [exact AL1| exact AL2| clear - CLS; lia| clear - CLS; lia| lia|].
apply (PMKA.stksh_keepA L ar LB FF (V2 + cls) 36864 W M Mc B7 WAPP); [clear - SLO SPT; lia| clear - SLO SPT; lia| clear - V2S CLS; lia| exact AL1| lia| exact STKSH].
Qed.
End Stage.
End SCFG_1.
End PMHASK.
