(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK16_b Ba0PgSrcReadC16_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmParStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcReadK_b PnASrcRead1_b PnASrcReadP_b Ba0_code_raf314_af318_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PnRunA_b PmAUarK_b PmAUar_b PnAReadCsK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGSRDMS2D16.
Abbreviation RSEGS := PGSRDK16.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Section G2.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma ms2_disj O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 p k :
  PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra ->
  getr R0 (reg 11) = Z_to_bv 64 p -> getr R0 (reg 12) = Z_to_bv 64 k -> 0 <= k < 2 ^ 64 ->
  PGSRDK16.srd_frame L ar HI 16 R0 OB LBX FF LK Aw cr sp src F fl LK2 M2 model2 ->
  forall i, p <= i < p + k ->
    ~ (sp - 160 - 16 <= i < sp) /\ ~ (F <= i < F + 128) /\ ~ (F / 8 + SB <= i < F / 8 + SB + 16)
    /\ ~ (PGS.ow_os O <= i < PGS.ow_os O + 296) /\ ~ ((PGS.ow_os O + 8) / 8 + SB <= i < (PGS.ow_os O + 8) / 8 + SB + 36)
    /\ ~ (fl <= i < fl + 1).
Proof using All.
  intros CTX R11 R12 Hkb G i Hi.
  destruct CTX as (OK & HH & AM & K0 & ENT & FRM & FRS & OFR & A10 & S32 & ARGS & WX & PA & IA & BASE & INCS & KONT).
  destruct ARGS as (p0 & k0 & A11 & A12 & Hk & DST). unfold PM.CHUNK in Hk.
  unfold PGSRDK16.srd_frame in G.
  destruct G as [Gk GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & _).
  unfold app_mem in FSAPP. destruct FSAPP as (FSA0 & FSAs & FSA47).
  assert (AO : PMSPA.aobjA FF (PGS.ow_os O) 296)
    by (apply (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O)); [exact OFR| exact LY1| exact LY2]).
  assert (OBIN : forall B m, In (B, m) OB -> In (B, m) (PM.src_own src ++ OB ++ LBX))
    by (intros B m Hin; apply in_or_app; right; apply in_or_app; left; exact Hin).
  assert (DQ : forall a, p0 <= a < p0 + k0 ->
      (in_block (PM.src_own src ++ OB ++ LBX) a \/ in_fframe FF a) /\ ~ (PGS.ow_os O <= a < PGS.ow_os O + 296)).
  { destruct DST as [(AOD & Hk8 & DD & AD & APF)|DW].
    - intros a Ha. split; [right; exact (PMASR1.in_fframe_of_aobjA FF p0 k0 a AOD Ha)| clear - Ha APF LY1 LY2; lia].
    - destruct (PGSA.oo_win _ _ _ _ _ _ OK M0 src OB p0 k0 PA DW)
        as (W0 & WD & [(B & m & BIN & WB1 & WB2)|(W1 & W2 & WL1 & WL2 & WL3 & WL4 & WL5)] & WACC).
      + pose proof (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M0 _ B m (PGS.ow_os O) 296 HH (OBIN B m BIN) AO) as APP.
        intros a Ha. split; [left; apply (PMASR1.in_block_of _ B m a (OBIN B m BIN)); clear - Ha WB1 WB2; lia| clear - Ha WB1 WB2 APP; lia].
      + intros a Ha. split; [right; exact (PMASR1.in_fframe_of_aobjA FF p0 k0 a (PGSKA.aobjA_sub FF (PGS.ow_lo O) (PGS.ow_hi O) p0 k0 OFR WL1 WL2) Ha)|].
        clear - Ha WL4; lia. }
  assert (APPA : forall a, in_block (PM.src_own src ++ OB ++ LBX) a \/ in_fframe FF a ->
      0 <= a < 2 ^ 47 /\ (a < BIGSHADOW_LO \/ BIGSHADOW_HI <= a)).
  { intros a [[[B m] [Hb Hb1]]|(f & Hf & Hf1 & _)].
    - destruct (WB _ Hb) as ((_ & _ & _ & _ & _ & TAPP) & _). cbn [fst snd] in Hb1, TAPP. unfold app_mem in TAPP. clear - Hb1 TAPP; lia.
    - destruct (WF f Hf) as (Y1 & Y2 & _). clear - Hf1 Y1 Y2 FSA0 FSAs FSA47; lia. }
  assert (P0 : 0 <= p0 /\ p0 + k0 <= 2 ^ 47).
  { destruct (APPA p0 (proj1 (DQ p0 ltac:(clear - Hk; lia)))) as (X1 & _).
    destruct (APPA (p0 + k0 - 1) (proj1 (DQ (p0 + k0 - 1) ltac:(clear - Hk; lia)))) as (X2 & _).
    clear - X1 X2; lia. }
  rewrite L5SAR.r11 in A11. rewrite L5SAR.r12 in A12. rewrite A11 in R11. rewrite A12 in R12.
  apply (f_equal bv_unsigned) in R11, R12.
  rewrite L5.unsigned_lit in R11 by (clear - P0 Hk; lia). rewrite L5.unsigned_lit in R12 by (clear - Hk; lia).
  rewrite (L5.unsigned_lit k Hkb) in R12.
  rewrite Z_to_bv_unsigned in R11. unfold bv_wrap, bv_modulus in R11. change (2 ^ Z.of_N 64) with (2 ^ 64) in R11.
  pose proof (Z.div_mod p (2 ^ 64) ltac:(clear - Hk; lia)) as PD. rewrite <- R11 in PD.
  assert (PI : p = p0 \/ i < 0 \/ 2 ^ 47 <= i).
  { destruct (Z.lt_trichotomy (p / 2 ^ 64) 0) as [Q|[Q|Q]]; [right; left| left| right; right]; clear - PD Q Hi R12 P0; lia. }
  pose proof (Z.div_mod (PGS.ow_os O + 8) 8 ltac:(clear - Hk; lia)) as DV1.
  pose proof (Z.mod_pos_bound (PGS.ow_os O + 8) 8 ltac:(clear - Hk; lia)) as DV2.
  assert (FB : ff_bytes 1 = 128) by reflexivity.
  assert (FB8 : ff_bytes 1 / 8 = 16) by reflexivity.
  assert (SBF : BIGSHADOW_LO <= SB /\ SB + 2 ^ 44 = BIGSHADOW_HI /\ BIGSHADOW_HI <= 2 ^ 47 /\ 0 <= BIGSHADOW_LO)
    by (unfold SB, BIGSHADOW_LO, BIGSHADOW_HI; lia).
  destruct PI as [PE|PI].
  - assert (Hi0 : p0 <= i < p0 + k0) by (clear - Hi PE R12; lia).
    destruct (DQ i Hi0) as (CL & NO). destruct (APPA i CL) as (IB & ISH).
    assert (AC : forall X sp' scr', aclient L ar (PM.src_own src ++ OB ++ LBX) (X ++ FF) sp' scr' i).
    { intros X sp' scr'. unfold aclient, aclient_g. destruct CL as [CB|(f & Hf & Hf1)]; [left; exact CB|].
      right; right; right; left. exists f. split; [apply in_or_app; right; exact Hf| exact Hf1]. }
    split; [intros Y; apply (GNCS i); [clear - Y; lia| exact (AC [] sp (PMSPA.pm_scr 4))]|].
    split; [intros Y; apply (GNCF i); [left; clear - Y FB; lia| exact (AC [] sp (PMSPA.pm_scr 4))]|].
    split; [intros Y; apply (GNCF i); [right; unfold S; clear - Y FB FB8 GF8; lia| exact (AC [] sp (PMSPA.pm_scr 4))]|].
    split; [exact NO|].
    split; [intros Y; clear - Y ISH SBF LY1 LY2 LY5 LY8 GSPT DV1 DV2; lia|].
    intros Y. apply GFLNC. replace fl with i by (clear - Y; lia). exact (AC [(F, 1, sp - 160 - 16 + 32)] 0 0).
  - split; [intros Y; clear - PI Y GSPC; lia|].
    split; [intros Y; clear - PI Y GFR FB; lia|].
    split; [intros Y; clear - PI Y GFR FB GF8 SBF; lia|].
    split; [intros Y; clear - PI Y LY1 LY2 LY5 LY8 GSPT; lia|].
    split; [intros Y; clear - PI Y SBF LY1 LY2 LY5 LY8 GSPT DV1 DV2; lia|].
    intros Y; clear - PI Y GFLR; lia.
Qed.

End G2.
End PGSRDMS2D16.
