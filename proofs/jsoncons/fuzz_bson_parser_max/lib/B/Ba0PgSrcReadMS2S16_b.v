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

Module PGSRDMS2S16.
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

Lemma ms2_saved O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M3 model3 LKc Ac (V : nat -> Z) :
  PGSRDK16.srd_ctx L ar HI 16 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra ->
  PGSRDK16.srd_frame L ar HI 16 R0 OB LBX FF LK Aw cr sp src F fl LK2 M2 model2 ->
  PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M3 model3 LKc cr Ac ->
  V 2%nat = sp - 16 ->
  (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
  L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 80) (V 26%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 72) (V 25%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 64) (V 24%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 56) (V 23%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 40) (V 21%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 32) (V 20%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 16) (V 18%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) (V 2%nat) (V 8%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) + 8) (V 1%nat).
Proof using All.
  intros CTX G BD XV2 XVS.
  pose proof BD as BD'. unfold PGSRDK16.srd_body, PMAUK.binv in BD'.
  destruct BD' as (HH3 & AM3 & MRT3 & INCA3 & INCL3 & ASTK3 & EK3 & DK3 & OWN3 & DSH3).
  pose proof ASTK3 as (A16 & SLO & SHI & SPT & SDEF & SUP).
  change (PMSPA.pm_scr 4) with 20480 in SLO.
  assert (VIS : forall i, sp - 160 - 16 <= i < sp -> mrestrict (ahid Ac model3) M3 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i)).
  { intros i Hi. unfold mrestrict.
    rewrite (PGSRDC16.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M3 model3 LKc Ac i CTX G BD (or_introl Hi)).
    reflexivity. }
  assert (OWNV : PNACSK.own sp R0 (mrestrict (ahid Ac model3) M3)).
  { apply (PNACSK.own_agree sp R0 M3 (mrestrict (ahid Ac model3) M3)); [clear - SLO SHI SPT; lia| clear - SHI SPT; lia| exact OWN3|].
    intros a Ha. unfold PNACSK.ocell in Ha. apply VIS. clear - Ha; lia. }
  destruct OWNV as (W1 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27).
  rewrite XV2, (XVS 26%nat), (XVS 25%nat), (XVS 24%nat), (XVS 23%nat), (XVS 21%nat), (XVS 20%nat), (XVS 18%nat), (XVS 8%nat), (XVS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity).
  replace (sp - 16 - 80) with (sp - 96) by (clear; lia). replace (sp - 16 - 72) with (sp - 88) by (clear; lia).
  replace (sp - 16 - 64) with (sp - 80) by (clear; lia). replace (sp - 16 - 56) with (sp - 72) by (clear; lia).
  replace (sp - 16 - 40) with (sp - 56) by (clear; lia). replace (sp - 16 - 32) with (sp - 48) by (clear; lia).
  replace (sp - 16 - 16) with (sp - 32) by (clear; lia).
  replace (sp - 16 + 8) with (sp - 8) by (clear; lia).
  split; [exact W26|]. split; [exact W25|]. split; [exact W24|]. split; [exact W23|]. split; [exact W21|]. split; [exact W20|]. split; [exact W18|]. split; [exact W8| exact W1].
Qed.

End G2.
End PGSRDMS2S16.
