(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK_b Ba0PgSrcReadC_b Ba0PgSrcReadMB_b Ba0PgSrcReadMS_b.
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

Module PGSRDMS1.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Lemma ms_g1_rng (R0 R R3 : bvmap 5 word) (MV : mem) (V : nat -> Z) (k rem sst len1 : Z) :
  V 38%nat = k ->
  (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
  PGSRDK.srd_stA V R MV -> PGSRDK.srd_pathG V R MV rem sst -> len1 = Z.min k rem ->
  forall i, In i [18; 19; 20; 21; 22; 23; 24; 25; 26; 39; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74]%nat ->
  0 <= PGSRDMS.vxMS V R3 len1 i < 2 ^ 64.
Proof.
  intros XV38 XVS STA PTH Hl i Hi.
  assert (B38 : 0 <= k < 2 ^ 64).
  { rewrite <- XV38. unfold PGSRDK.srd_stA in STA.
    repeat match type of STA with _ /\ _ => let H := fresh "S" in destruct STA as (H & STA) end.
    assumption. }
  destruct PTH as (V33 & R1 & B33 & _ & _). rewrite V33 in B33.
  cbn in Hi. repeat destruct Hi as [<-|Hi];
    [ first [ (cbn [PGSRDMS.vxMS PGSRDMB.vxC]; exact (bv_unsigned_in_range _ _))
            | (cbn [PGSRDMS.vxMS PGSRDMB.vxC]; match goal with |- 0 <= V ?j < _ => rewrite (XVS j ltac:(cbn; tauto)); exact (bv_unsigned_in_range _ _) end)
            | (cbn [PGSRDMS.vxMS]; rewrite Hl; clear - B38 R1 B33; lia) ] ..
    | destruct Hi ].
Qed.

Section Beq.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "S" in destruct PP as (H & PP) end.

Lemma ms_g1_ok : PGSRDMS.ms_g1_T L ar HI 0.
Proof using All.
  unfold PGSRDMS.ms_g1_T.
  intros O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 F fl LK2 M2 model2 FR
         fx R M model LKc Ac V BI V2 V36 V37 V38 V50 V51 VSV X3 X4 V34 V35 V45 IA STA PG
         len1 fx3 R3 M3 model3 HL BI3 DP OW3 IA3 BASE3 AGR G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 GK.
  intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
  pose proof (ms_g1_rng R0 R R3 _ V k rem sst len1 V38 VSV STA PG HL) as RNG.
  unfold PGSRDK.srd_pathG, PGSRDK.srd_pG in PG. destruct PG as (V33 & HR1 & B33 & _ & B35).
  unfold PGSRDK.srd_stA in STA. pdestr STA.
  unfold PGSRDMS.srd_stM_R.
  PGSRDC.sweep ltac:(first [(apply RNG; inl)
                    | (cbn [PGSRDMS.vxMS PGSRDMB.vxC];
                       first [assumption | exact (bv_unsigned_in_range _ _) | (symmetry; apply Z_to_bv_bv_unsigned)
                             | (rewrite (GK 27%nat) by inl; assumption)])]).
Qed.

End Beq.

End PGSRDMS1.
