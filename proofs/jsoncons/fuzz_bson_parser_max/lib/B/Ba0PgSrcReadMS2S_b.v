(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK_b Ba0PgSrcReadC_b.
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

Module PGSRDMS2S.
Abbreviation RSEGS := PGSRDK.RSEGS.
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
  PGSRDK.srd_ctx L ar HI 0 O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra ->
  PGSRDK.srd_frame L ar HI 0 R0 OB LBX FF LK Aw cr sp src F fl LK2 M2 model2 ->
  PGSRDK.srd_body L ar HI 0 O R0 M0 model0 OB LBX FF LK Aw sp src Wextra F M3 model3 LKc cr Ac ->
  V 2%nat = sp ->
  (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> V i = bv_unsigned (getr R0 (reg i))) ->
  L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 96) (V 26%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 88) (V 25%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 80) (V 24%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 72) (V 23%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 56) (V 21%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 48) (V 20%nat)
  /\ L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) ((V 2%nat) - 32) (V 18%nat).
Proof using All.
  intros CTX FR BI V2 VSV.
  pose proof FR as G. unfold PGSRDK.srd_frame in G.
  destruct G as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  assert (OWV : forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M3 a v -> L5.u64_at RSEGS (mrestrict (ahid Ac model3) M3) a v).
  { intros a v Ha Hb X. apply (L5C.u64_at_agree RSEGS M3 (mrestrict (ahid Ac model3) M3) a v); [| clear - Ha GSPC; lia| clear - Hb GSPC; lia| exact X].
    intros i Hi. apply AsanAcct.mrestrict_visible.
    apply (PGSRDC.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r src str sm Wextra F fl LK2 M2 model2 M3 model3 LKc Ac i CTX FR BI).
    left. clear - Hi Ha Hb. lia. }
  pose proof BI as BIu. unfold PGSRDK.srd_body in BIu.
  pose proof BIu as (_ & _ & _ & _ & _ & _ & _ & _ & OWN3 & _).
  destruct OWN3 as (W8 & W16 & W24 & W32 & W40 & W48 & W56 & W64 & W72 & W80 & W88 & W96 & W104).
  split; [rewrite V2, (VSV 26%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W96]|].
  split; [rewrite V2, (VSV 25%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W88]|].
  split; [rewrite V2, (VSV 24%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W80]|].
  split; [rewrite V2, (VSV 23%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W72]|].
  split; [rewrite V2, (VSV 21%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W56]|].
  split; [rewrite V2, (VSV 20%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W48]|].
  rewrite V2, (VSV 18%nat) by PGSRDC.inl; apply OWV; [clear; lia| clear; lia| exact W32].
Qed.

End G2.
End PGSRDMS2S.
