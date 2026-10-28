(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core
     L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PnModel PmStatics PmStaticsA PnStatics PnStaticsA
     PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAX_b PnSpecsAXR_b PnSpecsAXC_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnAResetBStmts_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNARBG.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section Glue.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).

(* [comment removed for export] *)
Definition head_stmt : Prop :=
  PNSAXC.clear_v8_spec RSEGS PMA.AD L ar HI 0xabb00 ->
  forall (fx : FPState) R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s,
    PNARBS.pre L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s ->
    (forall (fx1 : FPState) R1 M1 model1 LK1 Aw1, PNARBS.smid1 L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr sp fb s R1 M1 model1 LK1 Aw1 ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx1) R1 0xadbd0 M1 model1) K) ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R0 0xadb68 M0 model0) K.
(* [comment removed for export] *)
Definition mids_stmt : Prop :=
  PNSAXC.vec_clear_spec RSEGS PMA.AD L ar HI 0xab740 ->
  forall (fx : FPState) R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s R1 M1 model1 LK1 Aw1,
    PNARBS.pre L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s ->
    PNARBS.smid1 L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr sp fb s R1 M1 model1 LK1 Aw1 ->
    (forall (fx2 : FPState) R2 M2 model2 LK2 Aw2, PNARBS.smid2 L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr sp fb s R2 M2 model2 LK2 Aw2 ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 0xadcfc M2 model2) K) ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R1 0xadbd0 M1 model1) K.
(* [comment removed for export] *)
Definition tail_stmt : Prop :=
  PNSAXR.push_root_fast_spec RSEGS PMA.AD L ar HI 0xacf40 ->
  forall (fx : FPState) R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s R2 M2 model2 LK2 Aw2,
    PNARBS.pre L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s ->
    PNARBS.smid2 L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr sp fb s R2 M2 model2 LK2 Aw2 ->
    PNARBS.kont L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R2 0xadcfc M2 model2) K.

Theorem reset_of_stages : head_stmt -> mids_stmt -> tail_stmt ->
  PNSAXC.clear_v8_spec RSEGS PMA.AD L ar HI 0xabb00 -> PNSAXC.vec_clear_spec RSEGS PMA.AD L ar HI 0xab740 ->
  PNSAXR.push_root_fast_spec RSEGS PMA.AD L ar HI 0xacf40 -> PNARBS.reset_spec L ar HI.
Proof.
  intros HEAD MIDS TAIL ASH8 ASH PSH. apply PNARBS.spec_of.
  intros fx R M model K LBX FF LK Aw cr sp r fb s PRE KONT.
  apply (HEAD ASH8 fx R M model K LBX FF LK Aw cr sp r fb s PRE).
  intros fx1 R1 M1 model1 LK1 Aw1 MID1.
  apply (MIDS ASH fx1 R M model K LBX FF LK Aw cr sp r fb s R1 M1 model1 LK1 Aw1 PRE MID1).
  intros fx2 R2 M2 model2 LK2 Aw2 MID2.
  exact (TAIL PSH fx2 R M model K LBX FF LK Aw cr sp r fb s R2 M2 model2 LK2 Aw2 PRE MID2 KONT).
Qed.
End Glue.
End PNARBG.
