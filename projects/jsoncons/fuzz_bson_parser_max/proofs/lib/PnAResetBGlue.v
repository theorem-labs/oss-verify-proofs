(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core
     L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PnLayout PnLayoutA PmModel PnModel PmStatics PmStaticsA PnStatics PnStaticsA
     PmSpecs PmSpecsA PnSpecsAa PnSpecsAX PgSrc PgV8 PgSrcA PgV8A PnRun PnRunA PnRunAa PnAResetBStmts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNARBG.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section Glue.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).

(* [comment removed for export] *)
Definition head_stmt : Prop :=
  PNSAX.ann_shrink_v8_spec RSEGS PMA.AD L ar HI 0xab138 ->
  forall (fx : FPState) R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s,
    PNARBS.pre L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s ->
    (forall (fx1 : FPState) R1 M1 model1 LK1 Aw1, PNARBS.smid1 L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr sp fb s R1 M1 model1 LK1 Aw1 ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx1) R1 0xacaf0 M1 model1) K) ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R0 0xaca5c M0 model0) K.
(* [comment removed for export] *)
Definition mids_stmt : Prop :=
  PNSAX.ann_shrink_spec RSEGS PMA.AD L ar HI 0xaaecc ->
  forall (fx : FPState) R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s R1 M1 model1 LK1 Aw1,
    PNARBS.pre L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s ->
    PNARBS.smid1 L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr sp fb s R1 M1 model1 LK1 Aw1 ->
    (forall (fx2 : FPState) R2 M2 model2 LK2 Aw2, PNARBS.smid2 L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr sp fb s R2 M2 model2 LK2 Aw2 ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 0xacc58 M2 model2) K) ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R1 0xacaf0 M1 model1) K.
(* [comment removed for export] *)
Definition tail_stmt : Prop :=
  PNSAX.push_root_spec RSEGS PMA.AD L ar HI 0xabff8 ->
  forall (fx : FPState) R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s R2 M2 model2 LK2 Aw2,
    PNARBS.pre L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s ->
    PNARBS.smid2 L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr sp fb s R2 M2 model2 LK2 Aw2 ->
    PNARBS.kont L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr sp r fb s ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R2 0xacc58 M2 model2) K.

Theorem reset_of_stages : head_stmt -> mids_stmt -> tail_stmt ->
  PNSAX.ann_shrink_v8_spec RSEGS PMA.AD L ar HI 0xab138 -> PNSAX.ann_shrink_spec RSEGS PMA.AD L ar HI 0xaaecc ->
  PNSAX.push_root_spec RSEGS PMA.AD L ar HI 0xabff8 -> PNARBS.reset_spec L ar HI.
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
