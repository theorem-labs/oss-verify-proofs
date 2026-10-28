(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8 PnModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAX_b PnSpecsAa_b
     PnAEmbKit_b PnSpecsAXR_b PnAEmbRE_b PnAEmbRF_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNAER.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.

Theorem push_root_fast_ok : PNSAXR.push_root_fast_spec RSEGS PMA.AD L ar HI 0xacf40.
Proof.
  unfold PNSAXR.push_root_fast_spec.
  intros fx R M model K LBX FF LK Aw cr v b k stk det sp r HH AM K0 ENT FRS A10 AOV V8 ACCV VEC LT BASE CELLS KONT.
  destruct det as ((m & n) & q).
  destruct CELLS as (p1 & p2 & p3 & A11 & A12 & A13 & (P14 & AC1 & AG1 & SB1) & (P24 & AC2 & AG2 & SB2) & (P34 & AC3 & AG3 & SB3) & U1 & U2 & U3 & RM & RN & RQ).
  cbn [fst snd] in U1, U2, U3, RM, RN, RQ. unfold PNSAX.mk_root in KONT. cbn [fst snd] in KONT.
  apply (PNAERF.fast L ar C HI LY HIok EXT fx R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n q HH AM K0 ENT A10 AOV V8 ACCV VEC LT
           A11 A12 A13 P14 P24 P34 SB1 SB2 SB3 AG1 AG2 AG3 U1 U2 U3 RM RN RQ BASE).
  intros fx' R' M' model' LK' Aw' RP VEC' VBLK ACC' BASE' HP MRT INC IA AM' HH'.
  exact (KONT fx' R' M' model' LK' Aw' RP VEC' VBLK ACC' BASE' HP MRT INC IA AM' HH').
Qed.
Theorem push_root_slow_ok : PMA.opnew_spec L ar HI -> PNSAXR.push_root_slow_spec RSEGS PMA.AD L ar HI 0xad11c.
Proof.
  intros NEW. unfold PNSAXR.push_root_slow_spec.
  intros fx R M model K LBX FF LK Aw cr v det sp r HH AM K0 ENT FRS A10 AOV V8 ACCV V0 V8' V16 BASE CELLS CRED KONT.
  destruct det as ((m & n) & q).
  destruct CELLS as (p1 & p2 & p3 & A11 & A12 & A13 & (P14 & AC1 & AG1 & SB1) & (P24 & AC2 & AG2 & SB2) & (P34 & AC3 & AG3 & SB3) & U1 & U2 & U3 & RM & RN & RQ).
  cbn [fst snd] in U1, U2, U3, RM, RN, RQ. unfold PNSAX.mk_root in KONT. cbn [fst snd] in KONT.
  apply (PNAERE.empty L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr v sp r p1 p2 p3 m n q HH AM K0 ENT A10 AOV V8 ACCV V0 V8' V16
           A11 A12 A13 P14 P24 P34 SB1 SB2 SB3 AG1 AG2 AG3 U1 U2 U3 RM RN RQ CRED BASE).
  intros fx' R' M' model' LK' Aw' b' RP VEC' ACC' BASE' HP MRT INC IA AM' HH' X10 Bl Bh VB.
  destruct VEC' as (W0 & _ & REST).
  exact (KONT fx' R' M' model' LK' Aw' b' RP X10 Bl Bh (conj W0 REST) VB ACC' BASE' HP MRT INC IA AM' HH').
Qed.
End WithHeap.
End PNAER.
