(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx IcptIfaceA
     L5Defs L5Core L5CoreKit L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PnLayoutA PmModel PmStatics PmStaticsA PmSpecsA PgV8 PnModel PnSpecsAX PnSpecsAa
     PnAEmbKit PnAEmbRE PnAEmbRF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNAER.
Abbreviation RSEGS := Asan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.

Theorem push_root_ok : PMA.opnew_spec L ar HI -> PNSAX.push_root_spec RSEGS PMA.AD L ar HI 0xabff8.
Proof.
  intros NEW. unfold PNSAX.push_root_spec, PNSAX.push_spec_at.
  intros fx R M model K LBX FF LK Aw cr v b k stk own det sp r HH AM K0 ENT FRS A10 AOV V8 ACCV PRE DOM K10 BASE CELLS CRED KONT.
  destruct det as ((m & n) & q).
  destruct CELLS as (p1 & p2 & p3 & A11 & A12 & A13 & (P14 & AC1 & AG1 & SB1) & (P24 & AC2 & AG2 & SB2) & (P34 & AC3 & AG3 & SB3) & U1 & U2 & U3 & RM & RN & RQ).
  cbn [fst snd] in U1, U2, U3, RM, RN, RQ. unfold PNSAX.mk_root in KONT. cbn [fst snd] in KONT.
  destruct PRE as [(V0 & V8' & V16 & -> & -> & -> & ->) | (VEC & ->)].
  - (* [comment removed for export] *)
    cbn [app] in HH.
    assert (CR : acredit_ok L cr 40).
    { pose proof (CRED (or_introl eq_refl)) as X. unfold PNSAX.k_next in X. cbn in X. exact X. }
    apply (PNAERE.empty L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr v sp r p1 p2 p3 m n q HH AM K0 ENT A10 AOV V8 ACCV V0 V8' V16
             A11 A12 A13 P14 P24 P34 SB1 SB2 SB3 AG1 AG2 AG3 U1 U2 U3 RM RN RQ CR BASE).
    intros fx' R' M' model' LK' Aw' b' RP VEC' ACC' BASE' HP MRT INC IA AM' HH'.
    apply (KONT fx' R' M' model' LK' Aw' b' 0 0 (adebit L cr 40) RP ltac:(lia) VEC' ACC' BASE'); try assumption.
    right. split; [left; reflexivity|]. split; reflexivity.
  - (* [comment removed for export] *)
    destruct DOM as [X | LT]; [unfold PNM.bvec_own in X; discriminate X|].
    apply (PNAERF.fast L ar C HI LY HIok EXT fx R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n q HH AM K0 ENT A10 AOV V8 ACCV VEC LT
             A11 A12 A13 P14 P24 P34 SB1 SB2 SB3 AG1 AG2 AG3 U1 U2 U3 RM RN RQ BASE).
    intros fx' R' M' model' LK' Aw' RP VEC' ACC' BASE' HP MRT INC IA AM' HH'.
    apply (KONT fx' R' M' model' LK' Aw' b k 0 cr RP ltac:(lia) VEC' ACC' BASE'); try assumption.
    left. split; [unfold PNM.bvec_own; discriminate|]. split; [exact LT|]. split; [reflexivity|]. split; reflexivity.
Qed.
End WithHeap.
End PNAER.
