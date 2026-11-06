(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5CoreKit L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAa PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCModelA PeCSpecsA PeCSpecsAa PeAEmbKitJ PeAEmuE PeAEmuF PeAEmuGStmts PeAEmuG1 PeAEmuG2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMAEU.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.

Theorem push_miu_ok : PMA.opnew_spec L ar HI -> PMA.opdel_spec L ar HI -> PECSA.push_miu_spec L ar HI.
Proof.
  intros NEW DEL. unfold PECSA.push_miu_spec, PMSAX.push_miu_spec, PMSAX.push_spec_at.
  intros fx R M model K LBX FF LK Aw cr v b k stk own c sp r HH AM K0 ENT FRS A10 AOV V8 ACCV PRE FULL K10 CELLS CRED KONT.
  cbn [paa_esp_miu PmLayoutA.AADDR_A] in *.
  destruct CELLS as (p1 & p2 & p3 & m & n & t & A11 & A12 & A13 & P14 & P24 & AC1 & AC2 & AC3 & AG1 & AG2 & AG3 & SB1 & SB2 & SB3 & U1 & U2 & U3 & RM & RN & RT & ->).
  destruct PRE as [(V0 & V8' & V16 & -> & -> & -> & ->) | (VEC & ->)].
  -
    cbn [app] in HH.
    apply (PMAEUE.empty L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr v sp r p1 p2 p3 m n t HH AM K0 ENT A10 AOV V8 ACCV V0 V8' V16
             A11 A12 A13 P14 P24 SB1 SB2 SB3 AG1 AG2 AG3 U1 U2 U3 RM RN RT (CRED (or_introl eq_refl))).
    intros fx' R' M' model' LK' Aw' b' RP VEC' ACC' HP MRT INC IA AM' HH'.
    apply (KONT fx' R' M' model' LK' Aw' b' 0 (adebit L cr 32) RP VEC' ACC'); try assumption.
    right. split; [left; reflexivity|]. split; reflexivity.
  -
    assert (BIN : In (b, 32 * 2 ^ k) (PM.vec_own b k ++ LBX)) by (left; reflexivity).
    destruct (PMAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b (32 * 2 ^ k) HH BIN) as (Bq0 & _).
    assert (Bnz : Z.eqb b 0 = false) by (apply Z.eqb_neq; lia).
    rewrite Bnz in CRED.
    assert (LENk : Z.of_nat (length stk) <= 2 ^ k) by (destruct VEC as (_ & _ & _ & _ & X & _); exact X).
    destruct (Z_lt_le_dec (Z.of_nat (length stk)) (2 ^ k)) as [LT | GE].
    +
      apply (PMAEUF.fast L ar C HI LY HIok EXT fx R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n t HH AM K0 ENT A10 AOV V8 ACCV VEC LT
               A11 A12 A13 P14 P24 SB1 SB2 SB3 AG1 AG2 AG3 U1 U2 U3 RM RN RT).
      intros fx' R' M' model' LK' Aw' RP VEC' ACC' HP MRT INC IA AM' HH'.
      apply (KONT fx' R' M' model' LK' Aw' b k cr RP VEC' ACC'); try assumption.
      left. split; [unfold PM.vec_own; discriminate|]. split; [exact LT|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
    +
      assert (EQ : Z.of_nat (length stk) = 2 ^ k) by lia.
      assert (Kle : k <= 10) by (apply K10; right; exact EQ).
      assert (Kr : 0 <= k <= 10) by (destruct VEC as (_ & _ & _ & X & _); lia).
      pose proof (CRED (or_intror EQ)) as CR.
      pose proof ENT as (_ & _ & _ & _ & _ & ASTK & _).
      assert (RP1 : 0 <= p1 < 2 ^ 47).
      { destruct (PMAEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) v p1 4 HH ASTK ltac:(unfold PMSPA.pm_scr; lia) AG1 ltac:(lia)) as (Pa0 & Pa1 & _). lia. }
      assert (RP2 : 0 <= p2 < 2 ^ 47).
      { destruct (PMAEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) v p2 4 HH ASTK ltac:(unfold PMSPA.pm_scr; lia) AG2 ltac:(lia)) as (Pb0 & Pb1 & _). lia. }
      assert (RP3 : 0 <= p3 < 2 ^ 47).
      { destruct (PMAEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) v p3 1 HH ASTK ltac:(unfold PMSPA.pm_scr; lia) AG3 ltac:(lia)) as (Pc0 & Pc1 & _). lia. }
      apply (PMAEUG1.grow1 L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n t HH AM K0 ENT A10 AOV V8 ACCV VEC EQ Kle
               A11 A12 A13 P14 P24 SB1 SB2 SB3 AG1 AG2 AG3 U1 U2 U3 RM RN RT CR).
      intros fx6 R6 M6 model6 Aw6 B MID.
      apply (PMAEUG2.grow2 L ar C HI LY HIok EXT DEL fx6 R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n t B R6 M6 model6 Aw6 HH K0 ENT AOV V8 EQ Kr
               RP1 RP2 RP3 MID).
      intros fx' R' M' model' LK' Aw' b' RP VEC' ACC' HP MRT INC IA AM' HH'.
      apply (KONT fx' R' M' model' LK' Aw' b' (k + 1) (adebit L cr (32 * 2 ^ (k + 1))) RP VEC' ACC'); try assumption.
      right. split; [right; exact EQ|]. rewrite Bnz. split; reflexivity.
Qed.
End WithHeap.
End PMAEU.
