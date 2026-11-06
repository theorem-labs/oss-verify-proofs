(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAb PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PeSpecsBXJ PeStepAB0 PeBEmbKitJ PeBSlowMiuE PeBSlowMiuGStmts PeBSlowMiuG1 PeBSlowMiuG2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBSLMIU.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT.

Theorem slow_miu_ok : PMB.opnew_spec L ar HI -> PMB.opdel_spec L ar HI -> PMBX.slow_miu_spec L ar HI.
Proof.
  intros NEW DEL. unfold PMBX.slow_miu_spec, PMSBX.slow_spec_at.
  intros fx R M model K LBX FF LK Aw cr v b k stk own c sp r HH AM K0 ENT FRS A10 AOV V8 ACCV PRE FULL K10 CELLS CRED KONT.
  cbn [paa_esp_miu PMB.AAD PmLayoutA.AADDR_B] in *.
  destruct CELLS as (p1 & p2 & p3 & m & n & t & A11 & A12 & A13 & P14 & P24 & AC1 & AC2 & AC3 & AG1 & AG2 & AG3 & SB1 & SB2 & SB3 & U1 & U2 & U3 & RM & RN & RT & ->).
  rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12. rewrite L5K.rl13 in A13.
  destruct PRE as [(V0 & V8' & V16 & -> & -> & -> & ->) | (VEC & ->)].
  -
    cbn [app] in HH.
    apply (PMBSLMUE.empty L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr v sp r p1 p2 p3 m n t HH AM K0 ENT A10 AOV V8 ACCV V0 V8' V16
             A11 A12 A13 P14 P24 SB1 SB2 SB3 AG1 AG2 AG3 U1 U2 U3 RM RN RT CRED).
    intros fx' R' M' model' LK' Aw' b' RP A0 VEC' ACC' HP MRT INC IA AM' HH'.
    apply (KONT fx' R' M' model' LK' Aw' b' 0 (adebit L cr 32) RP VEC' ACC'); try assumption; try reflexivity.
    all: try (rewrite L5K.rl10; exact A0).
  -
    assert (BIN : In (b, 32 * 2 ^ k) (PM.vec_own b k ++ LBX)) by (left; reflexivity).
    destruct (PMBEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b (32 * 2 ^ k) HH BIN) as (Bq0 & _).
    assert (Bnz : Z.eqb b 0 = false) by (apply Z.eqb_neq; lia).
    rewrite Bnz in CRED.
    assert (EQ : Z.of_nat (length stk) = 2 ^ k) by (destruct FULL as [X|X]; [unfold PM.vec_own in X; discriminate| exact X]).
    assert (Kr : 0 <= k <= 10) by (destruct VEC as (_ & _ & _ & X & _); lia).
    pose proof ENT as (_ & _ & _ & _ & _ & ASTK & _).
      assert (RP1 : 0 <= p1 < 2 ^ 47).
      { destruct (PMBEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) v p1 4 HH
                    ASTK ltac:(unfold PMSPA.pm_scr; lia) AG1 ltac:(lia)) as (Pa0 & Pa1 & _). lia. }
      assert (RP2 : 0 <= p2 < 2 ^ 47).
      { destruct (PMBEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) v p2 4 HH
                    ASTK ltac:(unfold PMSPA.pm_scr; lia) AG2 ltac:(lia)) as (Pb0 & Pb1 & _). lia. }
    assert (RP3 : 0 <= p3 < 2 ^ 47).
      { destruct (PMBEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) v p3 1 HH
                    ASTK ltac:(unfold PMSPA.pm_scr; lia) AG3 ltac:(lia)) as (Pc0 & Pc1 & _). lia. }
    apply (PMBSLMUG1.grow1 L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n t HH AM K0 ENT A10 AOV V8 ACCV VEC EQ K10
             A11 A12 A13 P14 P24 SB1 SB2 SB3 AG1 AG2 AG3 U1 U2 U3 RM RN RT CRED).
    intros fx6 R6 M6 model6 Aw6 B MID.
    apply (PMBSLMUG2.grow2 L ar C HI LY HIok EXT DEL fx6 R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n t B R6 M6 model6 Aw6 HH K0 ENT AOV V8 EQ Kr
             RP1 RP2 RP3 MID).
    intros fx' R' M' model' LK' Aw' b' RP A0 VEC' ACC' HP MRT INC IA AM' HH'.
    apply (KONT fx' R' M' model' LK' Aw' b' (k + 1) (adebit L cr (32 * 2 ^ (k + 1))) RP VEC' ACC'); try assumption; try reflexivity.
    all: try (rewrite Bnz; reflexivity).
    all: try (rewrite L5K.rl10, A0; f_equal; rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add, EQ; lia).
Qed.
End WithHeap.
End PMBSLMIU.
