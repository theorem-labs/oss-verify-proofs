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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAb PeSpecsBXJ PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeStepAB0 PeBEmbKitJ.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCEPushSpecsA PeEmbShKit PeBEPushF PeBEPushE PeBEPushGStmts PeBEPushG1 PeBEPushG2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PEBEPUSH.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT.

Theorem eslow_k_ok : PMSPA.opnew_spec RSEGS AD L ar HI -> PMSPA.opdel_spec RSEGS AD L ar HI -> PECEPX.eslow_k_spec RSEGS AD EE L ar HI.
Proof.
  intros NEW DEL. unfold PECEPX.eslow_k_spec, PECEPA.eslow_spec_at.
  intros fx R M model K LBX FF LK Aw cr ov fb en it sp r HH AM K0 ENT FRS A10 AOV O8 EA LENEQ LENB BASE CELLS CRED KONT.
  destruct CELLS as (pk & kd & A11 & P14 & ACC & EARG & SP1 & U1 & RKD & ->).
  destruct en as [b k stk d]. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in LENEQ, LENB, CRED, KONT.
  destruct EARG as (PL & APK).
  assert (AG1 : PMBEK.argp (ar_sptop ar) FF sp (ov + 32) pk 4) by (split; [exact PL| lia]).
  pose proof EA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EK & ELEN & _ & EKB & _). cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EK, ELEN, EKB.
  destruct (Z.eq_dec k 0) as [K0z|Knz].
  -
    subst k.
    assert (Estk : stk = []).
    { unfold PEC.ecap in LENEQ. cbn in LENEQ. destruct stk; [reflexivity| exfalso; cbn [length] in LENEQ; lia]. }
    change (PEC.ESZ * PEC.ecap (0 + 1)) with 24 in CRED, KONT. change (0 + 1) with 1 in KONT.
    apply (PEBEPE.empty L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr ov fb b stk d sp r pk kd HH AM K0 ENT A10 AOV O8 EA BASE
             A11 P14 SP1 AG1 APK U1 RKD CRED).
    intros fx' R' M' model' LK' Aw' B RP EA' BASE' HP MRT INC IA AM' HH' RA0.
    exact (KONT fx' R' M' model' LK' Aw' B RP EA' RA0 HP MRT INC IA AM' HH').
  -
    assert (Kp : 0 < k) by lia.
    change UbjRef.MAX_DEPTH with 1024 in LENB.
    assert (K11 : 0 < k <= 11) by (split; [exact Kp| apply PMESHK.ecap_le11; lia]).
    change PEC.ESZ with 24 in CRED.
    pose proof ENT as (_ & _ & _ & _ & _ & ASTK & _).
    assert (RPK : 0 <= pk < 2 ^ 47).
    { destruct (PMBEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) (ov + 32) pk 4 HH
                  ASTK ltac:(unfold PMSPA.pm_scr; lia) AG1 ltac:(lia)) as (Pa0 & Pa1 & _). lia. }
    apply (PEBEPG1.grow1 L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr ov fb b k stk d sp r pk kd HH AM K0 ENT A10 AOV O8 EA LENEQ K11 BASE
             A11 P14 SP1 AG1 APK U1 RKD CRED).
    intros fx8 R8 M8 model8 Aw8 B MID.
    apply (PEBEPG2.grow2 L ar C HI LY HIok EXT DEL fx8 R M model K LBX FF LK Aw cr ov fb b k stk d sp r pk kd B R8 M8 model8 Aw8 HH K0 ENT AOV O8 EA LENEQ K11
             RPK MID).
    intros fx' R' M' model' LK' Aw' RP EA' BASE' HP MRT INC IA AM' HH' RA0.
    exact (KONT fx' R' M' model' LK' Aw' B RP EA' RA0 HP MRT INC IA AM' HH').
Qed.
End WithHeap.
End PEBEPUSH.
