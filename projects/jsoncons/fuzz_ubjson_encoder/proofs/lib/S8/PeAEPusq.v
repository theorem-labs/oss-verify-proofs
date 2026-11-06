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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCModelA PeStepA PeAEmbKitJ.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCEPushSpecsA PeAEPush PeAEPusqF PeAEPusqE PeAEPusqGStmts PeAEPusqG1 PeAEPusqG2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PEAEQPUSH.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.

Theorem epush_kl_ok : PMSPA.opnew_spec RSEGS AD L ar HI -> PMSPA.opdel_spec RSEGS AD L ar HI -> PECEPX.epush_kl_spec RSEGS AD EE L ar HI.
Proof.
  intros NEW DEL. unfold PECEPX.epush_kl_spec, PECEPA.epush_spec_at.
  intros fx R M model K LBX FF LK Aw cr ov fb en it sp r HH AM K0 ENT FRS A10 AOV O8 EA LENB BASE CELLS CRED KONT.
  destruct CELLS as (pk & pl & kd & ln & A11 & A12 & P14 & P18 & ACC & ACC2 & EARG & EARG2 & SP1 & SP2 & U1 & U2 & RKD & RLN & ->).
  destruct en as [b k stk d]. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in LENB, CRED, KONT.
  destruct EARG as (PL & APK). destruct EARG2 as (PL2 & APL).
  assert (AG1 : PMAEK.argp (ar_sptop ar) FF sp (ov + 32) pk 4) by (split; [exact PL| lia]).
  assert (AG2 : PMAEK.argp (ar_sptop ar) FF sp (ov + 32) pl 8) by (split; [exact PL2| lia]).
  pose proof EA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EK & ELEN & _ & EKB & _). cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EK, ELEN, EKB.
  destruct (Z.eq_dec k 0) as [K0z|Knz].
  -
    subst k.
    assert (Estk : stk = []).
    { unfold PEC.ecap in ELEN. cbn in ELEN. destruct stk; [reflexivity| exfalso; cbn [length] in ELEN; lia]. }
    assert (CR : acredit_ok L cr 24).
    { specialize (CRED ltac:(rewrite Estk; reflexivity)). exact CRED. }
    apply (PEAEQE.empty L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr ov fb b stk d sp r pk pl kd ln HH AM K0 ENT A10 AOV O8 EA BASE
             A11 A12 P14 P18 SP1 SP2 AG1 AG2 APK APL U1 U2 RKD RLN CR).
    intros fx' R' M' model' LK' Aw' B RP EA' BASE' HP MRT INC IA AM' HH'.
    apply (KONT fx' R' M' model' LK' Aw' (PEC.ENC B 1 (stk ++ [EI kd ln 0]) d) (adebit L cr 24) RP EA'); try assumption.
    + reflexivity.
    + reflexivity.
    + right. cbn [PEC.en_b PEC.en_k PEC.en_stk]. rewrite Estk. split; [reflexivity|]. split; reflexivity.
  - assert (Kp : 0 < k) by lia.
    destruct (Z_lt_le_dec (Z.of_nat (length stk)) (PEC.ecap k)) as [LT | GE].
    +
      apply (PEAEQF.fast L ar C HI LY HIok EXT fx R M model K LBX FF LK Aw cr ov fb b k stk d sp r pk pl kd ln HH AM K0 ENT A10 AOV O8 EA LT LENB BASE
               A11 A12 P14 P18 SP1 SP2 AG1 AG2 APK APL U1 U2 RKD RLN).
      intros fx' R' M' model' LK' Aw' RP EA' BASE' HP MRT INC IA AM' HH'.
      apply (KONT fx' R' M' model' LK' Aw' (PEC.ENC b k (stk ++ [EI kd ln 0]) d) cr RP EA'); try assumption.
      * reflexivity.
      * reflexivity.
      * left. cbn [PEC.en_b PEC.en_k PEC.en_stk]. split; [exact LT|]. split; [reflexivity|]. split; reflexivity.
    +
      assert (EQ : Z.of_nat (length stk) = PEC.ecap k) by lia.
      change UbjRef.MAX_DEPTH with 1024 in LENB.
      assert (K11 : 0 < k <= 11) by (split; [exact Kp| apply PEAEPUSH.ecap_le11; lia]).
      pose proof (CRED EQ) as CR. change PEC.ESZ with 24 in CR.
      pose proof ENT as (_ & _ & _ & _ & _ & ASTK & _).
      assert (RPK : 0 <= pk < 2 ^ 47).
      { destruct (PMAEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) (ov + 32) pk 4 HH
                    ASTK ltac:(unfold PMSPA.pm_scr; lia) AG1 ltac:(lia)) as (Pa0 & Pa1 & _). lia. }
      assert (RPL : 0 <= pl < 2 ^ 47).
      { destruct (PMAEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) (ov + 32) pl 8 HH
                    ASTK ltac:(unfold PMSPA.pm_scr; lia) AG2 ltac:(lia)) as (Pa0 & Pa1 & _). lia. }
      apply (PEAEQG1.grow1 L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr ov fb b k stk d sp r pk pl kd ln HH AM K0 ENT A10 AOV O8 EA EQ K11 BASE
               A11 A12 P14 P18 SP1 SP2 AG1 AG2 APK APL U1 U2 RKD RLN CR).
      intros fx8 R8 M8 model8 Aw8 B MID.
      apply (PEAEQG2.grow2 L ar C HI LY HIok EXT DEL fx8 R M model K LBX FF LK Aw cr ov fb b k stk d sp r pk pl kd ln B R8 M8 model8 Aw8 HH K0 ENT AOV O8 EA EQ K11
               RPK RPL MID).
      intros fx' R' M' model' LK' Aw' RP EA' BASE' HP MRT INC IA AM' HH'.
      apply (KONT fx' R' M' model' LK' Aw' (PEC.ENC B (k + 1) (stk ++ [EI kd ln 0]) d) (adebit L cr (PEC.ESZ * PEC.ecap (k + 1))) RP EA'); try assumption.
      * reflexivity.
      * reflexivity.
      * right. cbn [PEC.en_b PEC.en_k PEC.en_stk]. split; [exact EQ|]. split; reflexivity.
Qed.
End WithHeap.
End PEAEQPUSH.
