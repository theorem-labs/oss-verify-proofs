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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCEPushSpecsA PeAEPushF PeAEPushE PeAEPushGStmts PeAEPushG1 PeAEPushG2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PEAEPUSH.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.

Lemma ecap_le11 k : 0 < k -> PEC.ecap k <= 1024 -> k <= 11.
Proof.
  intros Hk Hc. destruct (Z_le_gt_dec k 11) as [X|X]; [exact X|]. exfalso.
  unfold PEC.ecap in Hc. replace (k =? 0) with false in Hc by (symmetry; apply Z.eqb_neq; lia).
  assert (Y : 2 ^ 11 <= 2 ^ (k - 1)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 11) with 2048 in Y. lia.
Qed.

Theorem epush_k_ok : PMSPA.opnew_spec RSEGS AD L ar HI -> PMSPA.opdel_spec RSEGS AD L ar HI -> PECEPX.epush_k_spec RSEGS AD EE L ar HI.
Proof.
  intros NEW DEL. unfold PECEPX.epush_k_spec, PECEPA.epush_spec_at.
  intros fx R M model K LBX FF LK Aw cr ov fb en it sp r HH AM K0 ENT FRS A10 AOV O8 EA LENB BASE CELLS CRED KONT.
  destruct CELLS as (pk & kd & A11 & P14 & ACC & EARG & SP1 & U1 & RKD & ->).
  destruct en as [b k stk d]. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in LENB, CRED, KONT.
  destruct EARG as (PL & APK).
  assert (AG1 : PMAEK.argp (ar_sptop ar) FF sp (ov + 32) pk 4) by (split; [exact PL| lia]).
  pose proof EA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EK & ELEN & _ & EKB & _). cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EK, ELEN, EKB.
  destruct (Z.eq_dec k 0) as [K0z|Knz].
  -
    subst k.
    assert (Estk : stk = []).
    { unfold PEC.ecap in ELEN. cbn in ELEN. destruct stk; [reflexivity| exfalso; cbn [length] in ELEN; lia]. }
    assert (CR : acredit_ok L cr 24).
    { specialize (CRED ltac:(rewrite Estk; reflexivity)). exact CRED. }
    apply (PEAEPE.empty L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr ov fb b stk d sp r pk kd HH AM K0 ENT A10 AOV O8 EA BASE
             A11 P14 SP1 AG1 APK U1 RKD CR).
    intros fx' R' M' model' LK' Aw' B RP EA' BASE' HP MRT INC IA AM' HH'.
    apply (KONT fx' R' M' model' LK' Aw' (PEC.ENC B 1 (stk ++ [EI kd 0 0]) d) (adebit L cr 24) RP EA'); try assumption.
    + reflexivity.
    + reflexivity.
    + right. cbn [PEC.en_b PEC.en_k PEC.en_stk]. rewrite Estk. split; [reflexivity|]. split; reflexivity.
  - assert (Kp : 0 < k) by lia.
    destruct (Z_lt_le_dec (Z.of_nat (length stk)) (PEC.ecap k)) as [LT | GE].
    +
      apply (PEAEPF.fast L ar C HI LY HIok EXT fx R M model K LBX FF LK Aw cr ov fb b k stk d sp r pk kd HH AM K0 ENT A10 AOV O8 EA LT LENB BASE
               A11 P14 SP1 AG1 APK U1 RKD).
      intros fx' R' M' model' LK' Aw' RP EA' BASE' HP MRT INC IA AM' HH'.
      apply (KONT fx' R' M' model' LK' Aw' (PEC.ENC b k (stk ++ [EI kd 0 0]) d) cr RP EA'); try assumption.
      * reflexivity.
      * reflexivity.
      * left. cbn [PEC.en_b PEC.en_k PEC.en_stk]. split; [exact LT|]. split; [reflexivity|]. split; reflexivity.
    +
      assert (EQ : Z.of_nat (length stk) = PEC.ecap k) by lia.
      change UbjRef.MAX_DEPTH with 1024 in LENB.
      assert (K11 : 0 < k <= 11) by (split; [exact Kp| apply ecap_le11; lia]).
      pose proof (CRED EQ) as CR. change PEC.ESZ with 24 in CR.
      pose proof ENT as (_ & _ & _ & _ & _ & ASTK & _).
      assert (RPK : 0 <= pk < 2 ^ 47).
      { destruct (PMAEK.arg_facts L ar C HI LY HIok _ FF LK cr Aw M _ sp (PMSPA.pm_scr 0) (ov + 32) pk 4 HH
                    ASTK ltac:(unfold PMSPA.pm_scr; lia) AG1 ltac:(lia)) as (Pa0 & Pa1 & _). lia. }
      apply (PEAEPG1.grow1 L ar C HI LY HIok EXT NEW fx R M model K LBX FF LK Aw cr ov fb b k stk d sp r pk kd HH AM K0 ENT A10 AOV O8 EA EQ K11 BASE
               A11 P14 SP1 AG1 APK U1 RKD CR).
      intros fx8 R8 M8 model8 Aw8 B MID.
      apply (PEAEPG2.grow2 L ar C HI LY HIok EXT DEL fx8 R M model K LBX FF LK Aw cr ov fb b k stk d sp r pk kd B R8 M8 model8 Aw8 HH K0 ENT AOV O8 EA EQ K11
               RPK MID).
      intros fx' R' M' model' LK' Aw' RP EA' BASE' HP MRT INC IA AM' HH'.
      apply (KONT fx' R' M' model' LK' Aw' (PEC.ENC B (k + 1) (stk ++ [EI kd 0 0]) d) (adebit L cr (PEC.ESZ * PEC.ecap (k + 1))) RP EA'); try assumption.
      * reflexivity.
      * reflexivity.
      * right. cbn [PEC.en_b PEC.en_k PEC.en_stk]. split; [exact EQ|]. split; reflexivity.
Qed.
End WithHeap.
End PEAEPUSH.
