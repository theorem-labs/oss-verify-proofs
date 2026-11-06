(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics PmStaticsA PmSpecs PmSpecsA PeSpecsAb PmStep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_ac910_ac914.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEBENCF.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.

Theorem v_flush_ok : PECSB.v_flush_spec L ar HI P.
Proof.
  unfold PECSB.v_flush_spec, PECSPA.v_flush_spec, PECSPA.eslot_spec.
  intros PMODE a fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 _ CPRE INCS POK _ NB HB CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  rewrite L5K.rl1 in Rra.
  unfold PMSPA.cfg. cbn [pe_flush EE PeCLayoutB.EADDR_B].
  set (MV := mrestrict (ahid Aw model) M).
  pose proof (PMK.ret_to RSEGS fx R MV 0xac960 W_ac910 r F_ac910 eq_refl D_ac910 Rra ltac:(lia) Hr2) as MS.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok (PEC.owned s en k ++ LBX) FF LK cr Aw M model fx fx R 0xac960 R r MV K HH AM MS).
  { intros w D. exact D. }
  { intros a0 Ha. reflexivity. }
  intros M1 model1 HH1 AM1 MRT1 HID1 MV1 MG1 AG1.
  pose proof (L5SAR.mem_eq_of_agree M M1 AG1) as EM. subst M1.
  apply (KONT fx R M model1 LK Aw en k e cr).
  - intros x Hx. reflexivity.
  - exact CPRE.
  - intros E0. exact E0.
  - apply (L5SAR.ahpres_of L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M).
    + intros a0 _. reflexivity.
    + change (PMSPA.pm_scr 4) with 20480. exact SDEF.
    + apply L5SAR.dk_grows. intros w D. exact D.
  - unfold PMSP.credit_keep. split; lia.
  - exact MRT1.
  - intros x Hx. exact Hx.
  - intros x Hx. exact Hx.
  - exact AM1.
  - exact HH1.
Qed.
End WithHeap.
End PEBENCF.
