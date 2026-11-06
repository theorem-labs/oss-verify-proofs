(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIface LxLin.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LaState LaMem LaStep LaCheck LaUnitSplit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations LXL LAS LAM LAI LAC LAU.
Open Scope Z_scope.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Export LaUnitA0p_def.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LaUnitA0p_p0 LaUnitA0p_p1 LaUnitA0p_p2 LaUnitA0p_p3 LaUnitA0p_p4 LaUnitA0p_p5 LaUnitA0p_p6 LaUnitA0p_p7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Theorem UNIT_A0p_ok : check_unit UNIT_A0p = true.
Proof.
  apply (check_unit_parts UNIT_A0p PARTS_A0p hdr_A0p cov_A0p).
  intros b Hb. cbn [PARTS_A0p In] in Hb.
  destruct Hb as [<-|Hb]; [exact A0p_part0|].
  destruct Hb as [<-|Hb]; [exact A0p_part1|].
  destruct Hb as [<-|Hb]; [exact A0p_part2|].
  destruct Hb as [<-|Hb]; [exact A0p_part3|].
  destruct Hb as [<-|Hb]; [exact A0p_part4|].
  destruct Hb as [<-|Hb]; [exact A0p_part5|].
  destruct Hb as [<-|Hb]; [exact A0p_part6|].
  destruct Hb as [<-|Hb]; [exact A0p_part7|].
  destruct Hb.
Qed.

From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LaGlue LaFinal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma UNIT_A0p_env3 : LAG.uenv_okb (un_env UNIT_A0p) = true /\ LAG.glue_okb (un_env UNIT_A0p) LIBR_HULL_A LIBR_A SNAP_A = true /\ LAF.envA_okb (un_env UNIT_A0p) = true.
Proof. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. vm_compute; reflexivity. Qed.
Lemma UNIT_A0p_obl : LAF.unit_obligation 0 [] UNIT_A0p.
Proof.
  unfold LAF.unit_obligation.
  destruct UNIT_A0p_env3 as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact UNIT_A0p_ok|]. split; [reflexivity|]. split; [apply (nth_error_In _ 0%nat); vm_compute; reflexivity | reflexivity].
Qed.
Lemma UNIT_A0s_obl : LAF.unit_obligation 0 SNAP_A UNIT_A0p.
Proof.
  unfold LAF.unit_obligation.
  destruct UNIT_A0p_env3 as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact UNIT_A0p_ok|]. split; [reflexivity|]. split; [apply (nth_error_In _ 144%nat); vm_compute; reflexivity | reflexivity].
Qed.
