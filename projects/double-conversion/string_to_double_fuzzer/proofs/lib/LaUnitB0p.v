(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIface LxLin.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceB LaState LaMem LaStep LaCheck LaUnitSplit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations LXL LAS LAM LAI LAC LAU.
Open Scope Z_scope.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Export LaUnitB0p_def.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LaUnitB0p_p0 LaUnitB0p_p1 LaUnitB0p_p2 LaUnitB0p_p3 LaUnitB0p_p4 LaUnitB0p_p5 LaUnitB0p_p6 LaUnitB0p_p7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Theorem UNIT_B0p_ok : check_unit UNIT_B0p = true.
Proof.
  apply (check_unit_parts UNIT_B0p PARTS_B0p hdr_B0p cov_B0p).
  intros b Hb. cbn [PARTS_B0p In] in Hb.
  destruct Hb as [<-|Hb]; [exact B0p_part0|].
  destruct Hb as [<-|Hb]; [exact B0p_part1|].
  destruct Hb as [<-|Hb]; [exact B0p_part2|].
  destruct Hb as [<-|Hb]; [exact B0p_part3|].
  destruct Hb as [<-|Hb]; [exact B0p_part4|].
  destruct Hb as [<-|Hb]; [exact B0p_part5|].
  destruct Hb as [<-|Hb]; [exact B0p_part6|].
  destruct Hb as [<-|Hb]; [exact B0p_part7|].
  destruct Hb.
Qed.

From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LbGlue LbFinal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma UNIT_B0p_env3 : LBG.uenv_okb (un_env UNIT_B0p) = true /\ LBG.glue_okb (un_env UNIT_B0p) LIBR_HULL_B LIBR_B SNAP_B = true /\ LBF.envA_okb (un_env UNIT_B0p) = true.
Proof. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. vm_compute; reflexivity. Qed.
Lemma UNIT_B0p_obl : LBF.unit_obligation 0 [] UNIT_B0p.
Proof.
  unfold LBF.unit_obligation.
  destruct UNIT_B0p_env3 as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact UNIT_B0p_ok|]. split; [reflexivity|]. split; [apply (nth_error_In _ 0%nat); vm_compute; reflexivity | reflexivity].
Qed.
Lemma UNIT_B0s_obl : LBF.unit_obligation 0 SNAP_B UNIT_B0p.
Proof.
  unfold LBF.unit_obligation.
  destruct UNIT_B0p_env3 as (E1 & E2 & E3). split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact UNIT_B0p_ok|]. split; [reflexivity|]. split; [apply (nth_error_In _ 133%nat); vm_compute; reflexivity | reflexivity].
Qed.
