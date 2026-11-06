(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab BothImages BothPlanImages BoStartup BoStartupPlan BoStartupRanges
  BoStartupHS1 BoStartupHSC BoStartupHSA BoStartupHSF.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Export BoStartupCertG1 BoStartupCertG2 BoStartupCertG3 BoStartupCertG4.

Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cert2 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HS1_both HSC_both.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HS1_both_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg90_xranges, startup_plan_seg90, BoStartupCert90.startup_shape; split; [exact BoStartupCert90.startup_cert | exact BoStartupCert90.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert3 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSC_both HSA_both.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSC_both_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg91_xranges, startup_plan_seg91, BoStartupCert91.startup_shape; split; [exact BoStartupCert91.startup_cert | exact BoStartupCert91.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg94_xranges, startup_plan_seg94, BoStartupCert94.startup_shape; split; [exact BoStartupCert94.startup_cert | exact BoStartupCert94.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert4 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSA_both HSF_both.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSA_both_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg100_xranges, startup_plan_seg100, BoStartupCert100.startup_shape; split; [exact BoStartupCert100.startup_cert | exact BoStartupCert100.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg101_xranges, startup_plan_seg101, BoStartupCert101.startup_shape; split; [exact BoStartupCert101.startup_cert | exact BoStartupCert101.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg102_xranges, startup_plan_seg102, BoStartupCert102.startup_shape; split; [exact BoStartupCert102.startup_cert | exact BoStartupCert102.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg103_xranges, startup_plan_seg103, BoStartupCert103.startup_shape; split; [exact BoStartupCert103.startup_cert | exact BoStartupCert103.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg104_xranges, startup_plan_seg104, BoStartupCert104.startup_shape; split; [exact BoStartupCert104.startup_cert | exact BoStartupCert104.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg105_xranges, startup_plan_seg105, BoStartupCert105.startup_shape; split; [exact BoStartupCert105.startup_cert | exact BoStartupCert105.startup_shape_holes]|].
  destruct Hh.
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.False Sort Prop.

(* [comment removed for export] *)
Lemma HSF_both_pc : forall h ch, HSF_both h = Some ch -> pc ch = 671644.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSF_both_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh.
Qed.
