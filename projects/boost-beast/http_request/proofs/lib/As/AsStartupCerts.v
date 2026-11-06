(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab AsImages AsPlanImages AsStartup AsStartupPlan AsStartupRanges
  AsStartupHS1 AsStartupHSC AsStartupHSA AsStartupHSF.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Export AsStartupCertG1 AsStartupCertG2 AsStartupCertG3 AsStartupCertG4.

Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

Lemma cert2 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HS1_asan HSC_asan.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HS1_asan_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg90_xranges, startup_plan_seg90, AsStartupCert90.startup_shape; split; [exact AsStartupCert90.startup_cert | exact AsStartupCert90.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert3 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSC_asan HSA_asan.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSC_asan_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg91_xranges, startup_plan_seg91, AsStartupCert91.startup_shape; split; [exact AsStartupCert91.startup_cert | exact AsStartupCert91.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg94_xranges, startup_plan_seg94, AsStartupCert94.startup_shape; split; [exact AsStartupCert94.startup_cert | exact AsStartupCert94.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert4 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSA_asan HSF_asan.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSA_asan_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg100_xranges, startup_plan_seg100, AsStartupCert100.startup_shape; split; [exact AsStartupCert100.startup_cert | exact AsStartupCert100.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg101_xranges, startup_plan_seg101, AsStartupCert101.startup_shape; split; [exact AsStartupCert101.startup_cert | exact AsStartupCert101.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg102_xranges, startup_plan_seg102, AsStartupCert102.startup_shape; split; [exact AsStartupCert102.startup_cert | exact AsStartupCert102.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg103_xranges, startup_plan_seg103, AsStartupCert103.startup_shape; split; [exact AsStartupCert103.startup_cert | exact AsStartupCert103.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg104_xranges, startup_plan_seg104, AsStartupCert104.startup_shape; split; [exact AsStartupCert104.startup_cert | exact AsStartupCert104.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg105_xranges, startup_plan_seg105, AsStartupCert105.startup_shape; split; [exact AsStartupCert105.startup_cert | exact AsStartupCert105.startup_shape_holes]|].
  destruct Hh.
Qed.

(* [comment removed for export] *)
Lemma HSF_asan_pc : forall h ch, HSF_asan h = Some ch -> pc ch = 666832.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSF_asan_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh as [[-> ->]|Hh]; [vm_compute; reflexivity|].
  destruct Hh.
Qed.
