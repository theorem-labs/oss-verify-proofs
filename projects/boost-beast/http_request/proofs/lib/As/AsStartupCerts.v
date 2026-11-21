(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the level certificates stated over one hand-off table per CONFIG_RSEQ value and the renumbered plans of LPS 727298f3. *)
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

(* LPS 727298f3: one hand-off table per CONFIG_RSEQ value up to 100 .. 105 ([AsStartupHS1], [AsStartupHSC],
   [AsStartupHSA]), met into one at the main entry ([AsStartupHSF]); each level is certified at both values. *)
Lemma cert2_0 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HS1_asan_0 HSC_asan_0.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HS1_asan_table_0 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg90_xranges, startup_plan_seg90_k, AsStartupCert90.startup_shape; split; [exact AsStartupCert90.startup_cert_0 | exact AsStartupCert90.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert2_1 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HS1_asan_1 HSC_asan_1.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HS1_asan_table_1 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg90_xranges, startup_plan_seg90_k, AsStartupCert90.startup_shape; split; [exact AsStartupCert90.startup_cert_1 | exact AsStartupCert90.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert2 : forall r, level_certified CERT_KC0 CERT_BFUEL CERT_FUEL (HS1_asan_r r) (HSC_asan_r r).
Proof. intros r. unfold HS1_asan_r, HSC_asan_r. destruct (Z.eqb r 1); [exact cert2_1 | exact cert2_0]. Qed.

Lemma cert3_0 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSC_asan_0 HSA_asan_0.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSC_asan_table_0 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg91_xranges, startup_plan_seg91_k, AsStartupCert91.startup_shape; split; [exact AsStartupCert91.startup_cert_0 | exact AsStartupCert91.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg94_xranges, startup_plan_seg94_k, AsStartupCert94.startup_shape; split; [exact AsStartupCert94.startup_cert_0 | exact AsStartupCert94.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert3_1 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSC_asan_1 HSA_asan_1.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSC_asan_table_1 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg91_xranges, startup_plan_seg91_k, AsStartupCert91.startup_shape; split; [exact AsStartupCert91.startup_cert_1 | exact AsStartupCert91.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg94_xranges, startup_plan_seg94_k, AsStartupCert94.startup_shape; split; [exact AsStartupCert94.startup_cert_1 | exact AsStartupCert94.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert3 : forall r, level_certified CERT_KC0 CERT_BFUEL CERT_FUEL (HSC_asan_r r) (HSA_asan_r r).
Proof. intros r. unfold HSC_asan_r, HSA_asan_r. destruct (Z.eqb r 1); [exact cert3_1 | exact cert3_0]. Qed.

Lemma cert4_0 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSA_asan_0 HSF_asan.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSA_asan_table_0 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg100_xranges, startup_plan_seg100_k, AsStartupCert100.startup_shape; split; [exact AsStartupCert100.startup_cert_0 | exact AsStartupCert100.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg101_xranges, startup_plan_seg101_k, AsStartupCert101.startup_shape; split; [exact AsStartupCert101.startup_cert_0 | exact AsStartupCert101.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg102_xranges, startup_plan_seg102_k, AsStartupCert102.startup_shape; split; [exact AsStartupCert102.startup_cert_0 | exact AsStartupCert102.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg103_xranges, startup_plan_seg103_k, AsStartupCert103.startup_shape; split; [exact AsStartupCert103.startup_cert_0 | exact AsStartupCert103.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg104_xranges, startup_plan_seg104_k, AsStartupCert104.startup_shape; split; [exact AsStartupCert104.startup_cert_0 | exact AsStartupCert104.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg105_xranges, startup_plan_seg105_k, AsStartupCert105.startup_shape; split; [exact AsStartupCert105.startup_cert_0 | exact AsStartupCert105.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert4_1 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSA_asan_1 HSF_asan.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSA_asan_table_1 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg100_xranges, startup_plan_seg100_k, AsStartupCert100.startup_shape; split; [exact AsStartupCert100.startup_cert_1 | exact AsStartupCert100.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg101_xranges, startup_plan_seg101_k, AsStartupCert101.startup_shape; split; [exact AsStartupCert101.startup_cert_1 | exact AsStartupCert101.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg102_xranges, startup_plan_seg102_k, AsStartupCert102.startup_shape; split; [exact AsStartupCert102.startup_cert_1 | exact AsStartupCert102.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg103_xranges, startup_plan_seg103_k, AsStartupCert103.startup_shape; split; [exact AsStartupCert103.startup_cert_1 | exact AsStartupCert103.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg104_xranges, startup_plan_seg104_k, AsStartupCert104.startup_shape; split; [exact AsStartupCert104.startup_cert_1 | exact AsStartupCert104.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg105_xranges, startup_plan_seg105_k, AsStartupCert105.startup_shape; split; [exact AsStartupCert105.startup_cert_1 | exact AsStartupCert105.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert4 : forall r, level_certified CERT_KC0 CERT_BFUEL CERT_FUEL (HSA_asan_r r) (HSF_asan).
Proof. intros r. unfold HSA_asan_r. destruct (Z.eqb r 1); [exact cert4_1 | exact cert4_0]. Qed.

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
