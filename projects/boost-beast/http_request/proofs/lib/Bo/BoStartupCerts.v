(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the level certificates stated over one hand-off table per CONFIG_RSEQ value and the renumbered plans of LPS 727298f3. *)
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

(* LPS 727298f3: one hand-off table per CONFIG_RSEQ value up to 100 .. 105 ([BoStartupHS1], [BoStartupHSC],
   [BoStartupHSA]), met into one at the main entry ([BoStartupHSF]); each level is certified at both values. *)
Lemma cert2_0 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HS1_both_0 HSC_both_0.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HS1_both_table_0 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg90_xranges, startup_plan_seg90_k, BoStartupCert90.startup_shape; split; [exact BoStartupCert90.startup_cert_0 | exact BoStartupCert90.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert2_1 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HS1_both_1 HSC_both_1.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HS1_both_table_1 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg90_xranges, startup_plan_seg90_k, BoStartupCert90.startup_shape; split; [exact BoStartupCert90.startup_cert_1 | exact BoStartupCert90.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert2 : forall r, level_certified CERT_KC0 CERT_BFUEL CERT_FUEL (HS1_both_r r) (HSC_both_r r).
Proof. intros r. unfold HS1_both_r, HSC_both_r. destruct (Z.eqb r 1); [exact cert2_1 | exact cert2_0]. Qed.

Lemma cert3_0 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSC_both_0 HSA_both_0.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSC_both_table_0 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg91_xranges, startup_plan_seg91_k, BoStartupCert91.startup_shape; split; [exact BoStartupCert91.startup_cert_0 | exact BoStartupCert91.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg94_xranges, startup_plan_seg94_k, BoStartupCert94.startup_shape; split; [exact BoStartupCert94.startup_cert_0 | exact BoStartupCert94.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert3_1 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSC_both_1 HSA_both_1.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSC_both_table_1 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg91_xranges, startup_plan_seg91_k, BoStartupCert91.startup_shape; split; [exact BoStartupCert91.startup_cert_1 | exact BoStartupCert91.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg94_xranges, startup_plan_seg94_k, BoStartupCert94.startup_shape; split; [exact BoStartupCert94.startup_cert_1 | exact BoStartupCert94.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert3 : forall r, level_certified CERT_KC0 CERT_BFUEL CERT_FUEL (HSC_both_r r) (HSA_both_r r).
Proof. intros r. unfold HSC_both_r, HSA_both_r. destruct (Z.eqb r 1); [exact cert3_1 | exact cert3_0]. Qed.

Lemma cert4_0 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSA_both_0 HSF_both.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSA_both_table_0 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg100_xranges, startup_plan_seg100_k, BoStartupCert100.startup_shape; split; [exact BoStartupCert100.startup_cert_0 | exact BoStartupCert100.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg101_xranges, startup_plan_seg101_k, BoStartupCert101.startup_shape; split; [exact BoStartupCert101.startup_cert_0 | exact BoStartupCert101.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg102_xranges, startup_plan_seg102_k, BoStartupCert102.startup_shape; split; [exact BoStartupCert102.startup_cert_0 | exact BoStartupCert102.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg103_xranges, startup_plan_seg103_k, BoStartupCert103.startup_shape; split; [exact BoStartupCert103.startup_cert_0 | exact BoStartupCert103.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg104_xranges, startup_plan_seg104_k, BoStartupCert104.startup_shape; split; [exact BoStartupCert104.startup_cert_0 | exact BoStartupCert104.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg105_xranges, startup_plan_seg105_k, BoStartupCert105.startup_shape; split; [exact BoStartupCert105.startup_cert_0 | exact BoStartupCert105.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert4_1 : level_certified CERT_KC0 CERT_BFUEL CERT_FUEL HSA_both_1 HSF_both.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSA_both_table_1 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg100_xranges, startup_plan_seg100_k, BoStartupCert100.startup_shape; split; [exact BoStartupCert100.startup_cert_1 | exact BoStartupCert100.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg101_xranges, startup_plan_seg101_k, BoStartupCert101.startup_shape; split; [exact BoStartupCert101.startup_cert_1 | exact BoStartupCert101.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg102_xranges, startup_plan_seg102_k, BoStartupCert102.startup_shape; split; [exact BoStartupCert102.startup_cert_1 | exact BoStartupCert102.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg103_xranges, startup_plan_seg103_k, BoStartupCert103.startup_shape; split; [exact BoStartupCert103.startup_cert_1 | exact BoStartupCert103.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg104_xranges, startup_plan_seg104_k, BoStartupCert104.startup_shape; split; [exact BoStartupCert104.startup_cert_1 | exact BoStartupCert104.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg105_xranges, startup_plan_seg105_k, BoStartupCert105.startup_shape; split; [exact BoStartupCert105.startup_cert_1 | exact BoStartupCert105.startup_shape_holes]|].
  destruct Hh.
Qed.

Lemma cert4 : forall r, level_certified CERT_KC0 CERT_BFUEL CERT_FUEL (HSA_both_r r) (HSF_both).
Proof. intros r. unfold HSA_both_r. destruct (Z.eqb r 1); [exact cert4_1 | exact cert4_0]. Qed.

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
