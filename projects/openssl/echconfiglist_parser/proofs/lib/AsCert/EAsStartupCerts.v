(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the level certificates stated over one hand-off table per CONFIG_RSEQ value up to 91 and 94, met at the S6 hand-offs, and the renumbered plans of LPS 727298f3. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanInit AsHSTab.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsCert Require Import AsImages AsPlanImages AsStartup EAsStartupPlan EAsStartupRanges EAsStartupHS1 EAsStartupHSC EAsStartupHSA.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsCert Require EAsStartupCert_startup_plan EAsStartupCert_startup_plan_seg90 EAsStartupCert_startup_plan_seg91 EAsStartupCert_startup_plan_seg94.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition shape1_holes := EAsStartupCert_startup_plan.startup_shape_holes.
Lemma cert2_0 : level_certified EAsStartupCert_startup_plan.KC0 EAsStartupCert_startup_plan.BFUEL EAsStartupCert_startup_plan.FUEL HS1_easan_0 HSC_easan_0.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HS1_easan_table_0 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg90_xranges, (startup_plan_seg90_k 0), EAsStartupCert_startup_plan_seg90.startup_shape; split; [exact EAsStartupCert_startup_plan_seg90.startup_cert_0 | exact EAsStartupCert_startup_plan_seg90.startup_shape_holes]|].
  destruct Hh.
Qed.
Lemma cert2_1 : level_certified EAsStartupCert_startup_plan.KC0 EAsStartupCert_startup_plan.BFUEL EAsStartupCert_startup_plan.FUEL HS1_easan_1 HSC_easan_1.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HS1_easan_table_1 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg90_xranges, (startup_plan_seg90_k 1), EAsStartupCert_startup_plan_seg90.startup_shape; split; [exact EAsStartupCert_startup_plan_seg90.startup_cert_1 | exact EAsStartupCert_startup_plan_seg90.startup_shape_holes]|].
  destruct Hh.
Qed.
Lemma cert2 : forall r, level_certified EAsStartupCert_startup_plan.KC0 EAsStartupCert_startup_plan.BFUEL EAsStartupCert_startup_plan.FUEL (HS1_easan_r r) (HSC_easan_r r).
Proof. intros r. unfold HS1_easan_r, HSC_easan_r. destruct (Z.eqb r 1); [exact cert2_1 | exact cert2_0]. Qed.
Lemma cert3_0 : level_certified EAsStartupCert_startup_plan.KC0 EAsStartupCert_startup_plan.BFUEL EAsStartupCert_startup_plan.FUEL HSC_easan_0 HSA_easan.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSC_easan_table_0 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg91_xranges, startup_plan_seg91_k, EAsStartupCert_startup_plan_seg91.startup_shape; split; [exact EAsStartupCert_startup_plan_seg91.startup_cert_0 | exact EAsStartupCert_startup_plan_seg91.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg94_xranges, startup_plan_seg94_k, EAsStartupCert_startup_plan_seg94.startup_shape; split; [exact EAsStartupCert_startup_plan_seg94.startup_cert_0 | exact EAsStartupCert_startup_plan_seg94.startup_shape_holes]|].
  destruct Hh.
Qed.
Lemma cert3_1 : level_certified EAsStartupCert_startup_plan.KC0 EAsStartupCert_startup_plan.BFUEL EAsStartupCert_startup_plan.FUEL HSC_easan_1 HSA_easan.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSC_easan_table_1 fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg91_xranges, startup_plan_seg91_k, EAsStartupCert_startup_plan_seg91.startup_shape; split; [exact EAsStartupCert_startup_plan_seg91.startup_cert_1 | exact EAsStartupCert_startup_plan_seg91.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg94_xranges, startup_plan_seg94_k, EAsStartupCert_startup_plan_seg94.startup_shape; split; [exact EAsStartupCert_startup_plan_seg94.startup_cert_1 | exact EAsStartupCert_startup_plan_seg94.startup_shape_holes]|].
  destruct Hh.
Qed.
Lemma cert3 : forall r, level_certified EAsStartupCert_startup_plan.KC0 EAsStartupCert_startup_plan.BFUEL EAsStartupCert_startup_plan.FUEL (HSC_easan_r r) HSA_easan.
Proof. intros r. unfold HSC_easan_r. destruct (Z.eqb r 1); [exact cert3_1 | exact cert3_0]. Qed.
