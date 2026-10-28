(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanInit AsHSTab.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages AsStartup EAsStartupPlan EAsStartupRanges EAsStartupHS1 EAsStartupHSC EAsStartupHSA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require EAsStartupCert_startup_plan EAsStartupCert_startup_plan_seg90 EAsStartupCert_startup_plan_seg91 EAsStartupCert_startup_plan_seg94.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition cert1 := EAsStartupCert_startup_plan.startup_cert.
Definition shape1_holes := EAsStartupCert_startup_plan.startup_shape_holes.
Lemma cert2 : level_certified EAsStartupCert_startup_plan.KC0 EAsStartupCert_startup_plan.BFUEL EAsStartupCert_startup_plan.FUEL HS1_easan HSC_easan.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HS1_easan_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg90_xranges, startup_plan_seg90, EAsStartupCert_startup_plan_seg90.startup_shape; split; [exact EAsStartupCert_startup_plan_seg90.startup_cert | exact EAsStartupCert_startup_plan_seg90.startup_shape_holes]|].
  destruct Hh.
Qed.
Lemma cert3 : level_certified EAsStartupCert_startup_plan.KC0 EAsStartupCert_startup_plan.BFUEL EAsStartupCert_startup_plan.FUEL HSC_easan HSA_easan.
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSC_easan_table fold_right fst snd] in Hh.
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg91_xranges, startup_plan_seg91, EAsStartupCert_startup_plan_seg91.startup_shape; split; [exact EAsStartupCert_startup_plan_seg91.startup_cert | exact EAsStartupCert_startup_plan_seg91.startup_shape_holes]|].
  destruct Hh as [[-> ->]|Hh]; [exists startup_plan_seg94_xranges, startup_plan_seg94, EAsStartupCert_startup_plan_seg94.startup_shape; split; [exact EAsStartupCert_startup_plan_seg94.startup_cert | exact EAsStartupCert_startup_plan_seg94.startup_shape_holes]|].
  destruct Hh.
Qed.

