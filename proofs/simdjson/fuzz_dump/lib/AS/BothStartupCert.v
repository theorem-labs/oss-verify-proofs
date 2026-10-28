(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanTablesB AsanPlanImagesB AsanInit AsanStartup StartupPlanBoth StartupHSBoth.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.

Definition startup_shape : shape := (SHole 0).

Lemma startup_cert :
  check ASEGS IT0 ASAN_B NX0 AsanInit.LIMIT XN0 XE0 XB0 HS_both KC0 BFUEL FUEL None asan_b_init startup_plan = COk startup_shape.
Proof. cert_refl constr:(COk startup_shape). Qed.
