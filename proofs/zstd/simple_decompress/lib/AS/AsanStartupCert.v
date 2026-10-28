(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan StartupHSAsan.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
(* [comment removed for export] *)
Definition IT0 : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_0.
Lemma IT0_ok : itab_sound BSEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition startup_shape : shape := SHole 10.
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_cert :
  check BSEGS IT0 ASAN NX0 AsanInit.LIMIT (XNS BSEGS ASAN NX0 AsanInit.LIMIT) XE0 XB0 HS_bothA KC0 BFUEL FUEL None asan_init startup_plan_both = COk startup_shape.
Proof. Time (vm_cert_refl constr:(COk startup_shape)). Time Qed.
