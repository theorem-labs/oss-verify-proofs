(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan StartupHSAsan StartupPlan2Asan StartupHS2Asan AsanStartupCert.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition IT2 : itab := mk_itab_ranges BSEGS startup2_plan_both_ranges.
Lemma IT2_ok : itab_sound BSEGS IT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition NXS2 : nat := 453%nat.
Lemma NXS2_ge : (NX0 <= NXS2)%nat. Proof. unfold NX0, NXS2. lia. Qed.
(* [comment removed for export] *)
Definition startup2_shape : shape := SCase (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 344))) 3935) 4030 (SHole 1) (SHole 2).
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup2_cert :
  check BSEGS IT2 ASAN NXS2 AsanInit.LIMIT (XNS BSEGS ASAN NXS2 AsanInit.LIMIT) XE0 XB0 HS_both2 KC0 BFUEL FUEL None HS_bothD_0 startup2_plan_both = COk startup2_shape.
Proof. Time (vm_cert_refl constr:(COk startup2_shape)). Time Qed.
