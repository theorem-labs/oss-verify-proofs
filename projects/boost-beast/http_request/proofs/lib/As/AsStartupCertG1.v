(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsImages AsPlanImages AsStartup AsStartupHS1 AsStartupHSA AsStartupHSC AsStartupPlan AsStartupRanges.
From Ltac2 Require Import Ltac2 Constr Std Control.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Module AsStartupCert1.   (* [comment removed for export] *)
Definition startup_shape : shape := (SHole 90).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
Lemma startup_cert :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HS1_asan CERT_KC0 CERT_BFUEL CERT_FUEL None hinit startup_plan = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
End AsStartupCert1.

Module AsStartupCert90.   (* [comment removed for export] *)
Definition startup_shape : shape := (SCase (EVar 10) 10 (SHole 91) (SHole 94)).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
Lemma startup_cert :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg90_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSC_asan CERT_KC0 CERT_BFUEL CERT_FUEL None HS1_asan_90 startup_plan_seg90 = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
End AsStartupCert90.

Module AsStartupCert91.   (* [comment removed for export] *)
Definition startup_shape : shape := (SHole 102).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
Lemma startup_cert :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg91_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSA_asan CERT_KC0 CERT_BFUEL CERT_FUEL None HSC_asan_91 startup_plan_seg91 = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
End AsStartupCert91.

Module AsStartupCert94.   (* [comment removed for export] *)
Definition startup_shape : shape := (SHole 105).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
Lemma startup_cert :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg94_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSA_asan CERT_KC0 CERT_BFUEL CERT_FUEL None HSC_asan_94 startup_plan_seg94 = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
End AsStartupCert94.
