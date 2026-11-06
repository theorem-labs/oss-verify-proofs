(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsImages AsPlanImages AsStartup AsStartupHSA AsStartupHSF AsStartupPlan AsStartupRanges.
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

Module AsStartupCert104.   (* [comment removed for export] *)
Definition startup_shape : shape := (SHole 4).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
Lemma startup_cert :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg104_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSF_asan CERT_KC0 CERT_BFUEL CERT_FUEL None HSA_asan_104 startup_plan_seg104 = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
End AsStartupCert104.

Module AsStartupCert105.   (* [comment removed for export] *)
Definition startup_shape : shape := (SHole 5).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
Lemma startup_cert :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg105_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSF_asan CERT_KC0 CERT_BFUEL CERT_FUEL None HSA_asan_105 startup_plan_seg105 = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
End AsStartupCert105.
