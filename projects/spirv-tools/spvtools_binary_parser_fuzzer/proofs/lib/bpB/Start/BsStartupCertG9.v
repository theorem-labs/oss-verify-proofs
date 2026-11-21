(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the start-up certificate re-runs the check in the build against the computed hand-off tables, on the plan renumbered by the map read from the run. *)
(* LPS 727298f3: the start-up certificates, re-run in the build against the computed hand-off tables
   ([BsStartupRegen]) on the renumbered plans ([psh FSH]); the recorded certificates this file held were
   for the earlier start state. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BothPlanCore BothPlan BsImages BsPlanImages BsStartup BsStartupHSA BsStartupHSF BsStartupPlan BsStartupRanges BsPlanRegen BsStartupRegen.
From Ltac2 Require Import Ltac2 Constr Std Control.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Module AsStartupCert104.
Definition startup_shape : shape := (SHole 4).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. reflexivity. Qed.
Lemma startup_cert_0 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg104_xranges) ASAN_H NX0 BothInit.LIMIT XN0 XE0 XB0 HSF_asan CERT_KC0 CERT_BFUEL CERT_FUEL None HSA_asan_104_0 (psh FSH startup_plan_seg104) = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
Lemma startup_cert_1 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg104_xranges) ASAN_H NX0 BothInit.LIMIT XN0 XE0 XB0 HSF_asan CERT_KC0 CERT_BFUEL CERT_FUEL None HSA_asan_104_1 (psh FSH startup_plan_seg104) = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
End AsStartupCert104.
