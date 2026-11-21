(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the start-up certificate re-runs the check in the build against the computed hand-off tables, on the plan renumbered by the map read from the run. *)
(* LPS 727298f3: the start-up certificates, re-run in the build against the computed hand-off tables
   ([BsStartupRegen]) on the renumbered plans ([psh FSH]); the recorded certificates this file held were
   for the earlier start state. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BothPlanCore BothPlan BsImages BsPlanImages BsStartup BsStartupHS1 BsStartupPlan BsStartupRanges BsPlanRegen BsStartupRegen.
From Ltac2 Require Import Ltac2 Constr Std Control.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Module AsStartupCert1.
Definition startup_shape : shape := (SHole 90).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. reflexivity. Qed.
Lemma startup_cert_0 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 BothInit.LIMIT XN0 XE0 XB0 HS1_asan_0 CERT_KC0 CERT_BFUEL CERT_FUEL None (hinit_r 0) (psh FSH startup_plan) = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
Lemma startup_cert_1 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 BothInit.LIMIT XN0 XE0 XB0 HS1_asan_1 CERT_KC0 CERT_BFUEL CERT_FUEL None (hinit_r 1) (psh FSH startup_plan) = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
(** both CONFIG_RSEQ values *)
Lemma startup_cert : forall r, r = 0 \/ r = 1 ->
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 BothInit.LIMIT XN0 XE0 XB0 (HS1_asan_r r) CERT_KC0 CERT_BFUEL CERT_FUEL None (hinit_r r) (psh FSH startup_plan) = COk startup_shape.
Proof. intros r [-> | ->]; [exact startup_cert_0 | exact startup_cert_1]. Qed.
End AsStartupCert1.
