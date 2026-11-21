(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the certificate checked at LPS 727298f3 at both CONFIG_RSEQ values, from the computed states at 90 over the plan renumbered by a map read from a probe. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanInit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsCert Require Import AsImages AsPlanImages AsStartup EAsStartupPlan EAsStartupRanges EAsStartupHSC EAsStartupHS1.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.

Definition startup_shape : shape := (SCase (EVar 10) 10 (SHole 91) (SHole 94)).

Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.

From Ltac2 Require Import Ltac2 Constr Std Control.
(* the certificate's [eq_refl], checked by the kernel's [vm_compute] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma startup_cert_0 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg90_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSC_easan_0 KC0 BFUEL FUEL None HS1_easan_90_0 (startup_plan_seg90_k 0) = COk startup_shape.
Proof. cert_refl constr:(COk startup_shape). Qed.
Lemma startup_cert_1 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg90_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSC_easan_1 KC0 BFUEL FUEL None HS1_easan_90_1 (startup_plan_seg90_k 1) = COk startup_shape.
Proof. cert_refl constr:(COk startup_shape). Qed.
