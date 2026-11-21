(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the certificate checked at LPS 727298f3 at both CONFIG_RSEQ values, over the plan renumbered by a map read from a probe and the hand-off states computed in the build. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanInit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages AsStartup EAsStartupPlan EAsStartupRanges EAsStartupHS1.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.

Definition startup_shape : shape := (SHole 90).

Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.

From Ltac2 Require Import Ltac2 Constr Std Control.
(* the certificate's [eq_refl], checked by the kernel's [vm_compute] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

(* LPS 727298f3: [hinit] takes the run's CONFIG_RSEQ as 0/1 ([AsImages]); the certificate is checked at
   both values over [startup_plan_k] against that value's computed table ([EAsStartupHS1]), and
   [startup_cert_k] picks the one of the run's kernel build. *)
Lemma startup_cert0 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HS1_easan_0 KC0 BFUEL FUEL None (hinit 0) startup_plan_k = COk startup_shape.
Proof. cert_refl constr:(COk startup_shape). Qed.
Lemma startup_cert1 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HS1_easan_1 KC0 BFUEL FUEL None (hinit 1) startup_plan_k = COk startup_shape.
Proof. cert_refl constr:(COk startup_shape). Qed.
Lemma startup_cert_k : forall k : LinuxProcessSemantics.LinuxProcessSem.State.KernelBuild,
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 (HS1_easan_r (rseq_z (LinuxProcessSemantics.LinuxProcessSem.State.kb_rseq k))) KC0 BFUEL FUEL None (hinit (rseq_z (LinuxProcessSemantics.LinuxProcessSem.State.kb_rseq k))) startup_plan_k = COk startup_shape.
Proof.
  (* the file loads Ltac2 for [cert_refl]: this proof is Ltac1 *)
  ltac1:(intros k; unfold HS1_easan_r; destruct (LinuxProcessSemantics.LinuxProcessSem.State.kb_rseq k);
         [exact startup_cert1 | exact startup_cert0]).
Qed.
