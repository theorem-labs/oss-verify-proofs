(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: start-up certificate made again at LPS 727298f3, for each CONFIG_RSEQ value, from the hand-off states the build computes. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From Ltac2 Require Import Ltac2 Constr Std Control.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AxSymExec3 AsanPlanCore AsanPlan PlanRegen StartupHSAsan.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: segment A of the ASan start-up chain (the launch to hand-off 10) at each
   CONFIG_RSEQ value, from that value's start state, on the renumbered recorded plan and against
   the computed hand-off map ([StartupHSAsan]). *)
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma acertA0 : ACHK aIT 0 NX0 (asan_init 0) aplanA aHSA0 = COk ashA0.
Proof. ltac2:(vm_cert_refl constr:(COk ashA0)). Qed.
Lemma acertA1 : ACHK aIT 1 NX0 (asan_init 1) aplanA aHSA1 = COk ashA1.
Proof. ltac2:(vm_cert_refl constr:(COk ashA1)). Qed.
