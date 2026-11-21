(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: start-up certificate made again at LPS 727298f3, for each CONFIG_RSEQ value, from the hand-off states the build computes. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From Ltac2 Require Import Ltac2 Constr Std Control.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AxSymExec3 AsanPlanCore AsanPlan PlanRegen StartupHSAsan StartupHS2Asan.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: the last segment of the ASan start-up chain (hand-off 0 to the main phase's
   hand-offs 1 and 2) at each CONFIG_RSEQ value, from that value's computed hand-off state
   ([StartupHSAsan], [StartupHS2Asan]). *)
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma acert20 : ACHK aIT2 0 (nxt aSD0) aSD0 aplan2 aHS2_0 = COk ash2_0.
Proof. ltac2:(vm_cert_refl constr:(COk ash2_0)). Qed.
Lemma acert21 : ACHK aIT2 1 (nxt aSD1) aSD1 aplan2 aHS2_1 = COk ash2_1.
Proof. ltac2:(vm_cert_refl constr:(COk ash2_1)). Qed.
