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

(* LPS 727298f3: segment B of the ASan start-up chain (hand-off 10 to hand-off 11) at each
   CONFIG_RSEQ value, from that value's computed hand-off state ([StartupHSAsan]). *)
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma acertB0 : ACHK aIT 0 (nxt aSA0) aSA0 aplanB aHSB0 = COk ashB0.
Proof. ltac2:(vm_cert_refl constr:(COk ashB0)). Qed.
Lemma acertB1 : ACHK aIT 1 (nxt aSA1) aSA1 aplanB aHSB1 = COk ashB1.
Proof. ltac2:(vm_cert_refl constr:(COk ashB1)). Qed.
