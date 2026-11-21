(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: start-up certificate made again at LPS 727298f3, for each CONFIG_RSEQ value, from the hand-off states the build computes. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From Ltac2 Require Import Ltac2 Constr Std Control.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AxSymExec3 AsanPlanCore AsanPlan PlanRegen StartupHSBoth.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: segment D of the ASan+UBSan start-up chain (hand-off 12 to hand-off 0) at each
   CONFIG_RSEQ value, from that value's computed hand-off state ([StartupHSBoth]). *)
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma bcertD0 : BCHK bIT 0 (nxt bSC0) bSC0 bplanD bHSD0 = COk bshD0.
Proof. ltac2:(vm_cert_refl constr:(COk bshD0)). Qed.
Lemma bcertD1 : BCHK bIT 1 (nxt bSC1) bSC1 bplanD bHSD1 = COk bshD1.
Proof. ltac2:(vm_cert_refl constr:(COk bshD1)). Qed.
