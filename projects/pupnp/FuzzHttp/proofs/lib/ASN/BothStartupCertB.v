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

(* LPS 727298f3: segment B of the ASan+UBSan start-up chain (hand-off 10 to hand-off 11) at each
   CONFIG_RSEQ value, from that value's computed hand-off state ([StartupHSBoth]). *)
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma bcertB0 : BCHK bIT 0 (nxt bSA0) bSA0 bplanB bHSB0 = COk bshB0.
Proof. ltac2:(vm_cert_refl constr:(COk bshB0)). Qed.
Lemma bcertB1 : BCHK bIT 1 (nxt bSA1) bSA1 bplanB bHSB1 = COk bshB1.
Proof. ltac2:(vm_cert_refl constr:(COk bshB1)). Qed.
