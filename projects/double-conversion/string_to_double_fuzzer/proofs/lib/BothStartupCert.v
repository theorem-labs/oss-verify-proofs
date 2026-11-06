(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From Ltac2 Require Import Ltac2 Constr Std Control.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanNodesRP BothPlanImages BothTableL AsanItabFast AsanInit AsanMainDefs AsanMainLib AsanStartup BothStartup StartupPlanBoth StartupHSBoth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.

(* [comment removed for export] *)
Definition IT0b : itab := mk_itab_ranges_fast BSEGS startup_plan_both_ranges.   (* [comment removed for export] *)
Lemma IT0b_ok : itab_sound BSEGS IT0b.
Proof. apply mk_itab_ranges_fast_sound. Qed.

Definition startup_shape_both : shape := SHole 0.

(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma startup_cert_both :
  check BSEGS IT0b BOTHL NX0 AsanInit.LIMIT (RPN.xn BSEGS BOTHL NX0 RPN.RP_BOTH) XE0 XB0 XL0 HS_both HL0 AP.TT_none KC0 BFUEL FUEL None both_initL startup_plan_both = COk startup_shape_both.
Proof. ltac2:(cert_refl constr:(COk startup_shape_both)). Qed.

Lemma startup_holes_both : all_holes startup_shape_both = true.
Proof. vm_compute. reflexivity. Qed.

Lemma HSB_noblob : forall h ch, HS_both h = Some ch -> acs_noblob ch = true.
Proof.
  (* [comment removed for export] *)
  intros h ch H.
  assert (E : match HS_both h with Some c => acs_noblob c | None => true end = true).
  { do 8 (destruct h as [|h]; [vm_compute; reflexivity|]). reflexivity. }
  rewrite H in E. exact E.
Qed.
