(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the certificates checked at LPS 727298f3 over the renumbered plans, from both CONFIG_RSEQ values' computed hand-off states to the computed main-entry table. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AsanPlanCore AsanPlan BoStartup BoStartupHSA BoStartupHSF BoStartupPlan BoStartupRanges BothImages BothPlanImages.
From Ltac2 Require Import Ltac2 Constr Std Control.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Module BoStartupCert100.   (* [comment removed for export] *)
Definition startup_shape : shape := (SHole 0).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
Lemma startup_cert_0 :
  check BSEGS2 (mk_itab_ranges BSEGS2 startup_plan_seg100_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSF_both CERT_KC0 CERT_BFUEL CERT_FUEL None HSA_both_100_0 startup_plan_seg100_k = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
Lemma startup_cert_1 :
  check BSEGS2 (mk_itab_ranges BSEGS2 startup_plan_seg100_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSF_both CERT_KC0 CERT_BFUEL CERT_FUEL None HSA_both_100_1 startup_plan_seg100_k = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
End BoStartupCert100.

Module BoStartupCert101.   (* [comment removed for export] *)
Definition startup_shape : shape := (SHole 1).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
Lemma startup_cert_0 :
  check BSEGS2 (mk_itab_ranges BSEGS2 startup_plan_seg101_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSF_both CERT_KC0 CERT_BFUEL CERT_FUEL None HSA_both_101_0 startup_plan_seg101_k = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
Lemma startup_cert_1 :
  check BSEGS2 (mk_itab_ranges BSEGS2 startup_plan_seg101_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSF_both CERT_KC0 CERT_BFUEL CERT_FUEL None HSA_both_101_1 startup_plan_seg101_k = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
End BoStartupCert101.
