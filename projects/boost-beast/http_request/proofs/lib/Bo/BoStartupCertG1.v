(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the certificates checked at LPS 727298f3 over the renumbered plans, from the computed hand-off states, at both CONFIG_RSEQ values. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AsanPlanCore AsanPlan BoStartup BoStartupHS1 BoStartupHSA BoStartupHSC BoStartupPlan BoStartupRanges BothImages BothPlanImages.
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

Module BoStartupCert1.   (* [comment removed for export] *)
Definition startup_shape : shape := (SHole 90).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
(* LPS 727298f3: [bhinit] takes the run's CONFIG_RSEQ as 0/1, and the hand-off table is the one that value's
   run computes ([BoStartupHS1]); the certificate is checked at both values over the renumbered plan
   [startup_plan_k], and [startup_cert_k] picks the one of the run's kernel build. *)
Lemma startup_cert0 :
  check BSEGS2 (mk_itab_ranges BSEGS2 startup_plan_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HS1_both_0 CERT_KC0 CERT_BFUEL CERT_FUEL None (bhinit 0) startup_plan_k = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
Lemma startup_cert1 :
  check BSEGS2 (mk_itab_ranges BSEGS2 startup_plan_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HS1_both_1 CERT_KC0 CERT_BFUEL CERT_FUEL None (bhinit 1) startup_plan_k = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
Lemma startup_cert_k : forall k : LinuxProcessSemantics.LinuxProcessSem.State.KernelBuild,
  check BSEGS2 (mk_itab_ranges BSEGS2 startup_plan_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 (HS1_both_r (rseq_z (LinuxProcessSemantics.LinuxProcessSem.State.kb_rseq k))) CERT_KC0 CERT_BFUEL CERT_FUEL None (bhinit (rseq_z (LinuxProcessSemantics.LinuxProcessSem.State.kb_rseq k))) startup_plan_k = COk startup_shape.
Proof. intros k. destruct (LinuxProcessSemantics.LinuxProcessSem.State.kb_rseq k); [exact startup_cert1 | exact startup_cert0]. Qed.
End BoStartupCert1.

Module BoStartupCert90.   (* [comment removed for export] *)
Definition startup_shape : shape := (SCase (EVar 10) 10 (SHole 91) (SHole 94)).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
Lemma startup_cert_0 :
  check BSEGS2 (mk_itab_ranges BSEGS2 startup_plan_seg90_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSC_both_0 CERT_KC0 CERT_BFUEL CERT_FUEL None HS1_both_90_0 startup_plan_seg90_k = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
Lemma startup_cert_1 :
  check BSEGS2 (mk_itab_ranges BSEGS2 startup_plan_seg90_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSC_both_1 CERT_KC0 CERT_BFUEL CERT_FUEL None HS1_both_90_1 startup_plan_seg90_k = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
End BoStartupCert90.

Module BoStartupCert91.   (* [comment removed for export] *)
Definition startup_shape : shape := (SHole 102).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
Lemma startup_cert_0 :
  check BSEGS2 (mk_itab_ranges BSEGS2 startup_plan_seg91_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSA_both_0 CERT_KC0 CERT_BFUEL CERT_FUEL None HSC_both_91_0 startup_plan_seg91_k = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
Lemma startup_cert_1 :
  check BSEGS2 (mk_itab_ranges BSEGS2 startup_plan_seg91_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSA_both_1 CERT_KC0 CERT_BFUEL CERT_FUEL None HSC_both_91_1 startup_plan_seg91_k = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
End BoStartupCert91.

Module BoStartupCert94.   (* [comment removed for export] *)
Definition startup_shape : shape := (SHole 105).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof. vm_compute. reflexivity. Qed.
Lemma startup_cert_0 :
  check BSEGS2 (mk_itab_ranges BSEGS2 startup_plan_seg94_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSA_both_0 CERT_KC0 CERT_BFUEL CERT_FUEL None HSC_both_94_0 startup_plan_seg94_k = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
Lemma startup_cert_1 :
  check BSEGS2 (mk_itab_ranges BSEGS2 startup_plan_seg94_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSA_both_1 CERT_KC0 CERT_BFUEL CERT_FUEL None HSC_both_94_1 startup_plan_seg94_k = COk startup_shape.
Proof. ltac2:(cert_refl constr:(COk startup_shape)). Qed.
End BoStartupCert94.
