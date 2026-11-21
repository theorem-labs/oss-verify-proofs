(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: one certificate per CONFIG_RSEQ layout, against the hand-off and join states [StartupHSBoth] computes in the build, with the start-up shape computed here rather than transcribed. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanFO AsanInit
  BothAsanPlanImages CertRefl AsanMainLib StartHooksBoth StartupPlanBoth PlanRegen StartupHSBoth.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.

(** The start-up's shape at each layout, read off the check it certifies. *)
Definition startup_shape_1 : shape :=
  Eval vm_compute in match su_run 1 (HS_both true) (JS_both true) with COk s => s | CErr _ _ _ => SNil end.
Definition startup_shape_0 : shape :=
  Eval vm_compute in match su_run 0 (HS_both false) (JS_both false) with COk s => s | CErr _ _ _ => SNil end.
Definition startup_shape (rsb : bool) : shape := if rsb then startup_shape_1 else startup_shape_0.

From Ltac2 Require Import Ltac2.
Lemma startup_cert_1 :
  APF.check ASEGS IT0 (INFO_BOTH_at 1) NX0 AsanInit.LIMIT (XNS 1) XE0 XB0 (HS_both true) KC0 BFUEL FUEL None
    (init_acs_hw (INFO_BOTH_at 1)) (startup_plan true)
  = COk startup_shape_1.
Proof. cert_refl constr:(COk startup_shape_1). Qed.
Lemma startup_cert_0 :
  APF.check ASEGS IT0 (INFO_BOTH_at 0) NX0 AsanInit.LIMIT (XNS 0) XE0 XB0 (HS_both false) KC0 BFUEL FUEL None
    (init_acs_hw (INFO_BOTH_at 0)) (startup_plan false)
  = COk startup_shape_0.
Proof. cert_refl constr:(COk startup_shape_0). Qed.
Lemma startup_cert (rsb : bool) :
  APF.check ASEGS IT0 (INFO_BOTH_at (rseq_z rsb)) NX0 AsanInit.LIMIT (XNS (rseq_z rsb)) XE0 XB0 (HS_both rsb) KC0 BFUEL FUEL None
    (init_acs_hw (INFO_BOTH_at (rseq_z rsb))) (startup_plan rsb)
  = COk (startup_shape rsb).
Proof. ltac1:(destruct rsb; [exact startup_cert_1 | exact startup_cert_0]). Qed.

Lemma startup_all_holes (rsb : bool) : all_holes (startup_shape rsb) = true.
Proof. ltac1:(destruct rsb; vm_compute; reflexivity). Qed.

(** every collected hand-off state is free of blob terms *)
Lemma HSA_noblob (rsb : bool) : forall h ch, HS_both rsb h = Some ch -> acs_noblob ch = true.
Proof.
  ltac1:(intros h ch H; apply (hlookup_forall acs_noblob (fst (SU rsb)) h ch); [|exact H];
    destruct rsb; vm_compute; reflexivity).
Qed.
