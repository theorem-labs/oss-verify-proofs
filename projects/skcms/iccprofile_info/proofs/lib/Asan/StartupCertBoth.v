(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanFO AsanInit AsanInitHW
  BothAsanPlanImages CertRefl StartHooksBoth StartupPlanBoth StartupHSBoth.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition KC0 : nat := 0.
Definition BFUEL : nat := 400000.
Definition FUEL : nat := 3000.
Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.

Definition startup_shape : shape := SCase (EVar 6) 10 (SHole 0) (SCase (EVar 6) 1802 (SHole 0) (SHole 0)).

From Ltac2 Require Import Ltac2.
Lemma startup_cert :
  APF.check ASEGS IT0 INFO_BOTH NX0 AsanInit.LIMIT XNS XE0 XB0 HS_both KC0 BFUEL FUEL None (init_acs_hw INFO_BOTH) startup_plan
  = COk startup_shape.
Proof. cert_refl constr:(COk startup_shape). Qed.
