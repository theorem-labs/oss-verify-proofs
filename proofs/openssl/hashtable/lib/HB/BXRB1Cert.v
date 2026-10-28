(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 BXu BFEEndRB1 CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition xrb1_IT : itab := APC.mk_itab_ranges HASEGS xu_ranges.
Lemma xrb1_IT_ok : itab_sound HASEGS xrb1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition xrb1_shape_ (_ : unit) : shape := (SExit 2).
Abbreviation xrb1_shape := (xrb1_shape_ tt).
Lemma xrb1_cert :
  CAP.check HASEGS xrb1_IT HAT NX0 AsanInit.LIMIT ha1_XN ha1_XE ha1_XB (fun _ : nat => @None acs) 0 true false true 400000 3000 None feendrb1 xu_plan = COk xrb1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk xrb1_shape)). Time Qed.
