(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 BXu BFEEndHA2 CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition xha2_IT : itab := APC.mk_itab_ranges HASEGS xu_ranges.
Lemma xha2_IT_ok : itab_sound HASEGS xha2_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition xha2_shape_ (_ : unit) : shape := (SExit 2).
Abbreviation xha2_shape := (xha2_shape_ tt).
Lemma xha2_cert :
  CAP.check HASEGS xha2_IT HAT NX0 AsanInit.LIMIT ha1_XN ha1_XE ha1_XB (fun _ : nat => @None acs) 0 true false true 400000 3000 None feendha2 xu_plan = COk xha2_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk xha2_shape)). Time Qed.
