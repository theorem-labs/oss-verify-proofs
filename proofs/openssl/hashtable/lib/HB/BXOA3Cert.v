(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 BXu BFEEndOA3 CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition xoa3_IT : itab := APC.mk_itab_ranges HASEGS xu_ranges.
Lemma xoa3_IT_ok : itab_sound HASEGS xoa3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition xoa3_shape_ (_ : unit) : shape := (SExit 2).
Abbreviation xoa3_shape := (xoa3_shape_ tt).
Lemma xoa3_cert :
  CAP.check HASEGS xoa3_IT HAT NX0 AsanInit.LIMIT ha1_XN ha1_XE ha1_XB (fun _ : nat => @None acs) 0 true false true 400000 3000 None feendoa3 xu_plan = COk xoa3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk xoa3_shape)). Time Qed.
