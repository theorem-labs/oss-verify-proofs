(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 BC1HS BC2AStart HBSplit BSt3b BC2B3Lit CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition c2b3_IT : itab := APC.mk_itab_ranges HASEGS st3b_ranges.
Lemma c2b3_IT_ok : itab_sound HASEGS c2b3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition c2b3_shape_ (_ : unit) : shape := (SHole 10).
Abbreviation c2b3_shape := (c2b3_shape_ tt).
Lemma c2b3_cert :
  CAP.check HASEGS c2b3_IT HAT NX0 AsanInit.LIMIT ha1_XN ha1_XE ha1_XB C2B3_HS 0 true false true 400000 3000 None c2b3_start st3b_plan = COk c2b3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk c2b3_shape)). Time Qed.
