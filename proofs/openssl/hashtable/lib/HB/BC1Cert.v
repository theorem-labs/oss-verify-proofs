(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 BC1 BC1HS CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition C1_IT : itab := APC.mk_itab_ranges HASEGS c1_ranges.
Lemma C1_IT_ok : itab_sound HASEGS C1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition c1_shape_ (_ : unit) : shape := SCase (EVar 6) 10 (SHole 0) (SHole 1).
Abbreviation c1_shape := (c1_shape_ tt).
Lemma c1_cert :
  CAP.check HASEGS C1_IT HAT NX0 AsanInit.LIMIT ha0_XN ha0_XE ha0_XB C1_HS 0 true false true 400000 3000 None (init_acs_of HAT) c1_plan = COk c1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk c1_shape)). Time Qed.
