(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 BFIaEndA0o BC7m BC7mA0oLit CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition c7ma0o_IT : itab := APC.mk_itab_ranges HASEGS c7m_ranges.
Lemma c7ma0o_IT_ok : itab_sound HASEGS c7ma0o_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition c7ma0o_shape_ (_ : unit) : shape := (SHole 27).
Abbreviation c7ma0o_shape := (c7ma0o_shape_ tt).
Lemma c7ma0o_cert :
  CAP.check HASEGS c7ma0o_IT HAT NX0 AsanInit.LIMIT ha1_XN ha1_XE ha1_XB C7mA0o_HS 0 true false true 400000 3000 None fiaenda0o c7m_plan = COk c7ma0o_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk c7ma0o_shape)). Time Qed.
