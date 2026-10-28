(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck2 BC3A1Lit BC4l BC4A1Lit CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition c4la1_IT : itab := APC.mk_itab_ranges HASEGS c4l_ranges.
Lemma c4la1_IT_ok : itab_sound HASEGS c4la1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition c4la1_shape_ (_ : unit) : shape := (SCase (EVar 7) 4095 (SHole 96) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2] (SEmitP 2 [SPLit [10]] (SHole 21)))).
Abbreviation c4la1_shape := (c4la1_shape_ tt).
Lemma c4la1_cert :
  CAP.check HASEGS c4la1_IT HAT NX0 AsanInit.LIMIT (ha2_XN (ION.iot_simple ION.OTooLong 32)) ha2_XE (ha2_XB (ION.iot_simple ION.OTooLong 32)) C4A1_HS 0 true false true 400000 3000 None c3a1_hs98 c4l_top = COk c4la1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk c4la1_shape)). Time Qed.
