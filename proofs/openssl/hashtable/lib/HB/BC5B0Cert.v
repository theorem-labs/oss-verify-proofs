(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck2 BC3B0Lit BC4e BC4d0 BC4B0Lit BC5B0Lit CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition c5b0_IT : itab := APC.mk_itab_ranges HASEGS (c4d0_ranges ++ c4e_ranges).
Lemma c5b0_IT_ok : itab_sound HASEGS c5b0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition c5b0_shape_ (_ : unit) : shape := (SCase (EVar 7) 0 (SHole 95) (SCase (EVar 7) 2 (SAlt2 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SHole 21)) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32]; SPBlob 2; SPLit [10]] (SHole 23))) (SHole 94))).
Abbreviation c5b0_shape := (c5b0_shape_ tt).
Lemma c5b0_cert :
  CAP.check HASEGS c5b0_IT HAT NX0 AsanInit.LIMIT (ha2_XN (ION.iot_simple ION.ODir 32)) ha2_XE (ha2_XB (ION.iot_simple ION.ODir 32)) C5B0_HS 0 true false true 400000 3000 None c3b0_hs98 c4d0_top = COk c5b0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk c5b0_shape)). Time Qed.
