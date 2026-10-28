(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 BC3A3Lit BC4e BC6 BC4A3Lit BC6A3Lit CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition c66aa3_IT : itab := APC.mk_itab_ranges HASEGS c6_ranges.
Lemma c66aa3_IT_ok : itab_sound HASEGS c66aa3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition c66aa3_shape_ (_ : unit) : shape := (SAlt2 (SCase (EVar 7) 63 (SCase (EVar 7) 0 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10]] (SHole 21)) (SCase (EVar 7) 62 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SHole 21)) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SEmitP 2 [] (SHole 21))))) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2] (SEmitP 2 [SPLit [10]] (SHole 21)))) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 115; 104; 111; 114; 116; 101; 114; 32; 116; 104; 97; 110; 32; 104; 101; 97; 100; 101; 114; 10]] (SHole 24))).
Abbreviation c66aa3_shape := (c66aa3_shape_ tt).
Lemma c66aa3_cert :
  CAP.check HASEGS c66aa3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.iot_simple (ION.OFile 0 0) 32)) ha3_XE (ha3_XB (ION.iot_simple (ION.OFile 0 0) 32)) C6A3_HS 0 true false true 400000 3000 None c3a3_hs98 c6_top0 = COk c66aa3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk c66aa3_shape)). Time Qed.
