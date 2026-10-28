(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck2 BC3B2Lit BC4n BC4B2Lit CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition c4nb2_IT : itab := APC.mk_itab_ranges HASEGS c4n_ranges.
Lemma c4nb2_IT_ok : itab_sound HASEGS c4nb2_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition c4nb2_shape_ (_ : unit) : shape := (SCase (EVar 7) 63 (SCase (EVar 7) 0 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10]] (SHole 21)) (SCase (EVar 7) 62 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SHole 21)) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SEmitP 2 [] (SHole 21))))) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2] (SEmitP 2 [SPLit [10]] (SHole 21)))).
Abbreviation c4nb2_shape := (c4nb2_shape_ tt).
Lemma c4nb2_cert :
  CAP.check HASEGS c4nb2_IT HAT NX0 AsanInit.LIMIT (ha2_XN (ION.iot_simple ION.ONoEnt 32)) ha2_XE (ha2_XB (ION.iot_simple ION.ONoEnt 32)) C4B2_HSn 0 true false true 400000 3000 None c3b2_hs98 c4n_top = COk c4nb2_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk c4nb2_shape)). Time Qed.
