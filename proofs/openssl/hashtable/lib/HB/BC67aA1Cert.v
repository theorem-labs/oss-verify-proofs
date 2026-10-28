(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 BC3A1Lit BC4e BC6 BC4A1Lit BC6A1Lit CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition c67aa1_IT : itab := APC.mk_itab_ranges HASEGS c6_ranges.
Lemma c67aa1_IT_ok : itab_sound HASEGS c67aa1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition c67aa1_shape_ (_ : unit) : shape := (SAlt2 (SCase (EVar 7) 63 (SCase (EVar 7) 0 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10]] (SHole 21)) (SCase (EVar 7) 62 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SHole 21)) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SEmitP 2 [] (SHole 21))))) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2] (SEmitP 2 [SPLit [10]] (SHole 21)))) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 111; 110; 102; 105; 103; 95; 108; 101; 110; 32; 111; 118; 101; 114; 114; 117; 110; 115; 32; 105; 110; 112; 117; 116; 10]] (SHole 24))).
Abbreviation c67aa1_shape := (c67aa1_shape_ tt).
Lemma c67aa1_cert :
  CAP.check HASEGS c67aa1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 6 64) 32 (Some (0, 32767)) (Some (-32767, -1)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 6 64) 32 (Some (0, 32767)) (Some (-32767, -1)) None None)) C6A1_HS 0 true false true 400000 3000 None c3a1_hs98 c6_top1 = COk c67aa1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk c67aa1_shape)). Time Qed.
