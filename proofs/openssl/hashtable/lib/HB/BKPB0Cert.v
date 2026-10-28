(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BC3B0Lit BC3B0LitK BC4B0Lit BC4e BKPa BKPB0Inv BKPB0Lit BKPB0Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kpb0_IT : itab := APC.mk_itab_ranges HASEGS kpb0_ranges.
Lemma kpb0_IT_ok : itab_sound HASEGS kpb0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kpb0_shape_ (_ : unit) : shape := (SAlt2 (SCase (EVar 7) 63 (SCase (EVar 7) 0 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10]] (SHole 21)) (SCase (EVar 7) 62 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SHole 21)) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SEmitP 2 [] (SHole 21))))) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2] (SEmitP 2 [SPLit [10]] (SHole 21)))) (SHole 101)).
Abbreviation kpb0_shape := (kpb0_shape_ tt).
Lemma kpb0_cert :
  CAP.check HASEGS kpb0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 65536 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 65536 67108864) 32 None None None None)) KPB0_HS 0 true false true 400000 3000 None c3b0_hs98k kpb0_pl = COk kpb0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kpb0_shape)). Time Qed.
