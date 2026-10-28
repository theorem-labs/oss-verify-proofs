(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BC3A3Lit BC3A3LitK BC4A3Lit BC4e BKPb BKPA3Inv BKPA3Lit BKPA3Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kpa3_IT : itab := APC.mk_itab_ranges HASEGS kpa3_ranges.
Lemma kpa3_IT_ok : itab_sound HASEGS kpa3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kpa3_shape_ (_ : unit) : shape := (SAlt2 (SCase (EVar 7) 63 (SCase (EVar 7) 0 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10]] (SHole 21)) (SCase (EVar 7) 62 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SHole 21)) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SEmitP 2 [] (SHole 21))))) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2] (SEmitP 2 [SPLit [10]] (SHole 21)))) (SHole 101)).
Abbreviation kpa3_shape := (kpa3_shape_ tt).
Lemma kpa3_cert :
  CAP.check HASEGS kpa3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 65536 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 65536 67108864) 32 None None None None)) KPA3_HS 0 true false true 400000 3000 None c3a3_hs98k kpa3_pl = COk kpa3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kpa3_shape)). Time Qed.
