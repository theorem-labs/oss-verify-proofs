(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv C3A2Lit C3A2LitK C4A2Lit C4e KPa KPA2Inv KPA2Lit KPA2Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kpa2_IT : itab := APC.mk_itab_ranges HASEGS kpa2_ranges.
Lemma kpa2_IT_ok : itab_sound HASEGS kpa2_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kpa2_shape_ (_ : unit) : shape := (SAlt2 (SCase (EVar 7) 63 (SCase (EVar 7) 0 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10]] (SHole 21)) (SCase (EVar 7) 62 (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SHole 21)) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2; SPLit [10]] (SEmitP 2 [] (SHole 21))))) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2] (SEmitP 2 [SPLit [10]] (SHole 21)))) (SHole 101)).
Abbreviation kpa2_shape := (kpa2_shape_ tt).
Lemma kpa2_cert :
  CAP.check HASEGS kpa2_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 65536 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 65536 67108864) 32 None None None None)) KPA2_HS 0 true false true 400000 3000 None c3a2_hs98k kpa2_pl = COk kpa2_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kpa2_shape)). Time Qed.
