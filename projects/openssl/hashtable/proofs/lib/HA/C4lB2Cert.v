(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck2 C3B2Lit C4l C4B2Lit CxfL9 CxfFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition c4lb2_IT : itab := APC.mk_itab_ranges HASEGS c4l_ranges.
Lemma c4lb2_IT_ok : itab_sound HASEGS c4lb2_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition c4lb2_shape_ (_ : unit) : shape := (SCase (EVar 7) 4095 (SHole 96) (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]; SPBlob 2] (SEmitP 2 [SPLit [10]] (SHole 21)))).
Abbreviation c4lb2_shape := (c4lb2_shape_ tt).
Lemma c4lb2_cert :
  CAP.check HASEGS c4lb2_IT HAT NX0 AsanInit.LIMIT (ha2_XN (ION.iot_simple ION.OTooLong 32)) ha2_XE (ha2_XB (ION.iot_simple ION.OTooLong 32)) C4B2_HS 0 true false true 400000 3000 None c3b2_hs98 c4l_top = COk c4lb2_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk c4lb2_shape)). Time Qed.
