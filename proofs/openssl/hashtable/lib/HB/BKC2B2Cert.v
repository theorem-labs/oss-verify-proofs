(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKE2B2Lit BKC2B2Inv BKC2B2Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc2b2_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc2b2_IT_ok : itab_sound HASEGS kc2b2_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc2b2_shape_ (_ : unit) : shape := (SHole 302).
Abbreviation kc2b2_shape := (kc2b2_shape_ tt).
Lemma kc2b2_cert :
  CAP.check HASEGS kc2b2_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 131072 262143) 32 (Some (0, 32767)) (Some (0, 262137)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 131072 262143) 32 (Some (0, 32767)) (Some (0, 262137)) None None)) KC2B2_HS 0 true false true 400000 3000 None ke2b2_hs202 kc2b2_pl = COk kc2b2_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc2b2_shape)). Time Qed.
