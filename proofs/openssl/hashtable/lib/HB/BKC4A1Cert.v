(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKE4A1Lit BKC4A1Inv BKC4A1Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc4a1_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc4a1_IT_ok : itab_sound HASEGS kc4a1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc4a1_shape_ (_ : unit) : shape := (SHole 304).
Abbreviation kc4a1_shape := (kc4a1_shape_ tt).
Lemma kc4a1_cert :
  CAP.check HASEGS kc4a1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 524288 1048575) 32 (Some (0, 32767)) (Some (0, 1048569)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 524288 1048575) 32 (Some (0, 32767)) (Some (0, 1048569)) None None)) KC4A1_HS 0 true false true 400000 3000 None ke4a1_hs204 kc4a1_pl = COk kc4a1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc4a1_shape)). Time Qed.
