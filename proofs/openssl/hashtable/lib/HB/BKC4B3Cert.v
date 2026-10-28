(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKE4B3Lit BKC4B3Inv BKC4B3Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc4b3_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc4b3_IT_ok : itab_sound HASEGS kc4b3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc4b3_shape_ (_ : unit) : shape := (SHole 304).
Abbreviation kc4b3_shape := (kc4b3_shape_ tt).
Lemma kc4b3_cert :
  CAP.check HASEGS kc4b3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 524288 1048575) 32 (Some (0, 32767)) (Some (0, 1048569)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 524288 1048575) 32 (Some (0, 32767)) (Some (0, 1048569)) None None)) KC4B3_HS 0 true false true 400000 3000 None ke4b3_hs204 kc4b3_pl = COk kc4b3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc4b3_shape)). Time Qed.
