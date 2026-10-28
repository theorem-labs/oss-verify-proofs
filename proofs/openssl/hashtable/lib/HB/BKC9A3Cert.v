(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKE9A3Lit BKC9A3Inv BKC9A3Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc9a3_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc9a3_IT_ok : itab_sound HASEGS kc9a3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc9a3_shape_ (_ : unit) : shape := (SHole 309).
Abbreviation kc9a3_shape := (kc9a3_shape_ tt).
Lemma kc9a3_cert :
  CAP.check HASEGS kc9a3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 16777216 33554431) 32 (Some (0, 32767)) (Some (0, 33554425)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 16777216 33554431) 32 (Some (0, 32767)) (Some (0, 33554425)) None None)) KC9A3_HS 0 true false true 400000 3000 None ke9a3_hs209 kc9a3_pl = COk kc9a3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc9a3_shape)). Time Qed.
