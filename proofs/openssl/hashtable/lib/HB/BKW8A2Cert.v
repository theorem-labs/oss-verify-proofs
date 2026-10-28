(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW7A2Lit BKW8a BKW8A2Inv BKW8A2Lit BKW8A2Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw8a2_IT : itab := APC.mk_itab_ranges HASEGS kw8a2_ranges.
Lemma kw8a2_IT_ok : itab_sound HASEGS kw8a2_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw8a2_shape_ (_ : unit) : shape := (SHole 109).
Abbreviation kw8a2_shape := (kw8a2_shape_ tt).
Lemma kw8a2_cert :
  CAP.check HASEGS kw8a2_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 16777216 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 16777216 67108864) 32 None None None None)) KW8A2_HS 0 true false true 400000 3000 None kw7a2_hs108 kw8a2_pl = COk kw8a2_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw8a2_shape)). Time Qed.
