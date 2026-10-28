(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW7A1Lit BKW8a BKW8A1Inv BKW8A1Lit BKW8A1Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw8a1_IT : itab := APC.mk_itab_ranges HASEGS kw8a1_ranges.
Lemma kw8a1_IT_ok : itab_sound HASEGS kw8a1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw8a1_shape_ (_ : unit) : shape := (SHole 109).
Abbreviation kw8a1_shape := (kw8a1_shape_ tt).
Lemma kw8a1_cert :
  CAP.check HASEGS kw8a1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 16777216 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 16777216 67108864) 32 None None None None)) KW8A1_HS 0 true false true 400000 3000 None kw7a1_hs108 kw8a1_pl = COk kw8a1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw8a1_shape)). Time Qed.
