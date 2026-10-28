(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW5A2Lit BKW6a BKW6A2Inv BKW6A2Lit BKW6A2Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw6a2_IT : itab := APC.mk_itab_ranges HASEGS kw6a2_ranges.
Lemma kw6a2_IT_ok : itab_sound HASEGS kw6a2_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw6a2_shape_ (_ : unit) : shape := (SHole 107).
Abbreviation kw6a2_shape := (kw6a2_shape_ tt).
Lemma kw6a2_cert :
  CAP.check HASEGS kw6a2_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 4194304 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 4194304 67108864) 32 None None None None)) KW6A2_HS 0 true false true 400000 3000 None kw5a2_hs106 kw6a2_pl = COk kw6a2_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw6a2_shape)). Time Qed.
