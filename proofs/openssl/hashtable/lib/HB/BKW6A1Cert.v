(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW5A1Lit BKW6a BKW6A1Inv BKW6A1Lit BKW6A1Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw6a1_IT : itab := APC.mk_itab_ranges HASEGS kw6a1_ranges.
Lemma kw6a1_IT_ok : itab_sound HASEGS kw6a1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw6a1_shape_ (_ : unit) : shape := (SHole 107).
Abbreviation kw6a1_shape := (kw6a1_shape_ tt).
Lemma kw6a1_cert :
  CAP.check HASEGS kw6a1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 4194304 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 4194304 67108864) 32 None None None None)) KW6A1_HS 0 true false true 400000 3000 None kw5a1_hs106 kw6a1_pl = COk kw6a1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw6a1_shape)). Time Qed.
