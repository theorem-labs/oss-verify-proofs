(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW1B1Lit BKW2a BKW2B1Inv BKW2B1Lit BKW2B1Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw2b1_IT : itab := APC.mk_itab_ranges HASEGS kw2b1_ranges.
Lemma kw2b1_IT_ok : itab_sound HASEGS kw2b1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw2b1_shape_ (_ : unit) : shape := (SHole 103).
Abbreviation kw2b1_shape := (kw2b1_shape_ tt).
Lemma kw2b1_cert :
  CAP.check HASEGS kw2b1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 262144 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 262144 67108864) 32 None None None None)) KW2B1_HS 0 true false true 400000 3000 None kw1b1_hs102 kw2b1_pl = COk kw2b1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw2b1_shape)). Time Qed.
