(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW8B1Lit BKW9a BKW9B1Inv BKW9B1Lit BKW9B1Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw9b1_IT : itab := APC.mk_itab_ranges HASEGS kw9b1_ranges.
Lemma kw9b1_IT_ok : itab_sound HASEGS kw9b1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw9b1_shape_ (_ : unit) : shape := (SHole 110).
Abbreviation kw9b1_shape := (kw9b1_shape_ tt).
Lemma kw9b1_cert :
  CAP.check HASEGS kw9b1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 33554432 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 33554432 67108864) 32 None None None None)) KW9B1_HS 0 true false true 400000 3000 None kw8b1_hs109 kw9b1_pl = COk kw9b1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw9b1_shape)). Time Qed.
