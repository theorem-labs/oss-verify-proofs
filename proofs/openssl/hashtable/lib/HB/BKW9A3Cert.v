(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW8A3Lit BKW9b BKW9A3Inv BKW9A3Lit BKW9A3Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw9a3_IT : itab := APC.mk_itab_ranges HASEGS kw9a3_ranges.
Lemma kw9a3_IT_ok : itab_sound HASEGS kw9a3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw9a3_shape_ (_ : unit) : shape := (SHole 110).
Abbreviation kw9a3_shape := (kw9a3_shape_ tt).
Lemma kw9a3_cert :
  CAP.check HASEGS kw9a3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 33554432 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 33554432 67108864) 32 None None None None)) KW9A3_HS 0 true false true 400000 3000 None kw8a3_hs109 kw9a3_pl = COk kw9a3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw9a3_shape)). Time Qed.
