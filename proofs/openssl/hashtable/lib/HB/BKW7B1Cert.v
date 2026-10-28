(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW6B1Lit BKW7a BKW7B1Inv BKW7B1Lit BKW7B1Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw7b1_IT : itab := APC.mk_itab_ranges HASEGS kw7b1_ranges.
Lemma kw7b1_IT_ok : itab_sound HASEGS kw7b1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw7b1_shape_ (_ : unit) : shape := (SHole 108).
Abbreviation kw7b1_shape := (kw7b1_shape_ tt).
Lemma kw7b1_cert :
  CAP.check HASEGS kw7b1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 8388608 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 8388608 67108864) 32 None None None None)) KW7B1_HS 0 true false true 400000 3000 None kw6b1_hs107 kw7b1_pl = COk kw7b1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw7b1_shape)). Time Qed.
