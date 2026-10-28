(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW3B0Lit BKW4a BKW4B0Inv BKW4B0Lit BKW4B0Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw4b0_IT : itab := APC.mk_itab_ranges HASEGS kw4b0_ranges.
Lemma kw4b0_IT_ok : itab_sound HASEGS kw4b0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw4b0_shape_ (_ : unit) : shape := (SHole 105).
Abbreviation kw4b0_shape := (kw4b0_shape_ tt).
Lemma kw4b0_cert :
  CAP.check HASEGS kw4b0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 1048576 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 1048576 67108864) 32 None None None None)) KW4B0_HS 0 true false true 400000 3000 None kw3b0_hs104 kw4b0_pl = COk kw4b0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw4b0_shape)). Time Qed.
