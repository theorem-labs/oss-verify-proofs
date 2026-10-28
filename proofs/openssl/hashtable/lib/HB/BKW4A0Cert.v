(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW3A0Lit BKW4a BKW4A0Inv BKW4A0Lit BKW4A0Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw4a0_IT : itab := APC.mk_itab_ranges HASEGS kw4a0_ranges.
Lemma kw4a0_IT_ok : itab_sound HASEGS kw4a0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw4a0_shape_ (_ : unit) : shape := (SHole 105).
Abbreviation kw4a0_shape := (kw4a0_shape_ tt).
Lemma kw4a0_cert :
  CAP.check HASEGS kw4a0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 1048576 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 1048576 67108864) 32 None None None None)) KW4A0_HS 0 true false true 400000 3000 None kw3a0_hs104 kw4a0_pl = COk kw4a0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw4a0_shape)). Time Qed.
