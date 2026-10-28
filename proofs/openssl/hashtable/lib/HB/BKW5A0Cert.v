(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW4A0Lit BKW5a BKW5A0Inv BKW5A0Lit BKW5A0Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw5a0_IT : itab := APC.mk_itab_ranges HASEGS kw5a0_ranges.
Lemma kw5a0_IT_ok : itab_sound HASEGS kw5a0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw5a0_shape_ (_ : unit) : shape := (SHole 106).
Abbreviation kw5a0_shape := (kw5a0_shape_ tt).
Lemma kw5a0_cert :
  CAP.check HASEGS kw5a0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 2097152 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 2097152 67108864) 32 None None None None)) KW5A0_HS 0 true false true 400000 3000 None kw4a0_hs105 kw5a0_pl = COk kw5a0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw5a0_shape)). Time Qed.
