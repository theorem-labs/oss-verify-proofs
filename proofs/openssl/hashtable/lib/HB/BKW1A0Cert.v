(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKPA0Lit BKW1a BKW1A0Inv BKW1A0Lit BKW1A0Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw1a0_IT : itab := APC.mk_itab_ranges HASEGS kw1a0_ranges.
Lemma kw1a0_IT_ok : itab_sound HASEGS kw1a0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw1a0_shape_ (_ : unit) : shape := (SHole 102).
Abbreviation kw1a0_shape := (kw1a0_shape_ tt).
Lemma kw1a0_cert :
  CAP.check HASEGS kw1a0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 131072 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 131072 67108864) 32 None None None None)) KW1A0_HS 0 true false true 400000 3000 None kpa0_hs101 kw1a0_pl = COk kw1a0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw1a0_shape)). Time Qed.
