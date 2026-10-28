(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKPB3Lit BKW1b BKW1B3Inv BKW1B3Lit BKW1B3Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw1b3_IT : itab := APC.mk_itab_ranges HASEGS kw1b3_ranges.
Lemma kw1b3_IT_ok : itab_sound HASEGS kw1b3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw1b3_shape_ (_ : unit) : shape := (SHole 102).
Abbreviation kw1b3_shape := (kw1b3_shape_ tt).
Lemma kw1b3_cert :
  CAP.check HASEGS kw1b3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 131072 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 131072 67108864) 32 None None None None)) KW1B3_HS 0 true false true 400000 3000 None kpb3_hs101 kw1b3_pl = COk kw1b3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw1b3_shape)). Time Qed.
