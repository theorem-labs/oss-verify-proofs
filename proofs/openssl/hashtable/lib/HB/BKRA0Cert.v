(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW9A0Lit BKRa BKRA0Inv BKRA0Lit BKRA0Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kra0_IT : itab := APC.mk_itab_ranges HASEGS kra0_ranges.
Lemma kra0_IT_ok : itab_sound HASEGS kra0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kra0_shape_ (_ : unit) : shape := (SEmitP 2 [SPLit [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10]] (SHole 230)).
Abbreviation kra0_shape := (kra0_shape_ tt).
Lemma kra0_cert :
  CAP.check HASEGS kra0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 67108864 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 67108864 67108864) 32 None None None None)) KRA0_HS 0 true false true 400000 3000 None kw9a0_hs110 kra0_pl = COk kra0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kra0_shape)). Time Qed.
