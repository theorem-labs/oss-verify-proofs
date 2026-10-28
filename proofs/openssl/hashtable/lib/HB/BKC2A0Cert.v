(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKE2A0Lit BKC2A0Inv BKC2A0Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc2a0_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc2a0_IT_ok : itab_sound HASEGS kc2a0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc2a0_shape_ (_ : unit) : shape := (SHole 302).
Abbreviation kc2a0_shape := (kc2a0_shape_ tt).
Lemma kc2a0_cert :
  CAP.check HASEGS kc2a0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 131072 262143) 32 (Some (0, 32767)) (Some (0, 262137)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 131072 262143) 32 (Some (0, 32767)) (Some (0, 262137)) None None)) KC2A0_HS 0 true false true 400000 3000 None ke2a0_hs202 kc2a0_pl = COk kc2a0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc2a0_shape)). Time Qed.
