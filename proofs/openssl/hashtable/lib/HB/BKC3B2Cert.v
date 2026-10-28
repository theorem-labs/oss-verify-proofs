(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKE3B2Lit BKC3B2Inv BKC3B2Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc3b2_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc3b2_IT_ok : itab_sound HASEGS kc3b2_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc3b2_shape_ (_ : unit) : shape := (SHole 303).
Abbreviation kc3b2_shape := (kc3b2_shape_ tt).
Lemma kc3b2_cert :
  CAP.check HASEGS kc3b2_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 262144 524287) 32 (Some (0, 32767)) (Some (0, 524281)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 262144 524287) 32 (Some (0, 32767)) (Some (0, 524281)) None None)) KC3B2_HS 0 true false true 400000 3000 None ke3b2_hs203 kc3b2_pl = COk kc3b2_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc3b2_shape)). Time Qed.
