(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW2A2Lit BKE3a BKE3A2Inv BKE3A2Lit BKE3A2Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke3a2_IT : itab := APC.mk_itab_ranges HASEGS ke3a2_ranges.
Lemma ke3a2_IT_ok : itab_sound HASEGS ke3a2_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke3a2_shape_ (_ : unit) : shape := (SHole 203).
Abbreviation ke3a2_shape := (ke3a2_shape_ tt).
Lemma ke3a2_cert :
  CAP.check HASEGS ke3a2_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 262144 524287) 32 (Some (0, 32767)) (Some (0, 524281)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 262144 524287) 32 (Some (0, 32767)) (Some (0, 524281)) None None)) KE3A2_HS 0 true false true 400000 3000 None kw2a2_hs103 ke3a2_pl = COk ke3a2_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke3a2_shape)). Time Qed.
