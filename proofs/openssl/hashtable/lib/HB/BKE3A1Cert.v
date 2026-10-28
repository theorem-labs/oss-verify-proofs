(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW2A1Lit BKE3a BKE3A1Inv BKE3A1Lit BKE3A1Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke3a1_IT : itab := APC.mk_itab_ranges HASEGS ke3a1_ranges.
Lemma ke3a1_IT_ok : itab_sound HASEGS ke3a1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke3a1_shape_ (_ : unit) : shape := (SHole 203).
Abbreviation ke3a1_shape := (ke3a1_shape_ tt).
Lemma ke3a1_cert :
  CAP.check HASEGS ke3a1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 262144 524287) 32 (Some (0, 32767)) (Some (0, 524281)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 262144 524287) 32 (Some (0, 32767)) (Some (0, 524281)) None None)) KE3A1_HS 0 true false true 400000 3000 None kw2a1_hs103 ke3a1_pl = COk ke3a1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke3a1_shape)). Time Qed.
