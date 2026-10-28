(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW5B2Lit BKE6a BKE6B2Inv BKE6B2Lit BKE6B2Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke6b2_IT : itab := APC.mk_itab_ranges HASEGS ke6b2_ranges.
Lemma ke6b2_IT_ok : itab_sound HASEGS ke6b2_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke6b2_shape_ (_ : unit) : shape := (SHole 206).
Abbreviation ke6b2_shape := (ke6b2_shape_ tt).
Lemma ke6b2_cert :
  CAP.check HASEGS ke6b2_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 2097152 4194303) 32 (Some (0, 32767)) (Some (0, 4194297)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 2097152 4194303) 32 (Some (0, 32767)) (Some (0, 4194297)) None None)) KE6B2_HS 0 true false true 400000 3000 None kw5b2_hs106 ke6b2_pl = COk ke6b2_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke6b2_shape)). Time Qed.
