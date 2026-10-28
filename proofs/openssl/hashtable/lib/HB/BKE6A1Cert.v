(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW5A1Lit BKE6a BKE6A1Inv BKE6A1Lit BKE6A1Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke6a1_IT : itab := APC.mk_itab_ranges HASEGS ke6a1_ranges.
Lemma ke6a1_IT_ok : itab_sound HASEGS ke6a1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke6a1_shape_ (_ : unit) : shape := (SHole 206).
Abbreviation ke6a1_shape := (ke6a1_shape_ tt).
Lemma ke6a1_cert :
  CAP.check HASEGS ke6a1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 2097152 4194303) 32 (Some (0, 32767)) (Some (0, 4194297)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 2097152 4194303) 32 (Some (0, 32767)) (Some (0, 4194297)) None None)) KE6A1_HS 0 true false true 400000 3000 None kw5a1_hs106 ke6a1_pl = COk ke6a1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke6a1_shape)). Time Qed.
