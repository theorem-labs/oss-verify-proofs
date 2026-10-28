(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW5B3Lit BKE6b BKE6B3Inv BKE6B3Lit BKE6B3Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke6b3_IT : itab := APC.mk_itab_ranges HASEGS ke6b3_ranges.
Lemma ke6b3_IT_ok : itab_sound HASEGS ke6b3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke6b3_shape_ (_ : unit) : shape := (SHole 206).
Abbreviation ke6b3_shape := (ke6b3_shape_ tt).
Lemma ke6b3_cert :
  CAP.check HASEGS ke6b3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 2097152 4194303) 32 (Some (0, 32767)) (Some (0, 4194297)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 2097152 4194303) 32 (Some (0, 32767)) (Some (0, 4194297)) None None)) KE6B3_HS 0 true false true 400000 3000 None kw5b3_hs106 ke6b3_pl = COk ke6b3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke6b3_shape)). Time Qed.
