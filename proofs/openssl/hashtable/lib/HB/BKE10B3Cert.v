(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW9B3Lit BKE10b BKE10B3Inv BKE10B3Lit BKE10B3Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke10b3_IT : itab := APC.mk_itab_ranges HASEGS ke10b3_ranges.
Lemma ke10b3_IT_ok : itab_sound HASEGS ke10b3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke10b3_shape_ (_ : unit) : shape := (SHole 210).
Abbreviation ke10b3_shape := (ke10b3_shape_ tt).
Lemma ke10b3_cert :
  CAP.check HASEGS ke10b3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 33554432 67108863) 32 (Some (0, 32767)) (Some (0, 67108857)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 33554432 67108863) 32 (Some (0, 32767)) (Some (0, 67108857)) None None)) KE10B3_HS 0 true false true 400000 3000 None kw9b3_hs110 ke10b3_pl = COk ke10b3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke10b3_shape)). Time Qed.
