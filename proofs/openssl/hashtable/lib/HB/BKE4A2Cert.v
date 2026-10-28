(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW3A2Lit BKE4a BKE4A2Inv BKE4A2Lit BKE4A2Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke4a2_IT : itab := APC.mk_itab_ranges HASEGS ke4a2_ranges.
Lemma ke4a2_IT_ok : itab_sound HASEGS ke4a2_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke4a2_shape_ (_ : unit) : shape := (SHole 204).
Abbreviation ke4a2_shape := (ke4a2_shape_ tt).
Lemma ke4a2_cert :
  CAP.check HASEGS ke4a2_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 524288 1048575) 32 (Some (0, 32767)) (Some (0, 1048569)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 524288 1048575) 32 (Some (0, 32767)) (Some (0, 1048569)) None None)) KE4A2_HS 0 true false true 400000 3000 None kw3a2_hs104 ke4a2_pl = COk ke4a2_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke4a2_shape)). Time Qed.
