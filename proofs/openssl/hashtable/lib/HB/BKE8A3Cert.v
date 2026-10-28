(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW7A3Lit BKE8b BKE8A3Inv BKE8A3Lit BKE8A3Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke8a3_IT : itab := APC.mk_itab_ranges HASEGS ke8a3_ranges.
Lemma ke8a3_IT_ok : itab_sound HASEGS ke8a3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke8a3_shape_ (_ : unit) : shape := (SHole 208).
Abbreviation ke8a3_shape := (ke8a3_shape_ tt).
Lemma ke8a3_cert :
  CAP.check HASEGS ke8a3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 8388608 16777215) 32 (Some (0, 32767)) (Some (0, 16777209)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 8388608 16777215) 32 (Some (0, 32767)) (Some (0, 16777209)) None None)) KE8A3_HS 0 true false true 400000 3000 None kw7a3_hs108 ke8a3_pl = COk ke8a3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke8a3_shape)). Time Qed.
