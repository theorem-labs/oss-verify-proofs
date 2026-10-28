(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW1A3Lit BKE2b BKE2A3Inv BKE2A3Lit BKE2A3Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke2a3_IT : itab := APC.mk_itab_ranges HASEGS ke2a3_ranges.
Lemma ke2a3_IT_ok : itab_sound HASEGS ke2a3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke2a3_shape_ (_ : unit) : shape := (SHole 202).
Abbreviation ke2a3_shape := (ke2a3_shape_ tt).
Lemma ke2a3_cert :
  CAP.check HASEGS ke2a3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 131072 262143) 32 (Some (0, 32767)) (Some (0, 262137)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 131072 262143) 32 (Some (0, 32767)) (Some (0, 262137)) None None)) KE2A3_HS 0 true false true 400000 3000 None kw1a3_hs102 ke2a3_pl = COk ke2a3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke2a3_shape)). Time Qed.
