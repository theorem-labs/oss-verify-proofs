(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW1A0Lit BKE2a BKE2A0Inv BKE2A0Lit BKE2A0Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke2a0_IT : itab := APC.mk_itab_ranges HASEGS ke2a0_ranges.
Lemma ke2a0_IT_ok : itab_sound HASEGS ke2a0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke2a0_shape_ (_ : unit) : shape := (SHole 202).
Abbreviation ke2a0_shape := (ke2a0_shape_ tt).
Lemma ke2a0_cert :
  CAP.check HASEGS ke2a0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 131072 262143) 32 (Some (0, 32767)) (Some (0, 262137)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 131072 262143) 32 (Some (0, 32767)) (Some (0, 262137)) None None)) KE2A0_HS 0 true false true 400000 3000 None kw1a0_hs102 ke2a0_pl = COk ke2a0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke2a0_shape)). Time Qed.
