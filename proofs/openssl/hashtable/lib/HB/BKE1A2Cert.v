(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKPA2Lit BKE1a BKE1A2Inv BKE1A2Lit BKE1A2Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke1a2_IT : itab := APC.mk_itab_ranges HASEGS ke1a2_ranges.
Lemma ke1a2_IT_ok : itab_sound HASEGS ke1a2_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke1a2_shape_ (_ : unit) : shape := (SHole 201).
Abbreviation ke1a2_shape := (ke1a2_shape_ tt).
Lemma ke1a2_cert :
  CAP.check HASEGS ke1a2_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 65536 131071) 32 (Some (0, 32767)) (Some (0, 131065)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 65536 131071) 32 (Some (0, 32767)) (Some (0, 131065)) None None)) KE1A2_HS 0 true false true 400000 3000 None kpa2_hs101 ke1a2_pl = COk ke1a2_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke1a2_shape)). Time Qed.
