(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKW6B1Lit BKE7a BKE7B1Inv BKE7B1Lit BKE7B1Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke7b1_IT : itab := APC.mk_itab_ranges HASEGS ke7b1_ranges.
Lemma ke7b1_IT_ok : itab_sound HASEGS ke7b1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke7b1_shape_ (_ : unit) : shape := (SHole 207).
Abbreviation ke7b1_shape := (ke7b1_shape_ tt).
Lemma ke7b1_cert :
  CAP.check HASEGS ke7b1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 4194304 8388607) 32 (Some (0, 32767)) (Some (0, 8388601)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 4194304 8388607) 32 (Some (0, 32767)) (Some (0, 8388601)) None None)) KE7B1_HS 0 true false true 400000 3000 None kw6b1_hs107 ke7b1_pl = COk ke7b1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke7b1_shape)). Time Qed.
