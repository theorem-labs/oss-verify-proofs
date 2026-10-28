(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKE7B0Lit BKC7B0Inv BKC7B0Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc7b0_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc7b0_IT_ok : itab_sound HASEGS kc7b0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc7b0_shape_ (_ : unit) : shape := (SHole 307).
Abbreviation kc7b0_shape := (kc7b0_shape_ tt).
Lemma kc7b0_cert :
  CAP.check HASEGS kc7b0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 4194304 8388607) 32 (Some (0, 32767)) (Some (0, 8388601)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 4194304 8388607) 32 (Some (0, 32767)) (Some (0, 8388601)) None None)) KC7B0_HS 0 true false true 400000 3000 None ke7b0_hs207 kc7b0_pl = COk kc7b0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc7b0_shape)). Time Qed.
