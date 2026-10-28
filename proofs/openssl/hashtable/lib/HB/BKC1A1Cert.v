(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKE1A1Lit BKC1A1Inv BKC1A1Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc1a1_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc1a1_IT_ok : itab_sound HASEGS kc1a1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc1a1_shape_ (_ : unit) : shape := (SHole 301).
Abbreviation kc1a1_shape := (kc1a1_shape_ tt).
Lemma kc1a1_cert :
  CAP.check HASEGS kc1a1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 65536 131071) 32 (Some (0, 32767)) (Some (0, 131065)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 65536 131071) 32 (Some (0, 32767)) (Some (0, 131065)) None None)) KC1A1_HS 0 true false true 400000 3000 None ke1a1_hs201 kc1a1_pl = COk kc1a1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc1a1_shape)). Time Qed.
