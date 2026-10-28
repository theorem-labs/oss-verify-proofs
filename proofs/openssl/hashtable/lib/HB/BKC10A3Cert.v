(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKE10A3Lit BKC10A3Inv BKC10A3Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc10a3_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc10a3_IT_ok : itab_sound HASEGS kc10a3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc10a3_shape_ (_ : unit) : shape := (SHole 310).
Abbreviation kc10a3_shape := (kc10a3_shape_ tt).
Lemma kc10a3_cert :
  CAP.check HASEGS kc10a3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 33554432 67108863) 32 (Some (0, 32767)) (Some (0, 67108857)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 33554432 67108863) 32 (Some (0, 32767)) (Some (0, 67108857)) None None)) KC10A3_HS 0 true false true 400000 3000 None ke10a3_hs210 kc10a3_pl = COk kc10a3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc10a3_shape)). Time Qed.
