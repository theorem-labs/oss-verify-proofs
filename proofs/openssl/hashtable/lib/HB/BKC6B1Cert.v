(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKE6B1Lit BKC6B1Inv BKC6B1Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc6b1_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc6b1_IT_ok : itab_sound HASEGS kc6b1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc6b1_shape_ (_ : unit) : shape := (SHole 306).
Abbreviation kc6b1_shape := (kc6b1_shape_ tt).
Lemma kc6b1_cert :
  CAP.check HASEGS kc6b1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 2097152 4194303) 32 (Some (0, 32767)) (Some (0, 4194297)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 2097152 4194303) 32 (Some (0, 32767)) (Some (0, 4194297)) None None)) KC6B1_HS 0 true false true 400000 3000 None ke6b1_hs206 kc6b1_pl = COk kc6b1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc6b1_shape)). Time Qed.
