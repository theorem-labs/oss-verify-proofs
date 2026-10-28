(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBCheck0 HBCheck1 AsanNodesIO HBCheck3 CxfL9 CxfFast BKInv BKE1B3Lit BKC1B3Inv BKC1B3Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc1b3_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc1b3_IT_ok : itab_sound HASEGS kc1b3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc1b3_shape_ (_ : unit) : shape := (SHole 301).
Abbreviation kc1b3_shape := (kc1b3_shape_ tt).
Lemma kc1b3_cert :
  CAP.check HASEGS kc1b3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 65536 131071) 32 (Some (0, 32767)) (Some (0, 131065)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 65536 131071) 32 (Some (0, 32767)) (Some (0, 131065)) None None)) KC1B3_HS 0 true false true 400000 3000 None ke1b3_hs201 kc1b3_pl = COk kc1b3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc1b3_shape)). Time Qed.
