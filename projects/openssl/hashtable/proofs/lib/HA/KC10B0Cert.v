(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv KE10B0Lit KC10B0Inv KC10B0Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc10b0_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc10b0_IT_ok : itab_sound HASEGS kc10b0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc10b0_shape_ (_ : unit) : shape := (SHole 310).
Abbreviation kc10b0_shape := (kc10b0_shape_ tt).
Lemma kc10b0_cert :
  CAP.check HASEGS kc10b0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 33554432 67108863) 32 (Some (0, 32767)) (Some (0, 67108857)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 33554432 67108863) 32 (Some (0, 32767)) (Some (0, 67108857)) None None)) KC10B0_HS 0 true false true 400000 3000 None ke10b0_hs210 kc10b0_pl = COk kc10b0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc10b0_shape)). Time Qed.
