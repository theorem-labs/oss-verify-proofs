(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv KE7B2Lit KC7B2Inv KC7B2Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc7b2_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc7b2_IT_ok : itab_sound HASEGS kc7b2_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc7b2_shape_ (_ : unit) : shape := (SHole 307).
Abbreviation kc7b2_shape := (kc7b2_shape_ tt).
Lemma kc7b2_cert :
  CAP.check HASEGS kc7b2_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 4194304 8388607) 32 (Some (0, 32767)) (Some (0, 8388601)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 4194304 8388607) 32 (Some (0, 32767)) (Some (0, 8388601)) None None)) KC7B2_HS 0 true false true 400000 3000 None ke7b2_hs207 kc7b2_pl = COk kc7b2_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc7b2_shape)). Time Qed.
