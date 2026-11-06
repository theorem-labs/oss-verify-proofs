(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv KE5A3Lit KC5A3Inv KC5A3Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kc5a3_IT : itab := APC.mk_itab_ranges HASEGS [].
Lemma kc5a3_IT_ok : itab_sound HASEGS kc5a3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kc5a3_shape_ (_ : unit) : shape := (SHole 305).
Abbreviation kc5a3_shape := (kc5a3_shape_ tt).
Lemma kc5a3_cert :
  CAP.check HASEGS kc5a3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 1048576 2097151) 32 (Some (0, 32767)) (Some (0, 2097145)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 1048576 2097151) 32 (Some (0, 32767)) (Some (0, 2097145)) None None)) KC5A3_HS 0 true false true 400000 3000 None ke5a3_hs205 kc5a3_pl = COk kc5a3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kc5a3_shape)). Time Qed.
