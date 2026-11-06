(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv KW8B3Lit KW9b KW9B3Inv KW9B3Lit KW9B3Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw9b3_IT : itab := APC.mk_itab_ranges HASEGS kw9b3_ranges.
Lemma kw9b3_IT_ok : itab_sound HASEGS kw9b3_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw9b3_shape_ (_ : unit) : shape := (SHole 110).
Abbreviation kw9b3_shape := (kw9b3_shape_ tt).
Lemma kw9b3_cert :
  CAP.check HASEGS kw9b3_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 33554432 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 33554432 67108864) 32 None None None None)) KW9B3_HS 0 true false true 400000 3000 None kw8b3_hs109 kw9b3_pl = COk kw9b3_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw9b3_shape)). Time Qed.
