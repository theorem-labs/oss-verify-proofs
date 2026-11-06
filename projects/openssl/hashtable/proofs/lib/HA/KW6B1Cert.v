(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv KW5B1Lit KW6a KW6B1Inv KW6B1Lit KW6B1Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw6b1_IT : itab := APC.mk_itab_ranges HASEGS kw6b1_ranges.
Lemma kw6b1_IT_ok : itab_sound HASEGS kw6b1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw6b1_shape_ (_ : unit) : shape := (SHole 107).
Abbreviation kw6b1_shape := (kw6b1_shape_ tt).
Lemma kw6b1_cert :
  CAP.check HASEGS kw6b1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 4194304 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 4194304 67108864) 32 None None None None)) KW6B1_HS 0 true false true 400000 3000 None kw5b1_hs106 kw6b1_pl = COk kw6b1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw6b1_shape)). Time Qed.
