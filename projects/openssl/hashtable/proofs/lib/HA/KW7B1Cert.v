(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv KW6B1Lit KW7a KW7B1Inv KW7B1Lit KW7B1Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw7b1_IT : itab := APC.mk_itab_ranges HASEGS kw7b1_ranges.
Lemma kw7b1_IT_ok : itab_sound HASEGS kw7b1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw7b1_shape_ (_ : unit) : shape := (SHole 108).
Abbreviation kw7b1_shape := (kw7b1_shape_ tt).
Lemma kw7b1_cert :
  CAP.check HASEGS kw7b1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 8388608 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 8388608 67108864) 32 None None None None)) KW7B1_HS 0 true false true 400000 3000 None kw6b1_hs107 kw7b1_pl = COk kw7b1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw7b1_shape)). Time Qed.
