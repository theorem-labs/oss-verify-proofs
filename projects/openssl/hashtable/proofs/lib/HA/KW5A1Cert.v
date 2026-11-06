(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv KW4A1Lit KW5a KW5A1Inv KW5A1Lit KW5A1Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw5a1_IT : itab := APC.mk_itab_ranges HASEGS kw5a1_ranges.
Lemma kw5a1_IT_ok : itab_sound HASEGS kw5a1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw5a1_shape_ (_ : unit) : shape := (SHole 106).
Abbreviation kw5a1_shape := (kw5a1_shape_ tt).
Lemma kw5a1_cert :
  CAP.check HASEGS kw5a1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 2097152 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 2097152 67108864) 32 None None None None)) KW5A1_HS 0 true false true 400000 3000 None kw4a1_hs105 kw5a1_pl = COk kw5a1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw5a1_shape)). Time Qed.
