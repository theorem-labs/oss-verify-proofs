(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv KPB0Lit KW1a KW1B0Inv KW1B0Lit KW1B0Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition kw1b0_IT : itab := APC.mk_itab_ranges HASEGS kw1b0_ranges.
Lemma kw1b0_IT_ok : itab_sound HASEGS kw1b0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition kw1b0_shape_ (_ : unit) : shape := (SHole 102).
Abbreviation kw1b0_shape := (kw1b0_shape_ tt).
Lemma kw1b0_cert :
  CAP.check HASEGS kw1b0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 131072 67108864) 32 None None None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 131072 67108864) 32 None None None None)) KW1B0_HS 0 true false true 400000 3000 None kpb0_hs101 kw1b0_pl = COk kw1b0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk kw1b0_shape)). Time Qed.
