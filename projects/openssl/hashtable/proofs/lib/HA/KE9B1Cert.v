(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv KW8B1Lit KE9a KE9B1Inv KE9B1Lit KE9B1Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke9b1_IT : itab := APC.mk_itab_ranges HASEGS ke9b1_ranges.
Lemma ke9b1_IT_ok : itab_sound HASEGS ke9b1_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke9b1_shape_ (_ : unit) : shape := (SHole 209).
Abbreviation ke9b1_shape := (ke9b1_shape_ tt).
Lemma ke9b1_cert :
  CAP.check HASEGS ke9b1_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 16777216 33554431) 32 (Some (0, 32767)) (Some (0, 33554425)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 16777216 33554431) 32 (Some (0, 32767)) (Some (0, 33554425)) None None)) KE9B1_HS 0 true false true 400000 3000 None kw8b1_hs109 ke9b1_pl = COk ke9b1_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke9b1_shape)). Time Qed.
