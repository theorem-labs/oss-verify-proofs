(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv KW2B0Lit KE3a KE3B0Inv KE3B0Lit KE3B0Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke3b0_IT : itab := APC.mk_itab_ranges HASEGS ke3b0_ranges.
Lemma ke3b0_IT_ok : itab_sound HASEGS ke3b0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke3b0_shape_ (_ : unit) : shape := (SHole 203).
Abbreviation ke3b0_shape := (ke3b0_shape_ tt).
Lemma ke3b0_cert :
  CAP.check HASEGS ke3b0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 262144 524287) 32 (Some (0, 32767)) (Some (0, 524281)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 262144 524287) 32 (Some (0, 32767)) (Some (0, 524281)) None None)) KE3B0_HS 0 true false true 400000 3000 None kw2b0_hs103 ke3b0_pl = COk ke3b0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke3b0_shape)). Time Qed.
