(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore AsanInit CertRefl CxRel CxPlan CxPlanSound HAPlanImage HAAtable HACheck0 HACheck1 AsanNodesIO HACheck3 CxfL9 CxfFast KInv KW3A0Lit KE4a KE4A0Inv KE4A0Lit KE4A0Rng.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition ke4a0_IT : itab := APC.mk_itab_ranges HASEGS ke4a0_ranges.
Lemma ke4a0_IT_ok : itab_sound HASEGS ke4a0_IT.
Proof. apply CXS.mk_itab_ranges_sound. Qed.
Definition ke4a0_shape_ (_ : unit) : shape := (SHole 204).
Abbreviation ke4a0_shape := (ke4a0_shape_ tt).
Lemma ke4a0_cert :
  CAP.check HASEGS ke4a0_IT HAT NX0 AsanInit.LIMIT (ha3_XN (ION.IOT (ION.OFile 524288 1048575) 32 (Some (0, 32767)) (Some (0, 1048569)) None None)) ha3_XE (ha3_XB (ION.IOT (ION.OFile 524288 1048575) 32 (Some (0, 32767)) (Some (0, 1048569)) None None)) KE4A0_HS 0 true false true 400000 3000 None kw3a0_hs104 ke4a0_pl = COk ke4a0_shape.
Proof. apply CXFF.check_l_intro. ltac2:(cert_refl_vm constr:(COk ke4a0_shape)). Time Qed.
